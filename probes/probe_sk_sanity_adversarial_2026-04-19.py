#!/usr/bin/env python3
"""Sanity-check probe for Read 2 N_1-native route (2026-04-19).

Keston gating directive: stage-1/2 stride sampling at n=7 (120 records)
and n=8 (18 records) may have skipped adversarial sub-threshold multisets.
Before writing Case A/Case B ansätze, verify margin doesn't collapse at
unsampled hard cases (binary-dominated extremes, ternary-dense,
quaternary-near-threshold).

Pass: min margin ≥ 3 on every adversarial case → stage-1/2 floor is
not a coverage artifact. Proceed to ansatz work.

Fail: min margin < 3 on any case → Read 2 is in worse shape than
stage-1/2 suggested. Reformulate.

Budget: 60s/ms, 20 cycles/ms. ~10 adversarial multisets ~= ~10 min.
"""

import importlib.util
import json
import os
import sys
import time
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))

# The scaffold file has dashes in its name, so it's not importable as
# a regular module. Load via importlib.
_spec = importlib.util.spec_from_file_location(
    "r4_scaffold",
    os.path.join(HERE, "probe_sk_closed_form_extraction_2026-04-19.py"),
)
_scaffold = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_scaffold)
analyze_k1 = _scaffold.analyze_k1
enumerate_all_cycles = _scaffold.enumerate_all_cycles
m_n_sharp = _scaffold.m_n_sharp


# Adversarial sub-threshold multisets.
# Each entry: (n, ms). All ms must satisfy prod(ms) < M_n^sharp.
# Cover: binary-dominated (>=n-2 binary), ternary-dense (<=2 binary),
# quaternary-bearing, plus non-sorted orderings to surface position
# effects the sorted stride-sampling missed.
ADVERSARIAL = [
    # n=7 (M_7^# = 864)
    (7, (2, 2, 2, 2, 2, 2, 3)),                # 6 binary, 1 ternary  (192)
    (7, (2, 2, 2, 2, 2, 3, 3)),                # 5 binary, 2 ternary adj (288)
    (7, (2, 2, 2, 3, 2, 2, 3)),                # 5 binary, 2 ternary sep (288)
    (7, (2, 2, 2, 2, 3, 3, 3)),                # 4 binary, 3 ternary adj (432)
    (7, (2, 3, 2, 3, 2, 3, 2)),                # interleaved 4-3 (288, same val as adj? 2^4*3^3=432; 4 binary/3 ternary)
    # n=8 (M_8^# = 2592)
    (8, (2, 2, 2, 2, 2, 2, 2, 3)),             # 7 binary (384)
    (8, (2, 2, 2, 2, 2, 2, 3, 3)),             # 6 binary, 2 ternary adj (576)
    (8, (2, 2, 2, 3, 2, 2, 2, 3)),             # 6 binary, 2 ternary opp (576)
    (8, (2, 2, 2, 2, 3, 3, 3, 3)),             # 4 binary, 4 ternary (1296)
    (8, (2, 2, 2, 3, 3, 3, 3, 3)),             # 3 binary, 5 ternary dense (1944)
    (8, (2, 2, 2, 2, 3, 3, 3, 4)),             # 4 binary, 3 ternary, 1 quat (1728)
    (8, (2, 2, 3, 2, 2, 3, 2, 4)),             # same multiset, quat separated (1728)
]


def run_one(n, ms, time_budget=60.0, max_cycles=20, L_max=24):
    assert len(ms) == n
    prod = 1
    for m in ms:
        prod *= m
    Mn = m_n_sharp(n)
    assert prod < Mn, f"ms={ms} prod={prod} not sub-threshold (M_n^#={Mn})"

    t0 = time.time()
    cycles = enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles)
    records = []
    for cycle, movers, det in cycles:
        L = len(movers)
        if L < 2 * n:
            continue
        r = analyze_k1(ms, n, cycle, movers, det)
        if r is not None:
            records.append(r)
    dt = time.time() - t0
    return records, dt


def main():
    print("=" * 72, flush=True)
    print("Sanity-check probe — adversarial sub-threshold (2026-04-19)", flush=True)
    print("=" * 72, flush=True)
    print(f"  {len(ADVERSARIAL)} adversarial cases", flush=True)

    all_records = []
    per_case = []
    t_start = time.time()
    for idx, (n, ms) in enumerate(ADVERSARIAL):
        records, dt = run_one(n, ms)
        if records:
            margins = [r['margin'] for r in records]
            mn, mx = min(margins), max(margins)
            avg = sum(margins) / len(margins)
        else:
            mn = mx = avg = None
        per_case.append({
            'n': n, 'ms': list(ms), 'dt': round(dt, 1),
            'records': len(records),
            'margin_min': mn, 'margin_max': mx,
            'margin_avg': None if avg is None else round(avg, 2),
        })
        status = (
            f"min={mn} max={mx} avg={avg:.2f}"
            if mn is not None else "NO L>=2n cycles found in budget"
        )
        print(
            f"  [{idx+1}/{len(ADVERSARIAL)}]  n={n} ms={list(ms)} "
            f"recs={len(records)} {dt:.0f}s  {status}",
            flush=True,
        )
        all_records.extend(records)

    print(f"\n  Total elapsed: {time.time() - t_start:.0f}s", flush=True)
    print(f"  Total records: {len(all_records)}", flush=True)

    # Coverage report — cases with 0 L>=2n cycles
    empty = [c for c in per_case if c['records'] == 0]
    if empty:
        print(f"\n  {len(empty)} cases returned no L>=2n cycles within budget:")
        for c in empty:
            print(f"    n={c['n']} ms={c['ms']} ({c['dt']:.0f}s)")
        print("  These are not informative — may need longer budget.")

    # Verdict
    tested = [c for c in per_case if c['margin_min'] is not None]
    if not tested:
        print("\n  VERDICT: No informative cases. Probe inconclusive.")
        sys.exit(2)

    global_min = min(c['margin_min'] for c in tested)
    global_min_case = next(
        c for c in tested if c['margin_min'] == global_min
    )

    print("\n" + "=" * 72)
    print(f"  Global min margin across {len(tested)} informative cases: {global_min}")
    print(f"  Worst case: n={global_min_case['n']} ms={global_min_case['ms']} "
          f"(recs={global_min_case['records']})")
    print("=" * 72)

    # Dump
    out_dir = os.path.normpath(
        os.path.join(HERE, '..', 'lean', 'docs', 'sk', 'sk_phase0_out')
    )
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(
        out_dir, 'r4_sanity_adversarial_2026-04-19.json'
    )
    with open(out_path, 'w') as f:
        json.dump({
            'per_case': per_case,
            'records': all_records,
        }, f)
    print(f"\n  Wrote {out_path}", flush=True)

    if global_min < 3:
        print(f"\n  FAIL: margin < 3 on adversarial case. "
              f"Stage-1/2 floor is a coverage artifact.")
        print(f"  Reformulate Read 2 or revisit Case A/B decomposition.")
        sys.exit(1)

    print(f"\n  PASS: margin ≥ 3 on all adversarial cases.")
    print(f"  Stage-1/2 floor is NOT a coverage artifact.")
    print(f"  Proceed to Case A/Case B N_1-native ansatz.")
    sys.exit(0)


if __name__ == "__main__":
    main()
