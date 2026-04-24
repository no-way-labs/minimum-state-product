#!/usr/bin/env python3
"""Read-2 decomposition discriminator (2026-04-19, session 1 gate).

Per Keston 2026-04-19: before committing session 2 to an aggregate
ansatz, classify records by the decomposition

  E_size ≥ shadow_count + cross_position_count
  T_size ≤ L · Σ(m_p − 1)      (trivial UB)

and check whether

  (1) shadow_count ≥ T_size                         — clean aggregate
  (2) shadow_count < T_size but shadow+trivial_cross ≥ T_size + 1
  (3) shadow + trivial cross < T_size + 1           — cross-position
                                                      is doing all the
                                                      work; research-y

"Shadow" = Case-A same-triple firing edges (q ∉ {p_k−1, p_k, p_k+1}),
with both tail c_k^(q,v) and head c_{k+1}^(q,v) NOT on cycle C.

Also reports empirical cross_position_count = E_size − shadow_count to
calibrate outcome 2's "trivial cross-position floor."
"""

import importlib.util
import json
import os
import sys
import time
from collections import defaultdict
from itertools import product as iproduct

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "r4_scaffold",
    os.path.join(HERE, "probe_sk_closed_form_extraction_2026-04-19.py"),
)
_scaffold = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_scaffold)
enumerate_all_cycles = _scaffold.enumerate_all_cycles
m_n_sharp = _scaffold.m_n_sharp
analyze_k1 = _scaffold.analyze_k1
value_sets = _scaffold.value_sets


def compute_shadow_exact(ms, n, cycle, movers, det):
    """Count Case-A shadow edges: tail c_k^(q,v) → head c_{k+1}^(q,v)
    via same-triple firing at p_k, q ∉ {p_k-1, p_k, p_k+1}, both
    endpoints not on cycle C.
    """
    L = len(movers)
    C = set(cycle)
    V = value_sets(cycle, n)

    shadow = 0
    for k in range(L):
        p = movers[k]
        excluded = {(p - 1) % n, p % n, (p + 1) % n}
        c_k = cycle[k]
        c_kp1 = cycle[(k + 1) % L]
        for q in range(n):
            if q in excluded:
                continue
            for v in V[q]:
                if v == c_k[q]:
                    continue
                tail = list(c_k); tail[q] = v; tail = tuple(tail)
                head = list(c_kp1); head[q] = v; head = tuple(head)
                if tail in C or head in C:
                    continue
                shadow += 1
    return shadow


# Same adversarial + spot-check set as session 1
TARGETS = [
    (7, (2, 2, 2, 2, 2, 2, 3)),
    (7, (2, 2, 2, 2, 2, 3, 3)),
    (7, (2, 2, 2, 3, 2, 2, 3)),
    (7, (2, 2, 2, 2, 3, 3, 3)),
    (7, (2, 3, 2, 3, 2, 3, 2)),
    (8, (2, 2, 2, 2, 2, 2, 2, 3)),
    (8, (2, 2, 2, 2, 2, 2, 3, 3)),
    (8, (2, 2, 2, 3, 2, 2, 2, 3)),
    (8, (2, 2, 2, 2, 3, 3, 3, 3)),
    (8, (2, 2, 2, 3, 3, 3, 3, 3)),
    (8, (2, 2, 2, 2, 3, 3, 3, 4)),
    (8, (2, 2, 3, 2, 2, 3, 2, 4)),
    (5, (2, 2, 3, 3, 3)),
    (5, (2, 3, 3, 3, 3)),
    (6, (2, 2, 2, 3, 3, 3)),
    (6, (2, 2, 3, 3, 3, 3)),
    (6, (2, 3, 3, 3, 3, 3)),
]


def classify(r):
    sh = r['shadow']
    T = r['T_size']
    if sh >= T:
        return 1
    # Outcome 2 uses "trivial cross-position floor" — we don't have a
    # principled closed-form floor yet, so we just check whether the
    # empirical `cross_position_count = E_size − shadow` suffices
    # *with any amount added on top*. Use 1 as the minimal target.
    if sh + r['cross_position'] >= T + 1:
        # Record how big the gap was so session 2 knows what structural
        # claim is needed.
        return 2
    return 3


def main():
    print("=" * 78)
    print("Read-2 decomposition discriminator (2026-04-19)")
    print("=" * 78)

    rows = []
    t_start = time.time()
    for (n, ms) in TARGETS:
        cycles = enumerate_all_cycles(ms, n, L_max=24,
                                      time_budget=60.0, max_cycles=20)
        for cycle, movers, det in cycles:
            L = len(movers)
            if L < 2 * n:
                continue
            r = analyze_k1(ms, n, cycle, movers, det)
            if r is None:
                continue
            shadow = compute_shadow_exact(ms, n, cycle, movers, det)
            r['shadow'] = shadow
            r['cross_position'] = r['E_size'] - shadow
            r['T_UB_trivial'] = L * sum(m - 1 for m in ms)
            r['T_gap'] = r['T_size'] - shadow           # positive = shadow short
            r['outcome'] = classify(r)
            rows.append(r)
    print(f"  Collected {len(rows)} records in {time.time()-t_start:.1f}s\n")

    # Outcome distribution
    by_outcome = defaultdict(list)
    for r in rows:
        by_outcome[r['outcome']].append(r)
    print("  Outcome distribution:")
    for o in sorted(by_outcome):
        label = {1: "(1) shadow ≥ T_size      — clean",
                 2: "(2) shadow+cross ≥ T+1   — cross-position needed",
                 3: "(3) shadow+cross < T+1   — RESEARCH-Y (should be 0)"}[o]
        print(f"    {label}: {len(by_outcome[o])} records")

    # Per-n breakdown
    print("\n  Per-n: shadow vs T_size vs T_UB_trivial vs E_size")
    print("    n | recs | shadow range | T_size range | T_UB_trivial | "
          "E_size range | outcome (1/2/3)")
    by_n = defaultdict(list)
    for r in rows:
        by_n[r['n']].append(r)
    for n, rs in sorted(by_n.items()):
        shs = [r['shadow'] for r in rs]
        Ts = [r['T_size'] for r in rs]
        TUs = [r['T_UB_trivial'] for r in rs]
        Es = [r['E_size'] for r in rs]
        outs = defaultdict(int)
        for r in rs:
            outs[r['outcome']] += 1
        print(f"    {n} | {len(rs):4d} | {min(shs):3d}..{max(shs):4d}    | "
              f"{min(Ts):3d}..{max(Ts):4d}    | {min(TUs):3d}..{max(TUs):4d} | "
              f"{min(Es):3d}..{max(Es):4d}     | "
              f"{outs[1]:3d}/{outs[2]:3d}/{outs[3]:3d}")

    # Cross-position structure — per-record
    print(f"\n  Max T_gap (T_size − shadow) across records: "
          f"{max(r['T_gap'] for r in rows)}")
    print(f"  Max cross_position across records: "
          f"{max(r['cross_position'] for r in rows)}")
    print(f"  Min cross_position across records: "
          f"{min(r['cross_position'] for r in rows)}")
    print(f"  Min (T_gap + 1 − cross_position) across records: "
          f"{min(r['T_gap'] + 1 - r['cross_position'] for r in rows)}")

    # Tripwire: shadow scaling sign in n
    print("\n  Shadow / (L · Σ(m-1)) per n:")
    for n, rs in sorted(by_n.items()):
        ratios = [r['shadow'] / r['T_UB_trivial'] for r in rs
                  if r['T_UB_trivial'] > 0]
        if ratios:
            print(f"    n={n}: mean={sum(ratios)/len(ratios):.3f}, "
                  f"min={min(ratios):.3f}, max={max(ratios):.3f}")

    # Dump
    out_dir = os.path.normpath(
        os.path.join(HERE, '..', 'lean', 'docs', 'sk', 'sk_phase0_out')
    )
    out_path = os.path.join(
        out_dir, 'r4_read2_discriminator_2026-04-19.json'
    )
    with open(out_path, 'w') as f:
        json.dump(rows, f)
    print(f"\n  Wrote {out_path}")

    # Exit code: 1 if any outcome-3 records, else 0
    if by_outcome[3]:
        print(f"\n  FAIL: {len(by_outcome[3])} records in outcome 3. "
              f"Session 2 needs real cross-position coverage claim.")
        sys.exit(1)
    elif by_outcome[2]:
        print(f"\n  YELLOW: {len(by_outcome[2])} records in outcome 2. "
              f"Session 2 must include a cross-position floor claim.")
        sys.exit(0)
    else:
        print(f"\n  GREEN: all records in outcome 1. "
              f"Shadow alone closes aggregate surplus.")
        sys.exit(0)


if __name__ == "__main__":
    main()
