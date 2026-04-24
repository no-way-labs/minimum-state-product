#!/usr/bin/env python3
"""R4 closed-form extraction probe (2026-04-19).

Extends probe_sk_tube_pigeonhole_2026-04-16 with per-record decomposition
of |E_N1|, |T_N1|, |sinks_N1|, plus firing-position and Hamming-coord
distributions, for tripwire evaluation.

B2' claim (the thing we need analytically uniform):
    |E_N1| − (|T_N1| − |sinks_N1|) ≥ 1
    uniformly in (n, L, C, ms),
where N_1 = N_1(C) ∩ VC-NG.

Stage plan (Keston sign-off 2026-04-19):
    stage1: n=5..7     (~1-2h, validates tripwires)
    stage2: n=8        (~5h, kicked off only after stage1 PASS)
    stage3: n=9 adversarial — {2^3,3^5,4} binary-dominated + ternary-dense

Tripwires (refined by Keston):
  T1 — margin closed form requires cycle-shape data beyond (n, L, ms).
       Diagnostic: at fixed (n, L, ms) do we observe >0 spread in margin?
       If yes, the closed form needs more than (n,L,ms), and it is
       exactly the cycle-shape dependency we were worried about.
  T2 — ms-symmetric-function decomposition fails.
       Diagnostic: at fixed (n, sum(m_i-1)) bucket, do we see big spread
       that is *not* explained by max_consec_bin or bin_count? If yes,
       structure is per-position-specific and not summary-stat-captured.
       Also: min margin at any n ≤ 2.
  T3 — threshold / trend.
       T3a: min margin at any n ≤ 2 (empirical floor collapse).
       T3b: min margin strictly decreasing across n=5..8 (erosion).
  T4 — firing-position concentration.
       T4a: single firing position > 60% of |E_N1| for some record.
       T4b: top-2 firing positions > 90% for some record.

Any tripwire fires → abort; escalate to Keston.
Clean → proceed to Lean Phase A infra for R4.
"""

import json
import math
import os
import sys
import time
from collections import defaultdict
from itertools import product as iproduct


def m_n_sharp(n):
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def enumerate_multisets(n, max_product):
    out = []
    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product:
                out.append(tuple(prefix))
            return
        for m in range(2, max_product + 1):
            new_prod = prod * m
            min_remaining = 2 ** (n - i - 1)
            if new_prod * min_remaining >= max_product:
                break
            prefix.append(m)
            rec(i + 1, prefix, new_prod)
            prefix.pop()
    rec(0, [], 1)
    return out


def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen_cycles = set()
    t0 = time.time()

    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)):
                return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max:
            return
        for p in range(n):
            Lp = config[(p - 1) % n]
            Sp = config[p]
            Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp)
            forced_out = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp:
                    continue
                if forced_out is not None and forced_out != new_val:
                    continue
                new_det = dict(det)
                new_det[km] = new_val
                ok = True
                for i in range(n):
                    if i == p:
                        continue
                    Li = config[(i - 1) % n]
                    Si = config[i]
                    Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si:
                        ok = False
                        break
                    new_det[ki] = Si
                if not ok:
                    continue
                nc = list(config)
                nc[p] = new_val
                nc = tuple(nc)
                if nc != start and nc in set(path):
                    continue
                dfs(start, nc, new_det, path + [nc], movers + [p])

    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            break
        dfs(start, start, {}, [start], [])
    return found


def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n):
            V[i].add(c[i])
    return V


def hamming(a, b, n):
    return sum(1 for i in range(n) if a[i] != b[i])


def ms_flags(ms, n):
    bin_count = sum(1 for m in ms if m == 2)
    max_run = cur = 0
    # cyclic max run of binary positions
    doubled = list(ms) + list(ms)
    for m in doubled:
        if m == 2:
            cur += 1
            max_run = max(max_run, cur)
        else:
            cur = 0
    max_run = min(max_run, n)
    return {
        'bin_count': bin_count,
        'max_consec_bin': max_run,
        'sum_m_minus_1': sum(m - 1 for m in ms),
        'sum_m': sum(ms),
        'prod_m': math.prod(ms),
    }


def analyze_k1(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set

    move_entries = {
        (p, Lv, Sv, Rv): val
        for (p, Lv, Sv, Rv), val in det.items()
        if val != Sv
    }

    # N_1 tube = configs in VC-NG at Hamming distance exactly 1 from cycle
    T = set()
    anchor_coords_map = {}  # c -> set of positions where c differs from some
                            # Hamming-1 cycle config
    for c in VC_NG:
        anchors = set()
        for cc in cycle:
            if hamming(c, cc, n) == 1:
                for q in range(n):
                    if c[q] != cc[q]:
                        anchors.add(q)
                        break
        if anchors:
            T.add(c)
            anchor_coords_map[c] = anchors

    if not T:
        return None

    # Build adj in T + log firing pos and anchor coord per edge
    adj = defaultdict(list)
    edges_by_firing_pos = [0] * n
    edges_by_anchor_pos = [0.0] * n
    for c in T:
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx not in move_entries:
                continue
            v = move_entries[ctx]
            nc = list(c)
            nc[p] = v
            nc = tuple(nc)
            if nc in T:
                adj[c].append(nc)
                edges_by_firing_pos[p] += 1
                anchors = anchor_coords_map[c]
                if anchors:
                    w = 1.0 / len(anchors)
                    for q in anchors:
                        edges_by_anchor_pos[q] += w

    T_size = len(T)
    E_size = sum(len(adj[c]) for c in T)
    sinks = sum(1 for c in T if not adj[c])

    # peel
    cur = set(T)
    while True:
        to_remove = set()
        for c in cur:
            if not any(s in cur for s in adj[c]):
                to_remove.add(c)
        if not to_remove:
            break
        cur -= to_remove
    peel_size = len(cur)

    margin = E_size - (T_size - sinks)

    # firing-pos concentration
    if E_size > 0:
        fp_fracs = sorted(
            (cnt / E_size for cnt in edges_by_firing_pos),
            reverse=True,
        )
        max_fp_frac = fp_fracs[0]
        top2_fp_frac = sum(fp_fracs[:2])
    else:
        max_fp_frac = 0.0
        top2_fp_frac = 0.0

    # anchor-pos concentration (Keston-requested second view)
    total_anchor = sum(edges_by_anchor_pos)
    if total_anchor > 0:
        ap_fracs = sorted(
            (w / total_anchor for w in edges_by_anchor_pos),
            reverse=True,
        )
        max_ap_frac = ap_fracs[0]
        top2_ap_frac = sum(ap_fracs[:2])
    else:
        max_ap_frac = 0.0
        top2_ap_frac = 0.0

    f = ms_flags(ms, n)

    return {
        'n': n,
        'ms': list(ms),
        'L': L,
        'VC_NG_size': len(VC_NG),
        'T_size': T_size,
        'E_size': E_size,
        'sinks': sinks,
        'peel_size': peel_size,
        'margin': margin,
        'edges_by_firing_pos': edges_by_firing_pos,
        'edges_by_anchor_pos': [round(w, 4) for w in edges_by_anchor_pos],
        'max_firing_pos_frac': round(max_fp_frac, 4),
        'top2_firing_pos_frac': round(top2_fp_frac, 4),
        'max_anchor_pos_frac': round(max_ap_frac, 4),
        'top2_anchor_pos_frac': round(top2_ap_frac, 4),
        'bin_count': f['bin_count'],
        'max_consec_bin': f['max_consec_bin'],
        'sum_m_minus_1': f['sum_m_minus_1'],
        'sum_m': f['sum_m'],
        'prod_m': f['prod_m'],
    }


def tripwire_evaluate(records, stage_name):
    print(f"\n{'='*72}\nTripwire evaluation: {stage_name}\n{'='*72}", flush=True)
    by_n = defaultdict(list)
    for r in records:
        by_n[r['n']].append(r)

    alarms = []
    per_n_min = {}

    for n, recs in sorted(by_n.items()):
        margins = [r['margin'] for r in recs]
        if not margins:
            continue
        per_n_min[n] = min(margins)
        print(
            f"  n={n}: records={len(recs)}, "
            f"margin min={min(margins)} max={max(margins)} "
            f"avg={sum(margins)/len(margins):.2f}",
            flush=True,
        )

    # T3a — threshold: margin ≤ 2 at any n
    bad_ns = [n for n, v in per_n_min.items() if v <= 2]
    if bad_ns:
        alarms.append(
            f"T3a FIRED: min margin ≤ 2 at n={bad_ns} "
            f"(values: {[(n, per_n_min[n]) for n in bad_ns]})"
        )

    # T3b — trend: strictly decreasing across adjacent n
    ns = sorted(per_n_min.keys())
    if len(ns) >= 2 and all(
        per_n_min[ns[i]] > per_n_min[ns[i + 1]] for i in range(len(ns) - 1)
    ):
        alarms.append(
            f"T3b FIRED: min margin strictly decreasing across n={ns}: "
            f"{[per_n_min[n] for n in ns]}"
        )

    # T1 — at fixed (n, L, ms), margin should be constant if closed form
    # factors through (n, L, ms). Any spread = cycle-shape-dependent.
    by_key = defaultdict(list)
    for r in records:
        key = (r['n'], r['L'], tuple(r['ms']))
        by_key[key].append(r['margin'])
    shape_dep_keys = [
        (k, margins) for k, margins in by_key.items()
        if len(margins) >= 2 and max(margins) != min(margins)
    ]
    if shape_dep_keys:
        worst = max(shape_dep_keys, key=lambda x: max(x[1]) - min(x[1]))
        alarms.append(
            f"T1 FIRED: margin varies at fixed (n,L,ms). "
            f"Worst: {worst[0]} -> {worst[1]} "
            f"(spread {max(worst[1]) - min(worst[1])}). "
            f"{len(shape_dep_keys)} such keys total."
        )
    else:
        n_multi_keys = sum(1 for k, m in by_key.items() if len(m) >= 2)
        print(
            f"  T1 diagnostic: {n_multi_keys} (n,L,ms) keys have ≥2 cycles, "
            f"0 show margin variance — (n,L,ms)-uniform so far.",
            flush=True,
        )

    # T2 — ms-symmetric-function decomposition
    # Bucket by (n, sum_m_minus_1); spread inside bucket should be
    # explainable by (bin_count, max_consec_bin). If a single
    # (n, sum_m_minus_1, bin_count, max_consec_bin) still has spread,
    # that's per-position structure, T2 fires.
    by_ms_bucket = defaultdict(list)
    for r in records:
        key = (
            r['n'],
            r['sum_m_minus_1'],
            r['bin_count'],
            r['max_consec_bin'],
        )
        by_ms_bucket[key].append(r['margin'])
    t2_bad = [
        (k, mg) for k, mg in by_ms_bucket.items()
        if len(mg) >= 3 and max(mg) - min(mg) >= 4 and max(mg) >= 3 * min(mg)
    ]
    if t2_bad:
        worst = max(t2_bad, key=lambda x: max(x[1]) - min(x[1]))
        alarms.append(
            f"T2 FIRED: ms symmetric functions don't explain variation. "
            f"Worst (n,Σ(m-1),bin_count,max_consec): {worst[0]} -> "
            f"margins {sorted(set(worst[1]))[:10]} "
            f"(spread {max(worst[1]) - min(worst[1])})"
        )

    # T4 — firing-position concentration
    max_fp = max(r['max_firing_pos_frac'] for r in records)
    max_top2 = max(r['top2_firing_pos_frac'] for r in records)
    if max_fp > 0.60:
        worst = max(records, key=lambda r: r['max_firing_pos_frac'])
        alarms.append(
            f"T4a FIRED: single firing pos > 60%. "
            f"Worst: {max_fp:.1%} at n={worst['n']} ms={worst['ms']} "
            f"L={worst['L']}"
        )
    if max_top2 > 0.90:
        worst = max(records, key=lambda r: r['top2_firing_pos_frac'])
        alarms.append(
            f"T4b FIRED: top-2 firing pos > 90%. "
            f"Worst: {max_top2:.1%} at n={worst['n']} ms={worst['ms']} "
            f"L={worst['L']}"
        )

    # Anchor-pos second view (Keston-requested, not tripwire by itself)
    max_ap = max(r['max_anchor_pos_frac'] for r in records)
    max_ap_top2 = max(r['top2_anchor_pos_frac'] for r in records)
    print(
        f"  Anchor-coord concentration: max single={max_ap:.1%}, "
        f"max top-2={max_ap_top2:.1%}",
        flush=True,
    )

    # Report
    if alarms:
        print(f"\n  *** {len(alarms)} TRIPWIRE(S) FIRED ***")
        for a in alarms:
            print(f"    {a}")
    else:
        print(f"\n  All tripwires clean. Stage {stage_name} PASS.")

    return alarms


STAGES = {
    'stage1': [
        (5, 3, 40, 3.0, 16),
        (6, 8, 15, 3.0, 17),
        (7, 40, 8, 3.0, 17),
    ],
    'stage2': [
        (8, 500, 3, 12.0, 20),
    ],
    'stage3': [
        # n=9 adversarial: {2^3,3^5,4} orientations + ternary-dense
        # stride=1 to enumerate all binary-3 + quaternary ms at n=9;
        # cycle_cap=4 per ms; L_max=24.
        (9, 1, 4, 20.0, 24),
    ],
}


def filter_stage3_multisets(mss):
    """n=9 adversarial: {2,2,2,3,3,3,3,3,4} orientations and ternary-dense."""
    out = []
    for ms in mss:
        sm = sorted(ms)
        if sm == [2, 2, 2, 3, 3, 3, 3, 3, 4]:
            out.append(ms)
        elif sm == [2, 3, 3, 3, 3, 3, 3, 3, 3]:  # ternary-dense, 1 binary
            out.append(ms)
        elif sm == [2, 2, 3, 3, 3, 3, 3, 3, 3]:  # ternary-dense, 2 binary
            out.append(ms)
    return out


def main():
    stage = sys.argv[1] if len(sys.argv) > 1 else 'stage1'
    if stage not in STAGES:
        print(f"Usage: {sys.argv[0]} [stage1|stage2|stage3]", flush=True)
        sys.exit(2)

    print("=" * 72, flush=True)
    print(f"R4 closed-form extraction probe (2026-04-19) — {stage}", flush=True)
    print("=" * 72, flush=True)

    plan = STAGES[stage]
    all_records = []

    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        if stage == 'stage3':
            sampled = filter_stage3_multisets(multisets)
        else:
            sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets ===", flush=True)
        t0 = time.time()
        count = 0
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n:
                    continue
                r = analyze_k1(ms, n, cycle, movers, det)
                if r is not None:
                    all_records.append(r)
                    count += 1
            step = max(1, len(sampled) // 10)
            if (idx + 1) % step == 0 or idx == len(sampled) - 1:
                print(
                    f"  [{idx+1}/{len(sampled)}]  "
                    f"{time.time()-t0:.0f}s  records={count}",
                    flush=True,
                )

    # Dump
    here = os.path.dirname(os.path.abspath(__file__))
    out_dir = os.path.normpath(
        os.path.join(here, '..', 'lean', 'docs', 'sk', 'sk_phase0_out')
    )
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, f'r4_closed_form_{stage}_2026-04-19.json')
    with open(out_path, 'w') as f:
        json.dump(all_records, f)
    print(f"\n  Wrote {len(all_records)} records to {out_path}", flush=True)

    alarms = tripwire_evaluate(all_records, stage)

    if alarms:
        print(f"\n  {stage} FAIL — {len(alarms)} tripwire(s) fired.")
        print(f"  ABORT. Do NOT commit Lean Phase A infra.")
        sys.exit(1)
    print(f"\n  {stage} PASS.")
    sys.exit(0)


if __name__ == "__main__":
    main()
