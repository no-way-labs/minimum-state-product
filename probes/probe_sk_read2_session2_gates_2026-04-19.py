#!/usr/bin/env python3
"""Session-2 gates for Read-2 ansatz (2026-04-19).

Before committing ansatz constants, run two empirical checks per Keston:

  (1) Shadow-ratio constant regression. Fit shadow / (L·Σμ) against
      (n − k)/n for k ∈ {3.0, 3.5, 4.0}; pick best-fit k. Check whether
      the gap (n−3)/n − ratio is growing in n.

  (2) Tripwire c — cross-position landing ratio. For each T_N1 config x
      and each position p', if det[(p', ctx_at_p'(x))] is defined and
      yields a target ≠ x, check if target ∈ T_N1. Landing ratio =
      |landings in T_N1| / |candidate firings|. Bounded below
      uniformly → floor is structural; varies > 2× at fixed (n, L, ms)
      → T1 resurfaces at a different object.
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
analyze_k1 = _scaffold.analyze_k1
value_sets = _scaffold.value_sets


def compute_gates(ms, n, cycle, movers, det):
    L = len(movers)
    C = set(cycle)
    V = value_sets(cycle, n)
    mu = [len(V[i]) - 1 for i in range(n)]
    Sigma_mu = sum(mu)

    # Build T_N1 and det dict for move lookup
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - C
    T = set()
    for c in VC_NG:
        if any(sum(1 for i in range(n) if c[i] != cc[i]) == 1 for cc in cycle):
            T.add(c)

    # det table: (p, L_ctx, S_ctx, R_ctx) -> new value where new ≠ S
    move_entries = {}
    for (p, Lv, Sv, Rv), val in det.items():
        if val != Sv:
            move_entries[(p, Lv, Sv, Rv)] = val

    # Cross-position candidate / landing count
    cand = 0
    land = 0
    # Shadow count (re-verify) = firings at p_k from Case-A tails
    shadow = 0
    for k in range(L):
        p_k = movers[k]
        excluded = {(p_k - 1) % n, p_k % n, (p_k + 1) % n}
        c_k = cycle[k]
        for q in range(n):
            if q in excluded:
                continue
            for v in V[q]:
                if v == c_k[q]:
                    continue
                tail = list(c_k); tail[q] = v; tail = tuple(tail)
                if tail in C:
                    continue
                if tail not in T:
                    continue
                # shadow edge: fire at p_k
                head = list(cycle[(k+1) % L]); head[q] = v; head = tuple(head)
                if head in T:
                    shadow += 1
                # cross-position firings
                for p_prime in range(n):
                    if p_prime == p_k:
                        continue
                    ctx = (p_prime,
                           tail[(p_prime - 1) % n],
                           tail[p_prime],
                           tail[(p_prime + 1) % n])
                    if ctx not in move_entries:
                        continue
                    cand += 1
                    new_val = move_entries[ctx]
                    tgt = list(tail); tgt[p_prime] = new_val; tgt = tuple(tgt)
                    if tgt in T:
                        land += 1

    return {
        'Sigma_mu': Sigma_mu,
        'shadow_by_step': shadow,  # may differ from raw (restrict to tails ∈ T)
        'cross_cand': cand,
        'cross_land': land,
        'landing_ratio': (land / cand) if cand > 0 else None,
    }


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


def main():
    print("=" * 78)
    print("Session-2 gates: shadow-ratio constant + tripwire c (2026-04-19)")
    print("=" * 78)

    rows = []
    t0 = time.time()
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
            g = compute_gates(ms, n, cycle, movers, det)
            r.update(g)
            r['L_Sigma_mu'] = L * g['Sigma_mu']
            r['shadow_ratio'] = g['shadow_by_step'] / r['L_Sigma_mu'] \
                                if r['L_Sigma_mu'] > 0 else 0
            rows.append(r)
    print(f"  Collected {len(rows)} records in {time.time()-t0:.1f}s\n")

    # ------ Gate 1: shadow-ratio constant regression ------
    print("  Gate 1: shadow_ratio = shadow / (L · Σμ) vs (n-k)/n")
    by_n = defaultdict(list)
    for r in rows:
        by_n[r['n']].append(r)

    # Per-n mean shadow_ratio
    print(f"    {'n':>3} | {'recs':>4} | mean ratio | (n-3)/n | gap   | "
          f"(n-3.5)/n | gap  | (n-4)/n | gap")
    means = {}
    for n, rs in sorted(by_n.items()):
        ratios = [r['shadow_ratio'] for r in rs]
        mean = sum(ratios) / len(ratios)
        means[n] = mean
        r30 = (n - 3) / n
        r35 = (n - 3.5) / n
        r40 = (n - 4) / n
        print(f"    {n:>3} | {len(rs):>4} | {mean:.4f}     | {r30:.4f}  | "
              f"{r30-mean:+.4f} | {r35:.4f}    | {r35-mean:+.4f} | "
              f"{r40:.4f}  | {r40-mean:+.4f}")

    # Best-fit k across all n: minimize sum of squared residuals
    ns = sorted(means.keys())
    best_k, best_err = None, float('inf')
    for k_try in [2.8, 3.0, 3.2, 3.4, 3.5, 3.6, 3.7, 3.8, 4.0]:
        err = sum(((n - k_try) / n - means[n]) ** 2 for n in ns)
        if err < best_err:
            best_err = err
            best_k = k_try
    print(f"\n  Best-fit k (constant in (n-k)/n): k = {best_k}, "
          f"sum-sq err = {best_err:.5f}")

    # Gap trend
    print("\n  Gap (n-3)/n − ratio across n:")
    gaps = [(n, (n-3)/n - means[n]) for n in ns]
    for n, gap in gaps:
        print(f"    n={n}: gap={gap:+.4f}")
    gap_trend = all(gaps[i][1] <= gaps[i+1][1] + 0.005 for i in range(len(gaps)-1))
    # widening if gap at max n > gap at any smaller n
    widening = gaps[-1][1] > max(g[1] for g in gaps[:-1]) if len(gaps) > 1 else False
    print(f"  Gap widening at largest n? {widening}")

    # ------ Gate 2: landing ratio (tripwire c) ------
    print("\n  Gate 2: cross-position landing ratio (tripwire c)")
    print(f"    {'n':>3} | {'recs':>4} | mean land | min | max | p10 | p90 | "
          f"max/min at fixed (n,L,ms)")

    for n, rs in sorted(by_n.items()):
        lrs = [r['landing_ratio'] for r in rs if r['landing_ratio'] is not None]
        if not lrs:
            print(f"    {n:>3} | {len(rs):>4} | NO DATA")
            continue
        mean = sum(lrs) / len(lrs)
        lrs_sorted = sorted(lrs)
        p10 = lrs_sorted[max(0, len(lrs_sorted)//10)]
        p90 = lrs_sorted[min(len(lrs_sorted)-1, 9*len(lrs_sorted)//10)]
        # variance at fixed (n, L, ms)
        by_key = defaultdict(list)
        for r in rs:
            if r['landing_ratio'] is not None:
                by_key[(r['L'], tuple(r['ms']))].append(r['landing_ratio'])
        max_ratio_spread = 0.0
        worst_key = None
        for key, xs in by_key.items():
            if len(xs) >= 2 and min(xs) > 0:
                rr = max(xs) / min(xs)
                if rr > max_ratio_spread:
                    max_ratio_spread = rr
                    worst_key = key
        print(f"    {n:>3} | {len(rs):>4} | {mean:.3f}    | "
              f"{min(lrs):.3f}| {max(lrs):.3f}| {p10:.3f} | {p90:.3f} | "
              f"{max_ratio_spread:.2f}x (worst key={worst_key})")

    global_min = min(r['landing_ratio'] for r in rows
                     if r['landing_ratio'] is not None)
    global_max_spread = 0.0
    worst_spread_key = None
    by_key_global = defaultdict(list)
    for r in rows:
        if r['landing_ratio'] is not None:
            key = (r['n'], r['L'], tuple(r['ms']))
            by_key_global[key].append(r['landing_ratio'])
    for key, xs in by_key_global.items():
        if len(xs) >= 2 and min(xs) > 0:
            rr = max(xs) / min(xs)
            if rr > global_max_spread:
                global_max_spread = rr
                worst_spread_key = key

    print(f"\n  Global min landing ratio: {global_min:.3f}")
    print(f"  Max spread at fixed (n,L,ms): {global_max_spread:.2f}x "
          f"(at {worst_spread_key})")

    out_dir = os.path.normpath(
        os.path.join(HERE, '..', 'lean', 'docs', 'sk', 'sk_phase0_out')
    )
    out_path = os.path.join(
        out_dir, 'r4_read2_session2_gates_2026-04-19.json'
    )
    with open(out_path, 'w') as f:
        json.dump(rows, f)
    print(f"\n  Wrote {out_path}")

    # Tripwire c verdict
    if global_max_spread > 2.0:
        print(f"\n  TRIPWIRE C FIRED: landing ratio spread > 2× at fixed "
              f"(n, L, ms). Cycle shape sneaking back in.")
        sys.exit(1)
    else:
        print(f"\n  Tripwire c clean: landing ratio spread ≤ 2× uniformly.")
    print(f"\n  Session-2 gates: {'CLEAN' if global_max_spread <= 2.0 else 'FAIL'}")
    sys.exit(0)


if __name__ == "__main__":
    main()
