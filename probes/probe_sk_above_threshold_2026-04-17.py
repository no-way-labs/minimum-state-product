#!/usr/bin/env python3
"""Causal intervention: is the |SK| >= 2^(n-1) bound driven by sub-threshold?

Empirical evidence for Lemma C comes exclusively from sub-threshold runs.
We've treated sub-threshold as structural context for the LB contradiction,
but haven't isolated WHETHER the bound itself needs it.

Intervention: probe good cycles at products at, above, and well above M_n
for n=5..8. If |SK| >= 2^(n-1) still holds universally, sub-threshold is
NOT causal for the bound (only for the LB contradiction downstream).
If it fails above threshold, sub-threshold IS load-bearing and we need
to locate the exact regime of applicability.

Scope: n=5..8, multisets at products spanning below M_n through several
times M_n. Find cycles of L >= 2n+2, compute |SK|, check the floor.
"""
from itertools import product as iproduct
from collections import defaultdict
import time
import math


def m_n_sharp(n):
    if n == 4: return 24
    if 5 <= n <= 8: return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def enumerate_cycles(ms, n, L_min, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []; seen = set(); t0 = time.time()

    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            if L < L_min: return
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen:
                seen.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max: return
        for p in range(n):
            Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp)
            forced = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced is not None and forced != new_val: continue
                new_det = dict(det); new_det[km] = new_val
                ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si: ok = False; break
                    new_det[ki] = Si
                if not ok: continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path): continue
                dfs(start, nc, new_det, path + [nc], movers + [p])

    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget: break
        dfs(start, start, {}, [start], [])
    return found


def compute_sk(ms, n, cycle, det):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n): V[i].add(c[i])
    V_sorted = [sorted(V[i]) for i in range(n)]
    all_configs = list(iproduct(*V_sorted))
    cycle_set = set(cycle)
    non_good = [c for c in all_configs if c not in cycle_set]
    ng_set = set(non_good)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in move_entries:
                nc = list(c); nc[p] = move_entries[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append(nc)
    remaining = set(non_good)
    while True:
        sinks = {c for c in remaining if not any(t in remaining for t in adj.get(c, []))}
        if not sinks: break
        remaining -= sinks
    return remaining, len(ng_set)


def main():
    """
    For each n in 5..8, test ms at multiple product regimes:
      - Below M_n (control: known to satisfy |SK| >= 2^(n-1))
      - At M_n exactly (threshold)
      - Above M_n (intervention)
      - Well above M_n at 2x, 3x (intervention)
    """
    print("=" * 100)
    print("CAUSAL INTERVENTION: does |SK| >= 2^(n-1) depend on sub-threshold?")
    print("=" * 100)

    # Build test plan: for each n, ms chosen to span product regimes
    plan = [
        # n=5, M_5 = 96
        (5, [(2,2,2,3,3),      # 72 (sub-M)
             (2,2,2,2,3),      # 48 (sub-M, all-small)
             (2,2,2,3,4),      # 96 (at M_5 — CLB witness)
             (2,2,2,4,4),      # 128 (above M_5)
             (2,2,3,3,4),      # 144 (above, 1.5x)
             (2,3,3,3,3),      # 162 (above, 1.7x)
             (2,2,3,4,4),      # 192 (2x M_5)
             (3,3,3,3,3),      # 243 (2.5x, all-ternary)
             ], 20),
        # n=6, M_6 = 288
        (6, [(2,2,2,3,3,3),    # 216 (sub-M)
             (2,2,2,2,3,3),    # 144 (sub-M, lots of binary)
             (2,2,2,3,3,4),    # 288 (at M_6)
             (2,2,2,3,4,4),    # 384 (above M_6)
             (2,2,3,3,3,4),    # 432 (1.5x)
             (2,2,3,3,4,4),    # 576 (2x)
             (3,3,3,3,3,3),    # 729 (2.5x, all-ternary)
             ], 18),
        # n=7, M_7 = 864
        (7, [(2,2,2,3,3,3,3),  # 648 (sub-M)
             (2,2,2,3,3,3,4),  # 864 (at M_7)
             (2,2,2,3,3,4,4),  # 1152 (above)
             (2,2,3,3,3,3,4),  # 1296 (1.5x)
             (2,2,3,3,3,4,4),  # 1728 (2x)
             ], 18),
        # n=8, M_8 = 2592
        (8, [(2,2,2,3,3,3,3,3),    # 1944 (sub-M)
             (2,2,2,3,3,3,3,4),    # 2592 (at M_8)
             (2,2,2,3,3,3,4,4),    # 3456 (above)
             (2,2,3,3,3,3,3,4),    # 3888 (1.5x)
             ], 20),
    ]

    violations = []
    by_n_regime = defaultdict(list)  # (n, regime) -> list of (ms, min_SK, bound, slack)

    for n, ms_list, L_max in plan:
        Mn = m_n_sharp(n)
        bound = 2 ** (n - 1)
        print(f"\n=== n={n}  M_n={Mn}  bound 2^(n-1)={bound}  L_range=[{2*n+2},{L_max}] ===")
        t_n = time.time()
        for ms in ms_list:
            prod = math.prod(ms)
            regime = ("sub" if prod < Mn
                      else "at"  if prod == Mn
                      else "above" if prod < 2*Mn
                      else "high")
            t_ms = time.time()
            cycles = enumerate_cycles(ms, n,
                                      L_min=2*n+2,
                                      L_max=L_max,
                                      time_budget=45.0,
                                      max_cycles=8)
            if not cycles:
                print(f"  ms={ms!s:32s} prod={prod:<6} {regime:<5} "
                      f"no cycle  ({time.time()-t_ms:.1f}s)")
                continue
            sk_sizes = []
            for cycle, movers, det in cycles:
                sk, ng_size = compute_sk(ms, n, cycle, det)
                sk_sizes.append((len(sk), len(cycle), ng_size))
            min_sk = min(s for s, _, _ in sk_sizes)
            min_L = min(L for _, L, _ in sk_sizes)
            max_L = max(L for _, L, _ in sk_sizes)
            slack = min_sk - bound
            verdict = "OK" if min_sk >= bound else "VIOLATES"
            print(f"  ms={ms!s:32s} prod={prod:<6} {regime:<5} "
                  f"cycles={len(cycles):<2} L=[{min_L}..{max_L}] "
                  f"min|SK|={min_sk:<5} slack={slack:+d} {verdict} "
                  f"({time.time()-t_ms:.1f}s)")
            by_n_regime[(n, regime)].append((ms, min_sk, bound, slack))
            if min_sk < bound:
                violations.append((n, ms, prod, regime, min_sk, bound))
        print(f"  (total {time.time()-t_n:.1f}s for n={n})")

    # Summary
    print("\n" + "=" * 100)
    print("REGIME SUMMARY: min slack over (n, regime)")
    print("=" * 100)
    for (n, regime) in sorted(by_n_regime):
        recs = by_n_regime[(n, regime)]
        if not recs: continue
        min_slack = min(r[3] for r in recs)
        max_slack = max(r[3] for r in recs)
        print(f"  n={n} regime={regime:<5}  #ms={len(recs):<2}  "
              f"min_slack={min_slack:+d}  max_slack={max_slack:+d}")

    print("\n" + "=" * 100)
    print("VIOLATIONS (|SK| < 2^(n-1))")
    print("=" * 100)
    if not violations:
        print("  NONE — bound holds at all tested regimes.")
        print("  => sub-threshold is NOT causal for the bound itself.")
        print("     it is only causal for the downstream LB contradiction.")
    else:
        for n, ms, prod, regime, sk, bound in violations:
            print(f"  n={n} ms={ms} prod={prod} regime={regime} "
                  f"|SK|={sk} < bound={bound}")
        print(f"\n  => sub-threshold (or something correlated) IS causal.")
        print(f"  => {len(violations)} violation(s) found.")


if __name__ == "__main__":
    main()
