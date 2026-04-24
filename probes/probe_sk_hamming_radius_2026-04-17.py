#!/usr/bin/env python3
"""Larger Hamming-radius kernels for Lemma C.

peel(N_k(C)) ⊆ SK for each k (monotonicity).
At k=1 we showed |peel(N_1(C))| ≥ 2^(n-1) tight at n=5,7 but FAILS at n=8 (min=84<128).

Test k=2, 3, …, n at n=7, 8, 9 with sub-threshold ms. Measure:
  - |peel(N_k(C))| / 2^(n-1)
  - Whether |peel(N_k(C))| ≥ 2^(n-1) universally.
  - Smallest k that closes the bound.
"""
from itertools import product as iproduct
from collections import defaultdict
import time, sys
sys.setrecursionlimit(100000)


def enumerate_cycles_from(ms, n, L_min, L_max, time_budget, max_cycles, start_config):
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
            km = (p, Lp, Sp, Rp); forced = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced is not None and forced != new_val: continue
                new_det = dict(det); new_det[km] = new_val; ok = True
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
    dfs(start_config, start_config, {}, [start_config], [])
    return found


def peel_subset(subset, adj_ng):
    """Peel a subset S ⊆ ng: iteratively remove configs with no out-neighbor in S ∩ ng."""
    remaining = set(subset)
    while True:
        sinks = {c for c in remaining if not any(t in remaining for t in adj_ng.get(c, []))}
        if not sinks: break
        remaining -= sinks
    return remaining


def hamming_min(c, cycle_set, n):
    m = n + 1
    for d in cycle_set:
        h = sum(1 for i in range(n) if c[i] != d[i])
        if h < m: m = h
        if m == 0: return 0
    return m


def build_structures(ms, n, cycle, det):
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
    adj_ng = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in move_entries:
                nc = list(c); nc[p] = move_entries[key]; nc = tuple(nc)
                if nc in ng_set: adj_ng[c].append(nc)
    return V_sorted, cycle_set, ng_set, adj_ng


def main():
    print("=" * 100)
    print("HAMMING RADIUS kernels: |peel(N_k(C))| vs 2^(n-1)")
    print("=" * 100)
    cases = [
        (5, (2,2,3,3,3), 13, 10.0),
        (5, (2,2,2,3,3), 13, 10.0),
        (6, (2,2,2,3,3,3), 15, 15.0),
        (6, (2,2,3,2,3,3), 15, 15.0),
        (7, (2,2,2,3,3,3,3), 17, 30.0),
        (7, (2,2,3,2,3,3,3), 17, 30.0),
        (8, (2,2,2,3,3,3,3,3), 19, 45.0),
        (8, (2,2,3,2,3,3,3,3), 19, 45.0),
        (9, (2,2,3,2,3,3,3,3,3), 22, 60.0),
        (9, (2,2,2,3,3,3,3,3,3), 22, 90.0),
        (10, (2,2,3,2,3,3,3,3,3,3), 22, 180.0),
        (10, (2,3,2,3,2,3,3,3,3,3), 22, 180.0),
    ]
    for n, ms, L_max, tb in cases:
        bound = 2**(n-1)
        print(f"\n=== n={n} ms={ms} bound={bound} ===")
        cycles = enumerate_cycles_from(ms, n, L_min=2*n+2, L_max=L_max,
                                       time_budget=tb, max_cycles=1,
                                       start_config=tuple([0]*n))
        if not cycles: print("  no cycles"); continue
        cycle, movers, det = cycles[0]
        print(f"  L={len(cycle)}")
        V_sorted, cycle_set, ng_set, adj_ng = build_structures(ms, n, cycle, det)
        # compute Hamming min distance for each config in ng
        dists = {c: hamming_min(c, cycle_set, n) for c in ng_set}
        max_d = max(dists.values())
        # |N_≤k(C) ∩ ng| per k
        SK = peel_subset(ng_set, adj_ng)
        print(f"  |VC_NG|={len(ng_set)} |SK|={len(SK)} max_hamming_dist={max_d}")
        for k in range(1, max_d + 1):
            Nk = {c for c in ng_set if dists[c] <= k}
            pk = peel_subset(Nk, adj_ng)
            marker = "OK" if len(pk) >= bound else "FAIL"
            print(f"  k={k}  |N_≤k|={len(Nk):5d}  |peel(N_≤k)|={len(pk):5d}  "
                  f"vs {bound} → {marker}  (|peel|/bound = {len(pk)/bound:.2f})")


if __name__ == "__main__":
    main()
