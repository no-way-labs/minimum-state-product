#!/usr/bin/env python3
"""n=9 spot-check: does P1-proj and |SK| ≥ 2^(n-1) = 256 hold?

Sub-threshold: product < 4·3^7 = 8748.
Minimum multisets with >=3 binary: {2^3, 3^6}=5832, {2^4, 3^5}=3888, {2^5, 3^4}=2592.

For each small ms, find 1-3 cycles of L >= 20, compute |SK| and projection.
"""
from itertools import product as iproduct
from collections import Counter, defaultdict
import time
import sys

sys.setrecursionlimit(50000)


def enumerate_cycles_bounded(ms, n, L_max, time_budget, max_cycles, L_min=None):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []; seen_cycles = set(); t0 = time.time()
    if L_min is None: L_min = 2*n+2

    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            if L < L_min: return
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max: return
        for p in range(n):
            Lp = config[(p-1)%n]; Sp = config[p]; Rp = config[(p+1)%n]
            km = (p, Lp, Sp, Rp); forced = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced is not None and forced != new_val: continue
                new_det = dict(det); new_det[km] = new_val; ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]; ki = (i,Li,Si,Ri)
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
    non_good = set(all_configs) - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    current = set(non_good)
    while True:
        victims = set()
        for c in current:
            has_forced = False
            for p in range(n):
                ctx = (p, c[(p-1)%n], c[p], c[(p+1)%n])
                if ctx in move_entries:
                    nc = list(c); nc[p] = move_entries[ctx]; nc = tuple(nc)
                    if nc in current: has_forced = True; break
            if not has_forced: victims.add(c)
        if not victims: break
        current -= victims
    return current


def main():
    n = 9
    bound = 2 ** (n - 1)  # 256
    lemma_a = 2**n - 2*n - 2*(n % 2)  # 2^9 - 18 - 2 = 492
    print(f"n=9  Lemma A value = {lemma_a}  |SK| bound 2^(n-1) = {bound}")
    # Top candidates
    candidates = [
        ((2,2,2,3,3,3,3,3,3), 5832),   # {2^3, 3^6}
        ((2,2,2,2,3,3,3,3,3), 3888),   # {2^4, 3^5}
        ((2,2,2,2,2,3,3,3,3), 2592),   # {2^5, 3^4}
        ((2,2,2,2,2,2,3,3,3), 1728),
        ((2,3,2,3,2,3,2,3,3), 2592*3//5),  # permutation
    ]
    for ms, prod in candidates:
        assert sum(1 for m in ms if m==2) >= 3
        print(f"\n=== ms={ms}  prod={prod}  ({sum(1 for m in ms if m==2)} binary) ===", flush=True)
        t0 = time.time()
        # Just find 1 cycle at L>=20
        cycles = enumerate_cycles_bounded(ms, n, L_max=22, time_budget=180.0, max_cycles=2, L_min=2*n+2)
        tt = time.time() - t0
        print(f"  search took {tt:.1f}s, found {len(cycles)} cycles")
        for ci, (cycle, movers, det) in enumerate(cycles):
            L = len(movers)
            V = [set() for _ in range(n)]
            for c in cycle:
                for i in range(n): V[i].add(c[i])
            V_sz = tuple(len(V[i]) for i in range(n))
            t1 = time.time()
            sk = compute_sk(ms, n, cycle, det)
            # Project on drop-p for each p
            proj_sizes = []
            for p in range(n):
                proj = set()
                for c in sk:
                    proj.add(tuple(c[i] for i in range(n) if i != p))
                proj_sizes.append(len(proj))
            max_proj = max(proj_sizes); argmax_p = proj_sizes.index(max_proj)
            fc = Counter(movers)
            tt1 = time.time() - t1
            print(f"  cycle {ci}: L={L} fc={[fc[p] for p in range(n)]} V_sz={V_sz}"
                  f"  |SK|={len(sk)} max_proj={max_proj} @p={argmax_p} (slack {max_proj-bound:+})"
                  f"  [sk+proj {tt1:.1f}s]", flush=True)


if __name__ == "__main__":
    main()
