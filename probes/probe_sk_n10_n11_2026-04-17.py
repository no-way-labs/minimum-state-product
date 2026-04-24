#!/usr/bin/env python3
"""n=10, 11 attempts using smart DFS seeding.

Strategy: start from config (0,...,0) which is likely on short good cycles.
Use ms=(2,2,3,2,3,...,3) which gave fast results at n=9 (24s for L=21).
"""
from itertools import product as iproduct, combinations
from collections import defaultdict
import time, sys
sys.setrecursionlimit(100000)


def enumerate_cycles_from(ms, n, L_min, L_max, time_budget, max_cycles, start_config):
    """DFS only from a single start config."""
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
    return remaining, V_sorted, cycle_set


def f_probe(n, ms, cycle, det, bound):
    sk, V_sorted, cycle_set = compute_sk(ms, n, cycle, det)
    if not sk: return None
    skuc = sk | cycle_set
    F_sizes, A_sizes = [], []
    for p in range(n):
        F_sizes.append(len({tuple(c[i] for i in range(n) if i != p) for c in skuc}))
        A_sizes.append(len({tuple(c[i] for i in range(n) if i != p) for c in sk}))
    return {'|SK|': len(sk), 'L': len(cycle_set),
            'F_min': min(F_sizes), 'F_max': max(F_sizes),
            'A_min': min(A_sizes), 'A_max': max(A_sizes),
            'V_sizes': [len(v) for v in V_sorted]}


def main():
    print("=" * 100)
    print("n=10, 11 good cycles via single-start DFS")
    print("=" * 100)

    plan = [
        (10, (2,2,3,2,3,3,3,3,3,3), 23, 300.0),
        (10, (2,2,2,3,3,3,3,3,3,3), 23, 300.0),
        (10, (2,3,2,3,2,3,3,3,3,3), 23, 300.0),
        (11, (2,2,3,2,3,3,3,3,3,3,3), 25, 600.0),
    ]

    for n, ms, L_max, tb in plan:
        bound = 2**(n-1)
        print(f"\n=== n={n} ms={ms} bound={bound} L_min={2*n+2} ===")
        t0 = time.time()
        cycles = enumerate_cycles_from(ms, n, L_min=2*n+2, L_max=L_max,
                                       time_budget=tb, max_cycles=1,
                                       start_config=tuple([0]*n))
        print(f"  DFS {time.time()-t0:.1f}s: found {len(cycles)} cycles")
        for ci, (cycle, movers, det) in enumerate(cycles):
            t1 = time.time()
            r = f_probe(n, ms, cycle, det, bound)
            dt = time.time() - t1
            if r is None: continue
            print(f"  L={r['L']} |SK|={r['|SK|']} V_sizes={r['V_sizes']} ({dt:.1f}s)")
            print(f"    (F) ∀p min={r['F_min']} max={r['F_max']} vs {bound}  "
                  f"({'OK' if r['F_min']>=bound else 'FAIL'})")
            print(f"    (A) ∃p max={r['A_max']} (min={r['A_min']}) vs {bound}  "
                  f"({'OK' if r['A_max']>=bound else 'FAIL'})")


if __name__ == "__main__":
    main()
