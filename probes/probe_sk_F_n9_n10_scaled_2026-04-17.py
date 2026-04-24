#!/usr/bin/env python3
"""(F) at n=9, 10 — multiple cycles and ms variants.

Uses reachability from seed cycles to compute SK without exhaustive enum.
Constructs good cycles by:
 (i) DFS-enumeration with larger time budget
 (ii) cycle-shape-invariance: fixed shape at lower n generates SK pattern.
"""
from itertools import product as iproduct, combinations
from collections import defaultdict, Counter
import time, sys
sys.setrecursionlimit(100000)


def enumerate_cycles(ms, n, L_min, L_max, time_budget, max_cycles, start_limit=None, start_filter=None):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    if start_filter: all_starts = [s for s in all_starts if start_filter(s)]
    if start_limit: all_starts = all_starts[:start_limit]
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
    return remaining, V_sorted, cycle_set


def f_probe(n, ms, cycle, det, bound):
    sk, V_sorted, cycle_set = compute_sk(ms, n, cycle, det)
    if not sk: return None
    skuc = sk | cycle_set

    F_sizes = []
    for p in range(n):
        proj = {tuple(c[i] for i in range(n) if i != p) for c in skuc}
        F_sizes.append(len(proj))

    A_sizes = []
    for p in range(n):
        proj = {tuple(c[i] for i in range(n) if i != p) for c in sk}
        A_sizes.append(len(proj))

    # Binary-lift: for each p, find best labeling
    bin_covs = []
    for p in range(n):
        labels_per_pos = []
        skip = False
        for i in range(n):
            if i == p: continue
            if len(V_sorted[i]) < 2: skip = True; break
            labels_per_pos.append(list(combinations(V_sorted[i], 2)))
        if skip:
            bin_covs.append(None); continue
        total = 1
        for lc in labels_per_pos: total *= len(lc)
        proj_skuc = {tuple(c[i] for i in range(n) if i != p) for c in skuc}
        if total > 30000:
            label = tuple(pairs[0] for pairs in labels_per_pos)
            B = set(iproduct(*label))
            covered = sum(1 for b in B if b in proj_skuc)
            bin_covs.append(covered)
            continue
        best = 0
        for label in iproduct(*labels_per_pos):
            B = set(iproduct(*label))
            covered = sum(1 for b in B if b in proj_skuc)
            if covered > best: best = covered
            if best == 2**(n-1): break
        bin_covs.append(best)

    return {
        '|SK|': len(sk), 'L': len(cycle_set),
        'F_sizes': F_sizes, 'A_sizes': A_sizes, 'bin_covs': bin_covs,
        'V_sorted_sizes': [len(v) for v in V_sorted],
    }


def main():
    print("=" * 100)
    print("(F) SCALING: n=9 (multiple ms/cycles), n=10 focused")
    print("=" * 100)

    n = 9
    bound = 2**(n-1)
    ms_list = [
        (2,2,2,3,3,3,3,3,3),
        (2,2,3,2,3,3,3,3,3),
        (2,3,2,3,2,3,3,3,3),
        (2,3,3,3,3,3,3,3,2),
    ]
    print(f"\n=== n={n} bound={bound} ===")
    for ms in ms_list:
        t0 = time.time()
        # seed from c_0=0 configs
        cycles = enumerate_cycles(ms, n, L_min=2*n+2, L_max=22,
                                  time_budget=60, max_cycles=1,
                                  start_limit=5)
        dt = time.time() - t0
        print(f"\n  ms={ms}: enumerate {dt:.1f}s, found {len(cycles)} cycles")
        for ci, (cycle, movers, det) in enumerate(cycles):
            r = f_probe(n, ms, cycle, det, bound)
            if r is None: continue
            print(f"    ms={ms} L={r['L']} cycle#{ci} |SK|={r['|SK|']} V={r['V_sorted_sizes']}")
            F_min = min(r['F_sizes']); F_max = max(r['F_sizes'])
            A_min = min(r['A_sizes']); A_max = max(r['A_sizes'])
            print(f"      (F) ∀p |π_p(SK∪C)|: min={F_min} max={F_max}  "
                  f"({'OK' if F_min>=bound else 'FAIL'})")
            print(f"      (A) max|π_p(SK)|={A_max} (min={A_min})  "
                  f"({'OK' if A_max>=bound else 'FAIL'})")
            bcs = [c for c in r['bin_covs'] if c is not None]
            if bcs:
                bin_full = sum(1 for c in r['bin_covs'] if c == 2**(n-1))
                print(f"      binary lift max={max(bcs)} min={min(bcs)} (full @ {bin_full}/{n})")

    # n=10 attempt
    n = 10
    bound = 2**(n-1)
    ms_list = [
        (2,2,2,3,3,3,3,3,3,3),
        (2,3,3,3,3,3,3,3,3,2),
    ]
    print(f"\n=== n={n} bound={bound} ===")
    for ms in ms_list:
        t0 = time.time()
        cycles = enumerate_cycles(ms, n, L_min=2*n+2, L_max=25,
                                  time_budget=120, max_cycles=1,
                                  start_limit=3)
        dt = time.time() - t0
        print(f"\n  ms={ms}: enumerate {dt:.1f}s, found {len(cycles)} cycles")
        for ci, (cycle, movers, det) in enumerate(cycles):
            r = f_probe(n, ms, cycle, det, bound)
            if r is None: continue
            print(f"    L={r['L']} cycle#{ci} |SK|={r['|SK|']} V={r['V_sorted_sizes']}")
            F_min = min(r['F_sizes']); F_max = max(r['F_sizes'])
            A_min = min(r['A_sizes']); A_max = max(r['A_sizes'])
            print(f"      (F) ∀p |π_p(SK∪C)|: min={F_min} max={F_max}  "
                  f"({'OK' if F_min>=bound else 'FAIL'})")
            print(f"      (A) max|π_p(SK)|={A_max} (min={A_min})  "
                  f"({'OK' if A_max>=bound else 'FAIL'})")
            bcs = [c for c in r['bin_covs'] if c is not None]
            if bcs:
                bin_full = sum(1 for c in r['bin_covs'] if c == 2**(n-1))
                print(f"      binary lift max={max(bcs)} min={min(bcs)} (full @ {bin_full}/{n})")


if __name__ == "__main__":
    main()
