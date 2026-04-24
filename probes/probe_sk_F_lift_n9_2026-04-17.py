#!/usr/bin/env python3
"""(F) at n=9, 10 + lift-basis search.

TARGETS:
  1. Verify (F) ∀p |π_p(SK∪C)| ≥ 2^(n-1) at n=9, n=10 where bound is 256, 512.
  2. Find a lift basis L_p ⊆ SK∪C with |π_p(L_p)| ≥ 2^(n-1).
     Candidates:
       (i) Binary cube {0,1}^(n-1) via 2-subset labeling (tested n=5 ok, n=6 fail).
       (ii) Cycle-rotated cube: start from each c0 ∈ C, flip "binary positions" in
            all 2^k subsets where k = # binary positions in V-structure.
       (iii) Hamming-1 peel closure: {c ∈ VC_NG : exists c' ∈ C with ||c-c'||_H = 1,
             and monotonicity ⇒ c ∈ SK}.
  3. Probe forward-closure structural induction signals:
       - peeling depth histogram (how many peel steps to SK)
       - |S_k| = size at peel step k; check if |S_k| ≥ bound at all k
       - |π_p(S_k)| at each peel step k.

Note: at n=9+, cycle enumeration is expensive. Use construction-based good cycles
instead of exhaustive DFS where possible. For n=9, ms=(2,3,3,3,3,3,3,3,2) endpoint-
binary has a known good cycle of length 25 (CLB witness); but 25 > 2n+2=20 so OK.

Simpler: use ms=(2,2,2,3,3,3,3,3,3) with aggressive time budget to find any
good cycle at L ≥ 2n+2.
"""
from itertools import product as iproduct, combinations
from collections import defaultdict, Counter
import time, sys
sys.setrecursionlimit(100000)


def enumerate_cycles(ms, n, L_min, L_max, time_budget, max_cycles, start_limit=None):
    all_starts = list(iproduct(*[range(m) for m in ms]))
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


def compute_sk_and_peels(ms, n, cycle, det):
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
    peel_sizes = [len(remaining)]
    peel_depth = {c: None for c in non_good}
    step = 0
    while True:
        sinks = {c for c in remaining if not any(t in remaining for t in adj.get(c, []))}
        if not sinks: break
        for c in sinks: peel_depth[c] = step
        remaining -= sinks
        peel_sizes.append(len(remaining))
        step += 1
    sk = remaining
    for c in sk: peel_depth[c] = 10**9  # infinite / in SK
    return sk, V_sorted, cycle_set, peel_sizes, peel_depth, adj


def f_probe(n, ms, cycle, det, bound):
    sk, V_sorted, cycle_set, peel_sizes, _, _ = compute_sk_and_peels(ms, n, cycle, det)
    if not sk: return None
    skuc = sk | cycle_set

    # (F) sizes
    F_sizes = []
    for p in range(n):
        proj = {tuple(c[i] for i in range(n) if i != p) for c in skuc}
        F_sizes.append(len(proj))

    # (A) sizes
    A_sizes = []
    for p in range(n):
        proj = {tuple(c[i] for i in range(n) if i != p) for c in sk}
        A_sizes.append(len(proj))

    # Binary-lift coverage per p
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
        if total > 30000:
            label = tuple(pairs[0] for pairs in labels_per_pos)
            B = set(iproduct(*label))
            proj_skuc = {tuple(c[i] for i in range(n) if i != p) for c in skuc}
            covered = sum(1 for b in B if b in proj_skuc)
            bin_covs.append(covered)
            continue
        proj_skuc = {tuple(c[i] for i in range(n) if i != p) for c in skuc}
        best = 0
        for label in iproduct(*labels_per_pos):
            B = set(iproduct(*label))
            covered = sum(1 for b in B if b in proj_skuc)
            if covered > best: best = covered
            if best == 2**(n-1): break
        bin_covs.append(best)

    return {
        '|SK|': len(sk), 'L': len(cycle_set),
        'F_sizes': F_sizes, 'A_sizes': A_sizes,
        'bin_covs': bin_covs,
        'peel_depth_len': len(peel_sizes),
        'peel_sizes': peel_sizes,
    }


def main():
    print("=" * 100)
    print("(F) + lift basis at n=9, 10 — scaling check")
    print("=" * 100)

    plan = [
        (9, [(2,2,2,3,3,3,3,3,3)], 22, 1, 120.0),
        (10, [(2,2,2,3,3,3,3,3,3,3)], 24, 1, 180.0),
    ]

    for n, ms_list, L_max, max_cycles, tb in plan:
        bound = 2 ** (n - 1)
        print(f"\n=== n={n} bound={bound} L_min={2*n+2} ===")
        for ms in ms_list:
            t0 = time.time()
            cycles = enumerate_cycles(ms, n, L_min=2*n+2, L_max=L_max,
                                      time_budget=tb, max_cycles=max_cycles,
                                      start_limit=10)
            print(f"  found {len(cycles)} cycles in {time.time()-t0:.1f}s")
            for ci, (cycle, movers, det) in enumerate(cycles):
                t1 = time.time()
                r = f_probe(n, ms, cycle, det, bound)
                dt = time.time() - t1
                if r is None: continue
                print(f"\n  ms={ms} L={r['L']} cycle#{ci} |SK|={r['|SK|']} [probe {dt:.1f}s]")

                F_min = min(r['F_sizes']); F_max = max(r['F_sizes'])
                A_min = min(r['A_sizes']); A_max = max(r['A_sizes'])
                print(f"    (F) ∀p |π_p(SK∪C)|: min={F_min} max={F_max} bound={bound}  "
                      f"({'OK' if F_min>=bound else 'FAIL'})")
                print(f"    (A) ∃p |π_p(SK)|:   max={A_max} (min={A_min}) bound={bound}  "
                      f"({'OK' if A_max>=bound else 'FAIL'})")
                bc_max = max(c for c in r['bin_covs'] if c is not None)
                bc_min = min(c for c in r['bin_covs'] if c is not None)
                bin_full = sum(1 for c in r['bin_covs'] if c == 2**(n-1))
                print(f"    binary lift: max={bc_max} min={bc_min} bound={bound}  "
                      f"(# p with full lift: {bin_full}/{n})")
                print(f"    peel depth: {r['peel_depth_len']}; size trajectory[0..5]: "
                      f"{r['peel_sizes'][:6]}, last: {r['peel_sizes'][-3:]}")


if __name__ == "__main__":
    main()
