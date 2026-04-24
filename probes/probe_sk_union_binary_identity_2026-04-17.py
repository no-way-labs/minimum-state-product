#!/usr/bin/env python3
"""Is π_p(SK ∪ C) exactly the binary sub-codomain when tight?

(F) is tight at min-L cycles: ∀p |π_p(SK∪C)| = 2^(n-1) for some p at n=5,6 min-L.
Test:
  - Pick the tight p (where |π_p(SK∪C)|=2^(n-1)).
  - Choose binary labeling of valueSet(i)={a_i, b_i} for i≠p.
  - Is π_p(SK∪C) = {0,1}^(n-1) under that labeling?
  - If YES: proves the bound at tight case, via "every binary config is in SK∪C".

If that's the structural fact, then (F) factors as:
  ∀p. |π_p(SK∪C)| ≥ |binary_subcodomain_p| = 2·|V_i| with |V_i|≥2 ≥ 2^(n-1).

Actually the clean statement would be:
  ∀p ∃binary labeling L with L_i ⊆ V_i, |L_i|=2.
  For every b ∈ ∏ L_i, there exists c ∈ SK∪C with π_p(c) = b.

Equivalent: binary_cube_lift(L) ⊆ SK ∪ C.
"""
from itertools import product as iproduct, combinations
from collections import defaultdict, Counter
import time, sys
sys.setrecursionlimit(100000)


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


def test_binary_lift_in_skuc(n, ms, cycle, det):
    sk, V_sorted, cycle_set = compute_sk(ms, n, cycle, det)
    if not sk: return None
    skuc = sk | cycle_set
    results = []
    bound = 2**(n-1)
    for p in range(n):
        # For each 2-subset labeling of V_i (i≠p), check: does every b ∈ ∏ L_i have π_p(c) = b for some c ∈ skuc?
        labels_per_pos = []
        skip = False
        for i in range(n):
            if i == p: continue
            if len(V_sorted[i]) < 2: skip = True; break
            labels_per_pos.append(list(combinations(V_sorted[i], 2)))
        if skip: continue

        total = 1
        for lc in labels_per_pos: total *= len(lc)
        if total > 50000: continue

        # Projection of SK∪C to drop-p
        proj = set()
        for c in skuc:
            proj.add(tuple(c[i] for i in range(n) if i != p))

        best_covered = 0; best_label = None
        for label in iproduct(*labels_per_pos):
            B = set(iproduct(*label))
            covered = sum(1 for b in B if b in proj)
            if covered > best_covered:
                best_covered = covered; best_label = label
                if best_covered == 2**(n-1): break

        results.append({
            'p': p, 'cov': best_covered, 'B_size': 2**(n-1),
            '|proj|': len(proj),
        })
    return {
        '|SK|': len(sk), 'L': len(cycle_set),
        'results': results,
    }


def main():
    print("=" * 100)
    print("BINARY LIFT ⊆ SK∪C test: is every binary config in SK∪C under some labeling?")
    print("=" * 100)

    plan = [
        # L range from 2n+2 upward
        (5, [(2,2,2,3,3)], 14, 3, 15.0),
        (6, [(2,2,2,3,3,3), (2,2,3,3,3,3)], 16, 2, 25.0),
        (7, [(2,2,2,3,3,3,3)], 16, 1, 35.0),
        (8, [(2,2,2,3,3,3,3,3)], 18, 1, 50.0),
    ]

    for n, ms_list, L_max, max_cycles, tb in plan:
        bound = 2 ** (n - 1)
        print(f"\n=== n={n} bound={bound} ===")
        for ms in ms_list:
            cycles = enumerate_cycles(ms, n, L_min=2*n+2, L_max=L_max,
                                      time_budget=tb, max_cycles=max_cycles)
            for ci, (cycle, movers, det) in enumerate(cycles):
                r = test_binary_lift_in_skuc(n, ms, cycle, det)
                if r is None: continue
                print(f"\n ms={ms} L={r['L']} cycle#{ci} |SK|={r['|SK|']}")
                full_hits = 0
                for rec in r['results']:
                    fl = "★" if rec['cov'] == bound else " "
                    if rec['cov'] == bound: full_hits += 1
                    print(f"   p={rec['p']} best_bin_lift_cov={rec['cov']}/{bound} "
                          f"|π_p(SK∪C)|={rec['|proj|']}  {fl}")
                print(f"  # p where binary lift fully ⊆ SK∪C: {full_hits}/{n}")


if __name__ == "__main__":
    main()
