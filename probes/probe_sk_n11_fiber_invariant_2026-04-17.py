#!/usr/bin/env python3
"""Combined: (a) find n=11 cycles with smarter DFS (breadth over start configs),
(b) Test fiber-invariant claim at BINARY p: during peel at binary p, the count of
singleton-fibers behaves structurally.

Key identity at binary p: |S| = #1fib + 2·#2fib, so |π_p(S)| = #1fib + #2fib.
Then 2|π_p(S)| - |S| = #1fib = # singleton-fiber configs.
When sinks X_k peeled, drop(π_p) = # of fibers fully covered = #{b: all lifts in X_k}.

Hypothesis: at binary p, drop(π_p, k) ≤ #{x ∈ X_k : 1-fiber} / 2  (pairing argument?)
OR some other bounded-relationship.

Also test: does π_p(SK) ≥ 2^(n-1) ALWAYS at binary p when |V_p|=2 AND some V_j≥3?
(If yes, proves strategy A at binary p.)
"""
from itertools import product as iproduct
from collections import defaultdict
import time, sys
sys.setrecursionlimit(100000)


def enumerate_cycles_multi_start(ms, n, L_min, L_max, time_budget, max_cycles, starts):
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
    for s in starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget: break
        dfs(s, s, {}, [s], [])
    return found


def build_peel(ms, n, cycle, det):
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

    remaining = set(non_good)
    layers = []
    while True:
        sinks = {c for c in remaining if not any(t in remaining for t in adj_ng.get(c, []))}
        if not sinks: break
        layers.append(sinks)
        remaining -= sinks
    return {'ng_set': ng_set, 'cycle_set': cycle_set, 'V_sorted': V_sorted,
            'layers': layers, 'SK': remaining}


def binary_fiber_invariant(data, n):
    """At binary p, track #1fib(S_k) and #2fib(S_k), compare drops."""
    layers = data['layers']; SK = data['SK']; ng_set = data['ng_set']
    V_sorted = data['V_sorted']
    binary_p = [p for p in range(n) if len(V_sorted[p]) == 2]
    S_k = set(ng_set)
    traj = {p: [] for p in binary_p}
    for k in range(len(layers) + 1):
        for p in binary_p:
            fiber = defaultdict(list)
            for c in S_k:
                b = tuple(c[i] for i in range(n) if i != p)
                fiber[b].append(c)
            n1 = sum(1 for v in fiber.values() if len(v) == 1)
            n2 = sum(1 for v in fiber.values() if len(v) == 2)
            pi = n1 + n2
            traj[p].append({'|S|': len(S_k), 'pi': pi, 'n1': n1, 'n2': n2,
                            'drop_singles_into_sinks': None,
                            'drop_doubles_both_into_sinks': None})
            if k < len(layers):
                X_k = layers[k]
                singles_peeled = 0
                doubles_fully_peeled = 0
                for b, lifts in fiber.items():
                    if len(lifts) == 1:
                        if lifts[0] in X_k: singles_peeled += 1
                    elif len(lifts) == 2:
                        if lifts[0] in X_k and lifts[1] in X_k: doubles_fully_peeled += 1
                traj[p][-1]['drop_singles_into_sinks'] = singles_peeled
                traj[p][-1]['drop_doubles_both_into_sinks'] = doubles_fully_peeled
        if k < len(layers): S_k -= layers[k]
    return traj, binary_p


def main():
    print("=" * 100)
    print("n=11 FIBER INVARIANT + smarter cycle seeding")
    print("=" * 100)
    # Approach: try multiple short starts in various corners.
    ms_list_11 = [
        (2,2,3,2,3,3,3,3,3,3,3),
        (2,2,2,3,3,3,3,3,3,3,3),
    ]
    for ms in ms_list_11:
        n = 11; bound = 2**(n-1); L_min = 2*n + 2
        print(f"\n=== n=11 ms={ms} bound={bound} L_min={L_min} ===")
        # Start from diverse corners
        starts = [tuple([0]*n)]
        # also try corners with one binary flipped
        for i in range(n):
            if ms[i] == 2:
                c = [0]*n; c[i] = 1; starts.append(tuple(c))
        # random medium starts
        starts.append(tuple([0,1,0,1,0,1,0,1,0,1,0][:n]))
        t0 = time.time()
        cycles = enumerate_cycles_multi_start(ms, n, L_min=L_min, L_max=L_min+1,
                                              time_budget=240.0, max_cycles=1,
                                              starts=starts)
        print(f"  DFS ({time.time()-t0:.0f}s): {len(cycles)} cycles found")
        if not cycles: continue
        cycle, movers, det = cycles[0]
        print(f"  L={len(cycle)}")
        data = build_peel(ms, n, cycle, det)
        print(f"  |VC_NG|={len(data['ng_set'])} |SK|={len(data['SK'])}")
        # Compute (A)/(F) for this cycle
        sk = data['SK']; cset = data['cycle_set']
        skuc = sk | cset
        F_sizes, A_sizes = [], []
        for p in range(n):
            F_sizes.append(len({tuple(c[i] for i in range(n) if i != p) for c in skuc}))
            A_sizes.append(len({tuple(c[i] for i in range(n) if i != p) for c in sk}))
        print(f"  (F) |π_p(SK∪C)| min={min(F_sizes)} max={max(F_sizes)} vs {bound}")
        print(f"  (A) |π_p(SK)|   min={min(A_sizes)} max={max(A_sizes)} vs {bound}")

        # Fiber invariant at binary p
        traj, binary_p = binary_fiber_invariant(data, n)
        print(f"  binary positions: {binary_p}")
        for p in binary_p[:2]:
            t = traj[p]
            print(f"  p={p}: traj pi series: {[r['pi'] for r in t]}")
            print(f"  p={p}: singles_peeled_per_step: {[r['drop_singles_into_sinks'] for r in t[:-1]]}")
            print(f"  p={p}: doubles_fully_peeled_per_step: {[r['drop_doubles_both_into_sinks'] for r in t[:-1]]}")

    # Also n=7,8,9 for reference
    print("\n" + "=" * 100)
    print("REFERENCE: binary fiber invariant at n=7,8,9")
    print("=" * 100)
    ref_cases = [
        (7, (2,2,2,3,3,3,3), 17, 25.0),
        (8, (2,2,2,3,3,3,3,3), 19, 40.0),
        (9, (2,2,3,2,3,3,3,3,3), 22, 50.0),
    ]
    for n, ms, L_max, tb in ref_cases:
        bound = 2**(n-1)
        starts = [tuple([0]*n)]
        cycles = enumerate_cycles_multi_start(ms, n, L_min=2*n+2, L_max=L_max,
                                              time_budget=tb, max_cycles=1, starts=starts)
        if not cycles: continue
        cycle, movers, det = cycles[0]
        data = build_peel(ms, n, cycle, det)
        traj, binary_p = binary_fiber_invariant(data, n)
        print(f"\n  n={n} L={len(cycle)} |SK|={len(data['SK'])} bound={bound}")
        for p in binary_p[:1]:
            t = traj[p]
            pi_final = t[-1]['pi']
            total_singles = sum(r['drop_singles_into_sinks'] or 0 for r in t[:-1])
            total_doubles = sum(r['drop_doubles_both_into_sinks'] or 0 for r in t[:-1])
            # Total drop in pi: pi[0] - pi[-1] = total_singles + total_doubles
            drops = t[0]['pi'] - t[-1]['pi']
            print(f"  p={p} (binary): pi start={t[0]['pi']} end={pi_final}  "
                  f"drops={drops} = singles({total_singles}) + doubles({total_doubles})")
            print(f"       |SK|/2 = {len(data['SK'])//2} vs bound {bound}")


if __name__ == "__main__":
    main()
