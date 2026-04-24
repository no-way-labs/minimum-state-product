#!/usr/bin/env python3
"""Structure of per-peel-step π_p drop.

At each peel step k, we remove sinks X_k ⊆ S_k. Each x ∈ X_k has
  π_p(x) ∈ π_p(S_k).
The drop π_p(S_k) → π_p(S_{k+1}) loses a value b iff
  every x ∈ π_p^{-1}(b) ∩ S_k was peeled, i.e., all lifts of b got removed.

We want: Σ_k Δπ_p(k) ≤ |π_p(S_0)| - 2^(n-1).

For the induction to work we need: each step's Δπ_p is "small" somehow.
Strategies:
  (A) Δπ_p ≤ # peeled configs (trivially).
  (B) Δπ_p ≤ # peeled configs with SINGLETON fiber in S_k.
  (C) Δπ_p = 0 unless ALL lifts of some b are peeled simultaneously.

Probe: for each k, for each p, report:
  - |X_k| = # peeled this step
  - Δπ_p(k)
  - # singleton-fiber configs in X_k under drop-p
  - correlation between Δπ_p and # singletons
"""
from itertools import product as iproduct, combinations
from collections import defaultdict, Counter
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


def peel_drop_analysis(ms, n, cycle, det):
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

    # Pre-peel fiber map: for each p, for each b, list of lifts
    def compute_fibers(S_set):
        fibers = [defaultdict(list) for _ in range(n)]
        for c in S_set:
            for p in range(n):
                b = tuple(c[i] for i in range(n) if i != p)
                fibers[p][b].append(c)
        return fibers

    remaining = set(non_good)
    step_records = []
    step = 0
    while True:
        sinks = {c for c in remaining if not any(t in remaining for t in adj.get(c, []))}
        if not sinks: break
        fibers = compute_fibers(remaining)
        # For each p: Δπ_p and # sinks with singleton fiber
        p_data = []
        for p in range(n):
            before_proj = {tuple(c[i] for i in range(n) if i != p) for c in remaining}
            after_proj = before_proj.copy()
            # A projection b survives iff some lift is not in sinks
            for s in sinks:
                b = tuple(s[i] for i in range(n) if i != p)
                # Check if all lifts of b are in sinks
                if all(l in sinks for l in fibers[p][b]):
                    after_proj.discard(b)
            drop = len(before_proj) - len(after_proj)
            # Count singleton-fiber sinks (= unique lift under drop-p)
            singleton_sinks = sum(1 for s in sinks
                                  if len(fibers[p][tuple(s[i] for i in range(n) if i != p)]) == 1)
            p_data.append({
                'drop': drop, 'before': len(before_proj),
                'sink_singletons': singleton_sinks,
            })
        step_records.append({
            'step': step, '|S|': len(remaining), '|sinks|': len(sinks),
            'p_data': p_data,
        })
        remaining -= sinks
        step += 1
    return step_records, len(remaining)


def main():
    print("=" * 100)
    print("PEEL DROP STRUCTURE: Δπ_p(k) vs # sinks with singleton fiber")
    print("=" * 100)
    cases = [
        (7, (2,2,2,3,3,3,3), 17, 35.0),
        (8, (2,2,2,3,3,3,3,3), 19, 50.0),
    ]
    for n, ms, L_max, tb in cases:
        bound = 2**(n-1)
        print(f"\n=== n={n} ms={ms} bound={bound} ===")
        cycles = enumerate_cycles_from(ms, n, L_min=2*n+2, L_max=L_max,
                                       time_budget=tb, max_cycles=1,
                                       start_config=tuple([0]*n))
        if not cycles: continue
        cycle, movers, det = cycles[0]
        print(f"  L={len(cycle)}")
        records, sk_size = peel_drop_analysis(ms, n, cycle, det)
        print(f"  |SK|={sk_size}")
        print(f"  step  |S|  |sinks|   " +
              "  ".join(f"Δπ{p}(sing)" for p in range(n)))
        for rec in records:
            parts = []
            for p, d in enumerate(rec['p_data']):
                parts.append(f"{d['drop']:2d}({d['sink_singletons']:2d})")
            print(f"  k={rec['step']:2d} {rec['|S|']:5d} {rec['|sinks|']:5d}    " +
                  " ".join(parts))


if __name__ == "__main__":
    main()
