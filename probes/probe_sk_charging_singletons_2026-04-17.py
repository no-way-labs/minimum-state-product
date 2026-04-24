#!/usr/bin/env python3
"""Charging scheme: singleton-fiber sinks x → forced edge target in C (or earlier peel layer).

A singleton-fiber sink x at peel step k (drop-position p) means:
  - x ∈ S_k
  - no y ∈ adj(x) ∩ S_k (sink)
  - no y ∈ S_k with y[i]=x[i] ∀i≠p, y ≠ x (singleton fiber)

When peeled, x causes π_p(S) to lose one value. We want:
  Σ_k σ_p(k) ≤ L · const (or ≤ L).

Mechanism hypothesis:
  Each x has at least one forced out-edge to some target t.
  Since x is a sink: t ∈ C ∪ S_{<k} (peeled earlier).
  If t ∈ C: charge σ_p(x) to t.
  If t ∈ S_j, j<k: charge recursively — each singleton-sink at layer k is
    ultimately charged to a config in C.

Question: is the charging injective (or bounded-multiplicity)?

Probe:
  for each peel step k, for each sink x, for each p where x has singleton drop-p fiber:
    record list of forced targets of x in C vs in S_{<k}.
    count: how many singleton-sinks share a charge target in C?
"""
from itertools import product as iproduct
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


def charging_analysis(ms, n, cycle, det):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n): V[i].add(c[i])
    V_sorted = [sorted(V[i]) for i in range(n)]
    all_configs = list(iproduct(*V_sorted))
    cycle_set = set(cycle)
    non_good = [c for c in all_configs if c not in cycle_set]
    ng_set = set(non_good)
    # forced-move targets (include moves into C too)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    all_targets = defaultdict(list)  # any forced target (in or out of ng_set)
    adj_ng = defaultdict(list)       # forced targets in ng_set only (peel graph)
    for c in non_good:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in move_entries:
                nc = list(c); nc[p] = move_entries[key]; nc = tuple(nc)
                all_targets[c].append(nc)
                if nc in ng_set:
                    adj_ng[c].append(nc)

    remaining = set(non_good)
    peel_layer = {}  # x -> k
    step = 0
    layers = []
    while True:
        sinks = {c for c in remaining if not any(t in remaining for t in adj_ng.get(c, []))}
        if not sinks: break
        for s in sinks: peel_layer[s] = step
        layers.append(sinks)
        remaining -= sinks
        step += 1

    # For each step k, each p, each sink x in X_k with singleton drop-p fiber,
    # record charge targets (in C or in earlier layer).
    reports_per_p = {p: {'total_singletons': 0, 'charges_to_C': 0,
                         'charges_to_earlier': 0,
                         'multiplicity_in_C': Counter()} for p in range(n)}
    total_L = len(cycle)
    S_k = set(non_good)
    for k, X_k in enumerate(layers):
        for p in range(n):
            # compute fiber sizes in S_k
            fiber = defaultdict(list)
            for c in S_k:
                b = tuple(c[i] for i in range(n) if i != p)
                fiber[b].append(c)
            for x in X_k:
                b = tuple(x[i] for i in range(n) if i != p)
                if len(fiber[b]) != 1: continue
                reports_per_p[p]['total_singletons'] += 1
                # find charge targets: forced targets that are in C or earlier layer
                targets_C = [t for t in all_targets.get(x, []) if t in cycle_set]
                targets_earlier = [t for t in all_targets.get(x, [])
                                   if t in peel_layer and peel_layer[t] < k]
                if targets_C:
                    reports_per_p[p]['charges_to_C'] += 1
                    # pick canonical target
                    reports_per_p[p]['multiplicity_in_C'][targets_C[0]] += 1
                elif targets_earlier:
                    reports_per_p[p]['charges_to_earlier'] += 1
        S_k -= X_k

    return reports_per_p, total_L


def main():
    print("=" * 100)
    print("CHARGING SCHEME: singleton-fiber sinks → C or earlier peel layer")
    print("=" * 100)
    cases = [
        (7, (2,2,2,3,3,3,3), 17, 35.0),
        (8, (2,2,2,3,3,3,3,3), 19, 50.0),
        (9, (2,2,3,2,3,3,3,3,3), 22, 60.0),
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
        reports, L = charging_analysis(ms, n, cycle, det)
        for p in range(n):
            r = reports[p]
            if r['total_singletons'] == 0: continue
            max_mult = max(r['multiplicity_in_C'].values()) if r['multiplicity_in_C'] else 0
            distinct_C = len(r['multiplicity_in_C'])
            print(f"  p={p}: σ_p={r['total_singletons']:3d}  "
                  f"→C={r['charges_to_C']:3d}  →earlier={r['charges_to_earlier']:3d}  "
                  f"distinct_C={distinct_C:3d}/{L}  max_mult_C={max_mult}")


if __name__ == "__main__":
    main()
