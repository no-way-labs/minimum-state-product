#!/usr/bin/env python3
"""Minimum forced-SCC size: the core of the gap mechanism.

Previous probe showed SK = union of non-trivial forced SCCs + backward cone.
Gap dichotomy says |SK| ∈ {0} ∪ [2^(n-1), ∞).

If we can show:
  (a) min non-trivial SCC size ≥ f_1(n), AND
  (b) backward cone adds at least f_2(n),
with f_1(n) + f_2(n) ≥ 2^(n-1), we have the mechanism.

This probe extracts per-cycle:
  - All SCCs in F|_X (both trivial and non-trivial)
  - For each non-trivial SCC: its size, its "cone" (pre-images reaching it)
  - Partition SK into (SCC, cone-of-SCC) for each SCC

Goal: find f_1, f_2 and check if they cleanly sum to 2^(n-1).
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


def compute_sk_and_adj(ms, n, cycle, det):
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
    return remaining, adj, V_sorted


def tarjan_sccs(nodes, adj):
    import sys
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, len(nodes) * 3 + 1000))
    nodes_set = set(nodes)
    idx = [0]; stack = []; low = {}; ix = {}; on = {}; sccs = []
    def go(v):
        ix[v] = idx[0]; low[v] = idx[0]; idx[0] += 1
        stack.append(v); on[v] = True
        for w in adj.get(v, []):
            if w not in nodes_set: continue
            if w not in ix:
                go(w); low[v] = min(low[v], low[w])
            elif on.get(w, False):
                low[v] = min(low[v], ix[w])
        if low[v] == ix[v]:
            comp = []
            while True:
                w = stack.pop(); on[w] = False; comp.append(w)
                if w == v: break
            sccs.append(comp)
    for v in nodes:
        if v not in ix: go(v)
    sys.setrecursionlimit(old)
    return sccs


def analyze_sk_structure(sk, adj, n):
    """For a non-empty SK, decompose into SCCs + backward cones."""
    if not sk: return None
    sk_list = list(sk)
    sccs = tarjan_sccs(sk_list, adj)
    # Identify non-trivial: size ≥ 2 OR size 1 with self-loop
    nontrivial_sccs = []
    trivial_nodes = []
    for s in sccs:
        if len(s) >= 2:
            nontrivial_sccs.append(set(s))
        else:
            v = s[0]
            if v in adj.get(v, []):
                nontrivial_sccs.append(set(s))
            else:
                trivial_nodes.append(v)

    if not nontrivial_sccs:
        # shouldn't happen for non-empty SK
        return {'num_nontrivial': 0, 'scc_sizes': [],
                'cone_sizes': [], 'isolated_singletons': len(trivial_nodes)}

    # For each non-trivial SCC, find its "cone" = SK configs that reach THIS SCC
    #   (but not other SCCs earlier in any BFS ordering)
    # Simpler: for each trivial node, find which SCC(s) it reaches in SK.
    # Assign it to the "closest" (just pick first found reachable) for now.
    cone_assignment = defaultdict(list)  # scc_idx → list of trivial nodes

    for t in trivial_nodes:
        # BFS from t within SK, find first SCC hit
        visited = {t}; q = [t]
        hit = None
        while q and hit is None:
            v = q.pop(0)
            for w in adj.get(v, []):
                if w not in sk: continue
                # check if w is in any non-trivial SCC
                for si, scc_set in enumerate(nontrivial_sccs):
                    if w in scc_set:
                        hit = si; break
                if hit is not None: break
                if w not in visited:
                    visited.add(w); q.append(w)
        if hit is None:
            cone_assignment['orphan'].append(t)
        else:
            cone_assignment[hit].append(t)

    # SCC + cone sizes per SCC
    decomp = []
    for si, scc_set in enumerate(nontrivial_sccs):
        cone_sz = len(cone_assignment.get(si, []))
        decomp.append({
            'scc_size': len(scc_set),
            'cone_size': cone_sz,
            'total': len(scc_set) + cone_sz
        })
    orphans = len(cone_assignment.get('orphan', []))
    return {
        'num_nontrivial': len(nontrivial_sccs),
        'decomp': decomp,
        'orphans': orphans,
        'total_sk': len(sk)
    }


def main():
    print("=" * 100)
    print("MINIMUM FORCED-SCC SIZE: the core of the gap mechanism")
    print("=" * 100)

    plan = [
        (5, [(2,2,2,2,3), (2,2,2,3,3), (2,2,2,3,4), (2,2,2,4,4),
             (2,2,3,3,3), (2,2,3,3,4), (2,3,3,3,3), (3,3,3,3,3)], 17, 15, 20.0),
        (6, [(2,2,2,3,3,3), (2,2,2,3,3,4), (2,2,3,3,3,3),
             (2,2,3,3,3,4), (3,3,3,3,3,3)], 17, 8, 40.0),
        (7, [(2,2,2,3,3,3,3), (2,2,2,3,3,3,4)], 17, 4, 45.0),
        (8, [(2,2,2,3,3,3,3,3)], 19, 3, 60.0),
    ]

    # Collect: for each n, list of (|SK|, num_SCC, scc_sizes, cone_sizes)
    by_n = defaultdict(list)

    for n, ms_list, L_max, max_cycles, tb in plan:
        bound = 2 ** (n - 1)
        print(f"\n=== n={n}  bound=2^{n-1}={bound}  max_cycles/ms={max_cycles} ===")
        for ms in ms_list:
            prod = math.prod(ms)
            cycles = enumerate_cycles(ms, n, L_min=2*n+2, L_max=L_max,
                                      time_budget=tb, max_cycles=max_cycles)
            if not cycles: continue
            for cycle, movers, det in cycles:
                sk, adj, V_sorted = compute_sk_and_adj(ms, n, cycle, det)
                if not sk: continue
                a = analyze_sk_structure(sk, adj, n)
                a['n'] = n; a['ms'] = ms; a['prod'] = prod; a['L'] = len(cycle)
                by_n[n].append(a)

    # Analyze min SCC sizes
    print("\n" + "=" * 100)
    print("MIN SCC SIZE AND TOTAL DECOMPOSITION STATS")
    print("=" * 100)
    for n in sorted(by_n):
        recs = by_n[n]
        bound = 2 ** (n - 1)
        # min SCC size (over all SCCs across all (ms, cycle))
        all_scc_sizes = []
        all_cone_sizes = []
        all_scc_plus_cone = []
        cycle_min_scc = []   # min SCC size per cycle
        for a in recs:
            for d in a['decomp']:
                all_scc_sizes.append(d['scc_size'])
                all_cone_sizes.append(d['cone_size'])
                all_scc_plus_cone.append(d['total'])
            if a['decomp']:
                cycle_min_scc.append(min(d['scc_size'] for d in a['decomp']))

        min_any_scc = min(all_scc_sizes) if all_scc_sizes else -1
        min_cycle_min_scc = min(cycle_min_scc) if cycle_min_scc else -1
        sk_sizes = [a['total_sk'] for a in recs]
        min_sk = min(sk_sizes) if sk_sizes else -1

        print(f"\n  n={n}  bound=2^{n-1}={bound}  #cycles_with_nonempty_SK={len(recs)}")
        print(f"    min |SK| overall                    = {min_sk}")
        print(f"    min non-trivial SCC size (over ALL) = {min_any_scc}")
        print(f"    min cycle's smallest SCC size       = {min_cycle_min_scc}")
        print(f"    num_SCC distribution                = {dict((k, sum(1 for a in recs if a['num_nontrivial']==k)) for k in sorted(set(a['num_nontrivial'] for a in recs)))}")

        # Key question: is min_any_scc >= 2^(n-1)?
        if min_any_scc >= bound:
            print(f"    ✓ min SCC ≥ 2^{n-1}: SCC ALONE clears the bound.")
        else:
            print(f"    ✗ min SCC = {min_any_scc} < 2^{n-1} = {bound}: SCC alone insufficient.")
            # Find examples where SCC + cone < bound? (would break gap)
            close_calls = sorted([(d['scc_size'], d['cone_size'], d['total'])
                                  for a in recs for d in a['decomp']],
                                 key=lambda x: x[2])[:5]
            print(f"    smallest (SCC, cone, total) tuples: {close_calls}")

        # Cycle-level: min (SCC + its cone) across all (cycle, SCC) pairs
        min_scc_plus_cone = min(all_scc_plus_cone) if all_scc_plus_cone else -1
        print(f"    min (SCC + its cone) per (cycle, SCC) = {min_scc_plus_cone}")
        if min_scc_plus_cone >= bound:
            print(f"    ✓ min (SCC + cone) ≥ 2^{n-1}: single SCC-component suffices.")


if __name__ == "__main__":
    main()
