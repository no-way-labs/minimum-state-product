#!/usr/bin/env python3
"""Recursion hypothesis: SCCs of SK_n are lifted SK_{n-1} slices.

At n=8, SCC sizes are [142, 142, 18]. 142 = |SK_{n=7}|. Coincidence? Test:
  - For each position p at which |V_p|=2, slice SK_n by fixing c[p]=v.
    Does slice = one of the SCCs?
  - Is the slice (relabeled to an (n-1)-ring by collapsing position p)
    itself an SK of some cycle in n-1?

If YES: recursion gives |SK_n| ≥ 2 · |SK_{n-1}| ≥ 2 · 2^(n-2) = 2^(n-1). Done.

If NO: find what other structure relates SCCs to (n-1) objects.

Also: test (i) injection directly via Hamming-distance-1 cloud restricted to
SK — see if it has cardinality ≥ 2^(n-1).
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time
import math
import sys
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
    return sccs


def recursion_probe(n, ms, cycle, det, bound):
    sk, adj, V_sorted = compute_sk_and_adj(ms, n, cycle, det)
    if not sk: return None

    sccs = tarjan_sccs(list(sk), adj)
    nt_sccs = [set(s) for s in sccs if len(s) >= 2 or s[0] in adj.get(s[0], [])]
    nt_sccs.sort(key=lambda s: -len(s))
    nt_sizes = [len(s) for s in nt_sccs]

    # Test recursion: slice by fixing c[p]=v for each position p
    slice_results = []
    for p in range(n):
        V_p = sorted(V_sorted[p])
        for v in V_p:
            slice_ = {c for c in sk if c[p] == v}
            slice_size = len(slice_)
            # Is this slice equal to one of the SCCs?
            scc_match = None
            for i, S in enumerate(nt_sccs):
                if S == slice_:
                    scc_match = (i, len(S)); break
            slice_results.append((p, v, slice_size, scc_match))

    # Test (i): Hamming-1 cloud cardinality
    cycle_set = set(cycle)
    hamming1_cloud = set()
    for c in cycle_set:
        for p in range(n):
            V_p = sorted(V_sorted[p])
            for v in V_p:
                if v == c[p]: continue
                nc = list(c); nc[p] = v; nc = tuple(nc)
                if nc not in cycle_set:
                    hamming1_cloud.add(nc)
    hamming1_in_sk = hamming1_cloud & sk
    # Deep cloud: up to Hamming distance 2
    ham2_cloud = set(hamming1_cloud)
    for c in hamming1_cloud:
        for p in range(n):
            V_p = sorted(V_sorted[p])
            for v in V_p:
                if v == c[p]: continue
                nc = list(c); nc[p] = v; nc = tuple(nc)
                if nc not in cycle_set:
                    ham2_cloud.add(nc)
    ham2_in_sk = ham2_cloud & sk

    return {
        'sk_size': len(sk), 'bound': bound,
        'scc_sizes': nt_sizes,
        'slice_results': slice_results,
        'ham1_total': len(hamming1_cloud),
        'ham1_in_sk': len(hamming1_in_sk),
        'ham2_total': len(ham2_cloud),
        'ham2_in_sk': len(ham2_in_sk),
    }


def main():
    print("=" * 100)
    print("RECURSION HYPOTHESIS: fixed-position slices and SCC identity")
    print("=" * 100)

    plan = [
        (6, [(2,2,2,3,3,3)], 17, 3, 30.0),
        (7, [(2,2,2,3,3,3,3)], 17, 2, 40.0),
        (8, [(2,2,2,3,3,3,3,3)], 19, 1, 60.0),
    ]

    for n, ms_list, L_max, max_cycles, tb in plan:
        bound = 2 ** (n - 1)
        print(f"\n=== n={n}  bound=2^{n-1}={bound} ===")
        for ms in ms_list:
            cycles = enumerate_cycles(ms, n, L_min=2*n+2, L_max=L_max,
                                      time_budget=tb, max_cycles=max_cycles)
            for ci, (cycle, movers, det) in enumerate(cycles):
                r = recursion_probe(n, ms, cycle, det, bound)
                if r is None: continue
                print(f"\n  ms={ms} L={len(cycle)} cycle#{ci}")
                print(f"    |SK|={r['sk_size']}  SCC_sizes={r['scc_sizes']}")
                print(f"    Hamming-1 cloud: total={r['ham1_total']}  in_SK={r['ham1_in_sk']}"
                      f"  (≥{bound}? {'YES' if r['ham1_in_sk']>=bound else 'NO'})")
                print(f"    Hamming-2 cloud: total={r['ham2_total']}  in_SK={r['ham2_in_sk']}"
                      f"  (≥{bound}? {'YES' if r['ham2_in_sk']>=bound else 'NO'})")
                print(f"    Slice-by-position results (p, val, slice_size, scc_match):")
                for p, v, ss, sm in r['slice_results']:
                    matched = f"=SCC[{sm[0]}](sz={sm[1]})" if sm else ""
                    print(f"      p={p} v={v}  slice_size={ss}  {matched}")


if __name__ == "__main__":
    main()
