#!/usr/bin/env python3
"""What relates the multiple SCCs at n=7,8 to each other?

Hypotheses:
  S1: SCCs are related by ring-rotation (cyclic shift of positions)
  S2: SCCs are related by an involution (bit-flip at a specific binary position)
  S3: SCCs are related by cycle-translation (applying good cycle once)
  S4: SCCs correspond to "residues mod K" for some K (e.g., drop-p projection cosets)
  S5: SCCs are distinguished by value at a fixed position

For each n=7,8 case, extract SCCs and check:
  - Are they isomorphic (same size, edge counts)?
  - Does rotation send SCC_i to SCC_j?
  - Does single-flip send SCC_i to SCC_j?
  - Is there a coset structure in ∏V?
"""
from itertools import product as iproduct, permutations
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


def analyze_scc_relations(n, sk, adj, V_sorted, ms):
    sccs = tarjan_sccs(list(sk), adj)
    nt_sccs = []
    for s in sccs:
        if len(s) >= 2 or s[0] in adj.get(s[0], []):
            nt_sccs.append(set(s))
    if len(nt_sccs) < 2:
        return None

    # Sort by size
    nt_sccs.sort(key=lambda s: (-len(s), sorted(s)[0]))

    info = {'num_sccs': len(nt_sccs),
            'sizes': [len(s) for s in nt_sccs]}

    # S1: rotation — ring-shift config by k
    rotation_matches = []
    for k in range(1, n):
        for i, A in enumerate(nt_sccs):
            rotated_A = {tuple(c[(pos - k) % n] for pos in range(n)) for c in A}
            for j, B in enumerate(nt_sccs):
                if i == j: continue
                if rotated_A == B:
                    rotation_matches.append((k, i, j))
                    break
    info['rotation_matches'] = rotation_matches[:5]

    # S2: single-bit flip at binary position
    binary_pos = [p for p, m in enumerate(ms) if m == 2]
    flip_matches = []
    for p in binary_pos:
        V_p = sorted(V_sorted[p])
        if len(V_p) != 2: continue
        v0, v1 = V_p
        for i, A in enumerate(nt_sccs):
            flipped_A = set()
            for c in A:
                tc = list(c); tc[p] = v1 if c[p] == v0 else v0
                flipped_A.add(tuple(tc))
            for j, B in enumerate(nt_sccs):
                if i == j: continue
                if flipped_A == B:
                    flip_matches.append((p, i, j))
                    break
    info['flip_matches'] = flip_matches[:5]

    # S3: distinguish by value at fixed positions
    # For each position p, compute value-distribution of each SCC
    distinguishing_positions = []
    for p in range(n):
        # distribution of c[p] in each SCC
        distribs = []
        for A in nt_sccs:
            ctr = Counter(c[p] for c in A)
            distribs.append(tuple(sorted(ctr.items())))
        # distinct?
        if len(set(distribs)) == len(nt_sccs):
            distinguishing_positions.append((p, distribs))
    info['distinguishing_positions'] = distinguishing_positions[:3]

    # S4: Value at fixed position — do different SCCs exhaust different values?
    # For each position, check if each SCC has its own value at that position
    value_partitions = []
    for p in range(n):
        # Does each SCC have a single value at position p?
        scc_values = []
        for A in nt_sccs:
            vs = set(c[p] for c in A)
            scc_values.append(vs)
        # Are they disjoint?
        disjoint = all(scc_values[i].isdisjoint(scc_values[j])
                       for i in range(len(scc_values))
                       for j in range(i+1, len(scc_values)))
        if disjoint:
            value_partitions.append((p, scc_values))
    info['value_partitions'] = value_partitions[:3]

    # S5: Union of SCCs — what's its structure? Is it closed under any symmetry?
    union_SK = set()
    for s in nt_sccs: union_SK |= s
    info['union_size'] = len(union_SK)

    return info


def main():
    print("=" * 100)
    print("SCC SYMMETRY / RELATIONS: what relates multiple SCCs at n=7,8?")
    print("=" * 100)

    plan = [
        (7, [(2,2,2,3,3,3,3), (2,2,2,3,3,3,4), (2,2,3,3,3,3,3)], 17, 3, 45.0),
        (8, [(2,2,2,3,3,3,3,3), (2,2,2,3,3,3,3,4)], 19, 2, 75.0),
    ]

    for n, ms_list, L_max, max_cycles, tb in plan:
        bound = 2 ** (n - 1)
        print(f"\n=== n={n}  bound=2^{n-1}={bound} ===")
        for ms in ms_list:
            cycles = enumerate_cycles(ms, n, L_min=2*n+2, L_max=L_max,
                                      time_budget=tb, max_cycles=max_cycles)
            for ci, (cycle, movers, det) in enumerate(cycles):
                sk, adj, V_sorted = compute_sk_and_adj(ms, n, cycle, det)
                if not sk: continue
                info = analyze_scc_relations(n, sk, adj, V_sorted, ms)
                if info is None: continue
                print(f"\n  ms={ms}  L={len(cycle)}  cycle#{ci}")
                print(f"    num_SCCs   = {info['num_sccs']}")
                print(f"    SCC_sizes  = {info['sizes']}")
                print(f"    |SK|       = {len(sk)}  (sum_SCC = {sum(info['sizes'])})")
                print(f"    rotation matches   : {info['rotation_matches']}")
                print(f"    single-flip matches: {info['flip_matches']}")
                print(f"    positions where SCCs have DISJOINT value sets:")
                for p, vals in info['value_partitions']:
                    vl = [sorted(v) for v in vals]
                    print(f"      p={p}  SCC values: {vl}")
                print(f"    positions where value-distribution DISTINGUISHES SCCs:")
                for p, ds in info['distinguishing_positions'][:2]:
                    print(f"      p={p}  distrib: {ds}")


if __name__ == "__main__":
    main()
