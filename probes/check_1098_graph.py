#!/usr/bin/env python3
"""Check structure of the FULL 1098 TP-preserving boundary-changing 6-tuple graph.

Question: if we handle ALL 1098 edges (not just the 617 CΦ edges),
does the graph have a manageable condensation structure that avoids
needing Φ_full entirely?
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import build_system
from collections import defaultdict, deque

def analyze_tp_graph(n):
    ms, fs = build_system(n)
    N = 1
    for m in ms: N *= m

    def idx_to_config(idx):
        c = []
        for m in reversed(ms):
            c.append(idx % m); idx //= m
        return tuple(reversed(c))
    def config_to_idx(c):
        idx = 0
        for j in range(n): idx = idx * ms[j] + c[j]
        return idx
    def move(c, pos):
        L = c[(pos-1)%n]; S = c[pos]; R = c[(pos+1)%n]
        c2 = list(c); c2[pos] = fs[pos](L, S, R); return tuple(c2)
    def fc(c): return sum(1 for j in range(n) if c[j] != c[(j+1)%n])
    def tp(c):
        e = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
        i21 = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n]==1)
        w = sum(j for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
        return (e, i21, w)
    def boundary6(c): return ((((c[0]*3+c[1])*3+c[2])*3+c[n-3])*3+c[n-2])*2+c[n-1]

    # Build bad configs + TP-preserving adjacency
    all_configs = [idx_to_config(i) for i in range(N)]
    bad_set = set()
    for i in range(N):
        if fc(all_configs[i]) > 0:
            bad_set.add(i)

    # Collect ALL TP-preserving boundary-CHANGING 6-tuple edges
    tp_6tuple_edges = set()
    for i in bad_set:
        c = all_configs[i]; t = tp(c)
        for p in range(n):
            c2 = move(c, p)
            if c2 == c: continue
            j = config_to_idx(c2)
            if j in bad_set and tp(c2) == t:
                b1, b2 = boundary6(c), boundary6(c2)
                if b1 != b2:
                    tp_6tuple_edges.add((b1, b2))

    print(f"\nn={n}: {len(tp_6tuple_edges)} TP-preserving boundary-changing 6-tuple edges")

    # Build adjacency
    adj = defaultdict(set)
    nodes = set()
    for a, b in tp_6tuple_edges:
        adj[a].add(b); nodes.add(a); nodes.add(b)
    print(f"  Nodes: {len(nodes)}")

    # Tarjan's SCC
    index_counter = [0]; stack = []; lowlink = {}; index = {}; on_stack = set(); sccs = []
    def strongconnect(v):
        index[v] = index_counter[0]; lowlink[v] = index_counter[0]
        index_counter[0] += 1; stack.append(v); on_stack.add(v)
        for w in adj.get(v, set()):
            if w not in index:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], index[w])
        if lowlink[v] == index[v]:
            scc = []
            while True:
                w = stack.pop(); on_stack.discard(w); scc.append(w)
                if w == v: break
            sccs.append(scc)
    sys.setrecursionlimit(10000)
    for v in nodes:
        if v not in index: strongconnect(v)

    nontrivial = [s for s in sccs if len(s) > 1]
    print(f"  Non-trivial SCCs: {len(nontrivial)}")
    for scc in nontrivial:
        print(f"    SCC size {len(scc)}: {sorted(scc)}")
        # Check internal edges
        scc_set = set(scc)
        internal_edges = [(a,b) for a in scc for b in adj[a] if b in scc_set]
        print(f"    Internal edges: {len(internal_edges)}")

    # Compute condensation DAG rank
    scc_id = {}
    for i, scc in enumerate(sccs):
        for v in scc: scc_id[v] = i
    cond_adj = defaultdict(set)
    for a, b in tp_6tuple_edges:
        si, sj = scc_id[a], scc_id[b]
        if si != sj: cond_adj[si].add(sj)

    # DAG rank via topological order
    cond_rank = {}
    def compute_rank(v):
        if v in cond_rank: return cond_rank[v]
        cond_rank[v] = 0  # prevent recursion
        if cond_adj[v]:
            cond_rank[v] = max(compute_rank(w) + 1 for w in cond_adj[v])
        return cond_rank[v]
    for i in range(len(sccs)):
        compute_rank(i)
    max_rank = max(cond_rank.values()) if cond_rank else 0
    print(f"  Condensation DAG max rank: {max_rank}")

    # For nontrivial SCCs, check if fc or some simple measure handles the cycle
    if nontrivial:
        # Also compute Φ_full to compare
        phi_full = {i: fc(all_configs[i]) for i in bad_set}
        tp_adj = {}
        for i in bad_set: tp_adj[i] = []
        for i in bad_set:
            c = all_configs[i]; t = tp(c)
            for p in range(n):
                c2 = move(c, p)
                if c2 == c: continue
                j = config_to_idx(c2)
                if j in bad_set and tp(c2) == t:
                    tp_adj[i].append(j)
        tp_rev = {i: [] for i in bad_set}
        for i in bad_set:
            for j in tp_adj[i]: tp_rev[j].append(i)
        changed = True
        while changed:
            changed = False
            for j in bad_set:
                for i in tp_rev[j]:
                    if phi_full[j] > phi_full[i]:
                        phi_full[i] = phi_full[j]; changed = True

        # Collect CΦ edges (for comparison)
        future_fc = {i: fc(all_configs[i]) for i in bad_set}
        all_adj = {i: [] for i in bad_set}
        for i in bad_set:
            c = all_configs[i]
            for p in range(n):
                c2 = move(c, p)
                if c2 == c: continue
                j = config_to_idx(c2)
                if j in bad_set: all_adj[i].append(j)
        all_rev = {i: [] for i in bad_set}
        for i in bad_set:
            for j in all_adj[i]: all_rev[j].append(i)
        changed = True
        while changed:
            changed = False
            for j in bad_set:
                for i in all_rev[j]:
                    if future_fc[j] > future_fc[i]:
                        future_fc[i] = future_fc[j]; changed = True

        cphi_edges = set()
        tp_only_edges = set()  # TP-preserving but NOT CΦ
        for i in bad_set:
            c = all_configs[i]; t = tp(c)
            for j in tp_adj[i]:
                c2 = all_configs[j]
                b1, b2 = boundary6(c), boundary6(c2)
                if b1 != b2:
                    if future_fc[j] == future_fc[i] and phi_full[j] == phi_full[i]:
                        cphi_edges.add((b1, b2))
                    else:
                        tp_only_edges.add((b1, b2))

        print(f"\n  CΦ edges (617 expected): {len(cphi_edges)}")
        print(f"  TP-only edges (481 expected): {len(tp_only_edges)}")

        # Check: are the 481 TP-only edges all in the condensation-rank-dropping set?
        tp_only_drops_rank = 0
        tp_only_same_rank = 0
        for a, b in tp_only_edges:
            if scc_id[a] != scc_id[b]:
                tp_only_drops_rank += 1
            else:
                tp_only_same_rank += 1
        print(f"  TP-only edges that drop condensation rank (1098-graph): {tp_only_drops_rank}")
        print(f"  TP-only edges WITHIN an SCC (1098-graph): {tp_only_same_rank}")

        # For nontrivial SCCs in 1098-graph, check if ALL internal edges have fc behavior
        for scc in nontrivial:
            scc_set = set(scc)
            print(f"\n  Analyzing SCC {sorted(scc)}:")
            # Collect all config-level edges that realize these 6-tuple edges
            for a in scc:
                for b in adj[a]:
                    if b in scc_set:
                        # Check fc behavior on all configs realizing this edge
                        fc_dirs = set()
                        count = 0
                        for i in bad_set:
                            c = all_configs[i]
                            if boundary6(c) != a: continue
                            t = tp(c)
                            for p in range(n):
                                c2 = move(c, p)
                                if c2 == c: continue
                                j = config_to_idx(c2)
                                if j in bad_set and tp(c2) == t and boundary6(c2) == b:
                                    d1, d2 = fc(c), fc(c2)
                                    if d1 < d2: fc_dirs.add("up")
                                    elif d1 > d2: fc_dirs.add("down")
                                    else: fc_dirs.add("same")
                                    count += 1
                        is_cphi = (a, b) in cphi_edges
                        print(f"    {a}→{b}: fc={fc_dirs} (n={count}) cphi={is_cphi}")

    return len(tp_6tuple_edges), len(nontrivial)

for n in [9, 10, 11, 12]:
    analyze_tp_graph(n)
