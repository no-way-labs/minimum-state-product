#!/usr/bin/env python3
"""
Check CF measure — optimized with SCC-based FutureFc computation.
"""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from itertools import product as cartesian
from collections import defaultdict, deque

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j+1) % n])

def psi(c, n):
    total = 0
    for j in range(n):
        L = c[(j-1) % n]; S = c[j]; R = c[(j+1) % n]
        total += (1 if S != L else 0) + (1 if S != R else 0)
    return total

def tarjan_scc(nodes, adj):
    """Tarjan's SCC algorithm. Returns list of SCCs in reverse topological order."""
    index_counter = [0]
    stack = []
    on_stack = set()
    index = {}
    lowlink = {}
    sccs = []

    def strongconnect(v):
        index[v] = lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)
        for w in adj.get(v, []):
            if w not in index:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], index[w])
        if lowlink[v] == index[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                scc.append(w)
                if w == v:
                    break
            sccs.append(scc)

    # Use iterative version for large graphs
    for v in nodes:
        if v not in index:
            # Iterative Tarjan
            call_stack = [(v, 0)]
            while call_stack:
                node, adj_idx = call_stack[-1]
                if node not in index:
                    index[node] = lowlink[node] = index_counter[0]
                    index_counter[0] += 1
                    stack.append(node)
                    on_stack.add(node)
                neighbors = adj.get(node, [])
                if adj_idx < len(neighbors):
                    call_stack[-1] = (node, adj_idx + 1)
                    w = neighbors[adj_idx]
                    if w not in index:
                        call_stack.append((w, 0))
                    elif w in on_stack:
                        lowlink[node] = min(lowlink[node], index[w])
                else:
                    call_stack.pop()
                    if lowlink[node] == index[node]:
                        scc = []
                        while True:
                            w = stack.pop()
                            on_stack.discard(w)
                            scc.append(w)
                            if w == node:
                                break
                        sccs.append(scc)
                    if call_stack:
                        parent = call_stack[-1][0]
                        lowlink[parent] = min(lowlink[parent], lowlink[node])
    return sccs

def compute_future_fc_fast(bad_set, bad_adj, n):
    """Compute FutureFc via SCC condensation + reverse topological propagation."""
    nodes = list(bad_set)
    sccs = tarjan_scc(nodes, bad_adj)
    # sccs is in reverse topological order

    # Map each node to its SCC index
    scc_id = {}
    for i, scc in enumerate(sccs):
        for v in scc:
            scc_id[v] = i

    # Compute max fc within each SCC
    scc_max_fc = []
    for scc in sccs:
        scc_max_fc.append(max(fc(v, n) for v in scc))

    # Build condensation DAG (edges between SCCs)
    scc_adj = defaultdict(set)
    for v in bad_set:
        for w in bad_adj.get(v, []):
            si, sj = scc_id[v], scc_id[w]
            if si != sj:
                scc_adj[si].add(sj)

    # Propagate max fc in topological order (sccs already in reverse topo)
    # So process from end to beginning
    future_fc_scc = list(scc_max_fc)
    for i in range(len(sccs)):
        for j in scc_adj.get(i, set()):
            future_fc_scc[i] = max(future_fc_scc[i], future_fc_scc[j])

    # Map back to nodes
    future_fc = {}
    for v in bad_set:
        future_fc[v] = future_fc_scc[scc_id[v]]
    return future_fc

def analyze_n(n):
    ms, fs = build_system(n)
    all_configs = list(cartesian(*(range(m) for m in ms)))

    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    up_down = list(range(n)) + list(range(n-2, 0, -1))
    full = up_down * (3 * n)
    for mover in full:
        config = list(cycle[-1])
        L = config[(mover-1) % n]; S = config[mover]; R = config[(mover+1) % n]
        new_val = fs[mover](L, S, R)
        if new_val != S:
            config[mover] = new_val
            t = tuple(config)
            if t not in visited:
                visited.add(t)
                cycle.append(t)
    good_set = visited
    bad_set = set(c for c in all_configs if c not in good_set)

    bad_adj = defaultdict(list)
    for c in bad_set:
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            nv = fs[i](L, S, R)
            if nv != S:
                lst = list(c); lst[i] = nv; succ = tuple(lst)
                if succ in bad_set:
                    bad_adj[c].append(succ)

    print(f"n={n}: {len(bad_set)} bad configs, computing FutureFc...", end=" ", flush=True)
    future_fc_map = compute_future_fc_fast(bad_set, bad_adj, n)
    print("done")

    cf_nonneg = 0
    cf_neg = 0
    nonneg_measure_fails = 0
    gap_psi_fail_count = 0

    all_cf_edges = []
    for c in bad_set:
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            nv = fs[i](L, S, R)
            if nv != S:
                lst = list(c); lst[i] = nv; cp = tuple(lst)
                if cp in bad_set and future_fc_map[cp] == future_fc_map[c]:
                    all_cf_edges.append((c, cp))
                    fc_c = fc(c, n); fc_cp = fc(cp, n)
                    psi_c = psi(c, n); psi_cp = psi(cp, n)

                    if fc_cp >= fc_c:
                        cf_nonneg += 1
                    else:
                        cf_neg += 1

                    nm_c = (n - fc_c, psi_c)
                    nm_cp = (n - fc_cp, psi_cp)
                    if nm_cp >= nm_c:
                        nonneg_measure_fails += 1

                    gap_c = future_fc_map[c] - fc_c
                    gap_cp = future_fc_map[cp] - fc_cp
                    if (gap_cp, psi_cp) >= (gap_c, psi_c):
                        gap_psi_fail_count += 1

    total_cf = cf_nonneg + cf_neg
    print(f"  {total_cf} CF steps (nonneg={cf_nonneg}, neg={cf_neg})")
    print(f"  nonneg_measure (n-fc,Psi) fails: {nonneg_measure_fails}/{total_cf}")
    print(f"  Lex(FutureFc-fc, Psi) fails: {gap_psi_fail_count}/{total_cf}")

    # Check if CF is a DAG
    cf_adj = defaultdict(list)
    cf_nodes = set()
    for c, cp in all_cf_edges:
        cf_adj[c].append(cp)
        cf_nodes.add(c)
        cf_nodes.add(cp)

    # Quick cycle check via SCC
    cf_sccs = tarjan_scc(list(cf_nodes), cf_adj)
    has_cycle = any(len(scc) > 1 for scc in cf_sccs)
    # Also check self-loops
    if not has_cycle:
        for c, cp in all_cf_edges:
            if c == cp:
                has_cycle = True
                break

    print(f"  CF is DAG: {not has_cycle}")

    if not has_cycle:
        in_degree = defaultdict(int)
        for c in cf_nodes:
            in_degree[c] = 0
        for c, cp in all_cf_edges:
            in_degree[cp] += 1
        queue = deque(c for c in cf_nodes if in_degree[c] == 0)
        rank = {c: 0 for c in cf_nodes}
        while queue:
            c = queue.popleft()
            for cp in cf_adj.get(c, []):
                rank[cp] = max(rank[cp], rank[c] + 1)
                in_degree[cp] -= 1
                if in_degree[cp] == 0:
                    queue.append(cp)
        max_rank = max(rank.values()) if rank else 0
        print(f"  CF DAG max rank: {max_rank}")

    print()

for n in range(5, 13):
    analyze_n(n)
