#!/usr/bin/env python3
"""
Compute the COMPLETE set of constant-FutureFc (CF) boundary 6-tuple transitions
for the CUP-2 system at n=9, check if it forms a DAG, and compute rank function.

Uses the actual CUP-2 tables and infrastructure from cup2_theorem.py and verifier.py.
"""

import sys, os, time
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, deque

N = 9

def fc(c, n):
    """fc = number of positions where c[j] != c[(j+1) % n]."""
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])

def exp2_count(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] in (0, 1))

def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def exp2_weight(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] in (0, 1))

def sixtuple(c, n):
    return (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])

def main():
    sys.stdout.reconfigure(line_buffering=True)
    n = N
    print(f"=" * 70)
    print(f"CF BOUNDARY 6-TUPLE DAG CHECK — n={n}")
    print(f"=" * 70)

    # Build system
    print(f"\nBuilding CUP-2 system for n={n}...")
    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    assert result['valid'], "System verification failed!"
    good_set = result['good_configs']
    print(f"  State sizes: {ms}")
    print(f"  Product: {result.get('product', 'N/A')}")
    print(f"  Good configs: {len(good_set)}")

    # Enumerate all configs
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)
    print(f"  Total configs: {len(all_configs)}")
    print(f"  Bad configs: {len(bad_list)}")

    # Compute fc for all bad configs
    fc_cache = {}
    for c in bad_list:
        fc_cache[c] = fc(c, n)

    # Build TP (three-property) subgraph: edges preserving exp2_count, int_21, exp2_weight
    print(f"\nBuilding TP subgraph (three monotone quantities preserved)...")
    tp_edges = []
    tp_fwd = defaultdict(list)
    for c in bad_list:
        e2c = exp2_count(c, n)
        i21c = int_21(c, n)
        ewc = exp2_weight(c, n)
        for i in range(n):
            L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c); lst[i] = out; succ = tuple(lst)
                if succ in bad_set:
                    e2s = exp2_count(succ, n)
                    i21s = int_21(succ, n)
                    ews = exp2_weight(succ, n)
                    if e2s == e2c and i21s == i21c and ews == ewc:
                        dfc = fc_cache[succ] - fc_cache[c]
                        tp_edges.append((c, succ, i, dfc))
                        tp_fwd[c].append((succ, dfc))

    print(f"  TP edges: {len(tp_edges)}")

    # Compute g_full = max reachable fc gain via TP edges (fixpoint)
    print(f"\nComputing Phi_full (max reachable fc)...")
    g = {c: 0 for c in bad_set}
    for iteration in range(2 * n + 10):
        changed = False
        for c in bad_list:
            for s, dfc in tp_fwd.get(c, []):
                new_g = dfc + g[s]
                if new_g > g[c]:
                    g[c] = new_g
                    changed = True
        if not changed:
            break
    print(f"  g converged after {iteration + 1} iterations")

    phi = {c: fc_cache[c] + g[c] for c in bad_set}

    # Verify Phi_full non-increasing on TP edges
    phi_viols = sum(1 for c, s, pos, dfc in tp_edges if phi[s] > phi[c])
    print(f"  Phi_full violations: {phi_viols}")
    assert phi_viols == 0, "Phi_full is NOT non-increasing!"

    phi_dist = defaultdict(int)
    for c in bad_set:
        phi_dist[phi[c]] += 1
    print(f"  Phi_full distribution: {dict(sorted(phi_dist.items()))}")

    # Extract constant-Phi edges
    const_edges = [(c, s, pos, dfc) for c, s, pos, dfc in tp_edges if phi[s] == phi[c]]
    print(f"\n  Constant-Phi edges: {len(const_edges)}")

    # Project to 6-tuple transitions
    print(f"\nProjecting to 6-tuple transitions...")
    sixtuple_transitions = set()
    sixtuple_transitions_all = set()
    for c, s, pos, dfc in const_edges:
        s6c = sixtuple(c, n)
        s6s = sixtuple(s, n)
        sixtuple_transitions_all.add((s6c, s6s))
        if s6c != s6s:
            sixtuple_transitions.add((s6c, s6s))

    id_count = len(sixtuple_transitions_all) - len(sixtuple_transitions)
    print(f"  Non-trivial 6-tuple transitions: {len(sixtuple_transitions)}")
    print(f"  Identity 6-tuple transitions (interior fires): {id_count}")

    # Collect all nodes
    all_nodes = set()
    for s1, s2 in sixtuple_transitions:
        all_nodes.add(s1)
        all_nodes.add(s2)
    print(f"  Unique 6-tuple nodes: {len(all_nodes)}")

    # Build adjacency list
    adj = defaultdict(set)
    for s1, s2 in sixtuple_transitions:
        adj[s1].add(s2)

    # Check for self-loops
    self_loops = [s for s1, s2 in sixtuple_transitions if s1 == s2 for s in [s1]]
    print(f"  Self-loops: {len(self_loops)}")

    # DAG check using iterative Tarjan's SCC
    print(f"\nChecking DAG property (Tarjan's SCC)...")

    def tarjan_iterative(nodes, adj):
        idx = [0]
        S = []
        low = {}
        num = {}
        on = {}
        result = []

        for start in nodes:
            if start in num:
                continue
            call_stack = [(start, iter(adj.get(start, set())), True)]
            num[start] = low[start] = idx[0]
            idx[0] += 1
            S.append(start)
            on[start] = True

            while call_stack:
                v, it, first_visit = call_stack[-1]
                found_next = False
                for w in it:
                    if w not in num:
                        num[w] = low[w] = idx[0]
                        idx[0] += 1
                        S.append(w)
                        on[w] = True
                        call_stack.append((w, iter(adj.get(w, set())), True))
                        found_next = True
                        break
                    elif on.get(w, False):
                        low[v] = min(low[v], num[w])

                if not found_next:
                    call_stack.pop()
                    if low[v] == num[v]:
                        scc = []
                        while True:
                            w = S.pop()
                            on[w] = False
                            scc.append(w)
                            if w == v:
                                break
                        result.append(scc)
                    if call_stack:
                        parent = call_stack[-1][0]
                        low[parent] = min(low[parent], low[v])

        return result

    sccs = tarjan_iterative(all_nodes, adj)
    non_trivial = [scc for scc in sccs if len(scc) > 1]

    print(f"  Total SCCs: {len(sccs)}")
    print(f"  Non-trivial SCCs (size > 1): {len(non_trivial)}")

    is_dag = len(non_trivial) == 0 and len(self_loops) == 0

    if not is_dag:
        print(f"\n  NOT a DAG!")
        for i, scc in enumerate(non_trivial[:10]):
            print(f"    SCC {i}: size {len(scc)}, sample: {scc[:3]}")
    else:
        print(f"\n  IS a DAG!")

    # Compute rank function (longest path) regardless
    if is_dag:
        print(f"\nComputing rank function (longest path)...")

        # BFS-based longest path on DAG
        # Tarjan gives reverse topological order
        topo_order = [scc[0] for scc in sccs]

        rank = {}
        for v in topo_order:
            if not adj.get(v, set()):
                rank[v] = 0
            else:
                rank[v] = max(rank.get(w, 0) for w in adj[v]) + 1

        max_rank = max(rank.values()) if rank else 0
        print(f"  Maximum rank (longest path): {max_rank}")
        print(f"  Formula prediction: 7*{n} - 30 = {7*n - 30}")

        # Rank distribution
        rank_dist = defaultdict(int)
        for v, r in rank.items():
            rank_dist[r] += 1
        print(f"\n  Rank distribution:")
        for r in sorted(rank_dist.keys()):
            print(f"    rank {r:3d}: {rank_dist[r]:3d} nodes")

        # Print all transitions with ranks
        print(f"\n  All {len(sixtuple_transitions)} 6-tuple transitions:")
        sorted_trans = sorted(sixtuple_transitions, key=lambda t: (-rank.get(t[0], -1), t))
        for s1, s2 in sorted_trans:
            r1 = rank.get(s1, '?')
            r2 = rank.get(s2, '?')
            print(f"    {s1} [rank {r1}] -> {s2} [rank {r2}]")

        print(f"\n{'=' * 70}")
        print(f"SUMMARY: DAG with {len(all_nodes)} nodes, {len(sixtuple_transitions)} edges, max rank = {max_rank}")
        print(f"{'=' * 70}")

if __name__ == '__main__':
    main()
