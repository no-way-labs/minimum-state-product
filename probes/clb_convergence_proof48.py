#!/usr/bin/env python3
"""
CONVERGENCE PROOF 48: Negative Cycle Detection via Bellman-Ford
================================================================

Use Bellman-Ford to detect negative-weight cycles in the comparison
edge graph. Much faster than enumerating all cycles.

The comparison graph:
- Nodes: 59 4-tuples (src[j], src[j+1], tgt[j], tgt[j+1])
- Edges: 338 transitions between consecutive 4-tuples
- Edge weight: h = α(src_pair) - α(tgt_pair) where α are interior weights

Question: for the joint n=5..11 weight vector, does the comparison
graph have any negative-weight cycle?

If NO → the pumping argument proves the LP is feasible for all n.
If YES → try to find weights where NO negative cycles exist,
         while still satisfying the boundary constraints.
"""

import sys
import os
import time
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict


def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))


def build_excursion_graph(n_val):
    ms, fs = build_system(n_val)
    n = n_val
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    anom_edges = []
    dfc_le0_adj = defaultdict(list)
    for c in bad_list:
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c); lst[i] = out; succ = tuple(lst)
                if succ in bad_set:
                    dfc = delta_fc(L, S, R, out)
                    if dfc <= 0: dfc_le0_adj[c].append(succ)
                    if out != L and out != R: anom_edges.append((c, succ, i, dfc))

    anom_sources = set(c for c, _, _, _ in anom_edges)
    anom_target_map = defaultdict(list)
    for c, succ, i, dfc in anom_edges:
        anom_target_map[succ].append(c)

    exc_edges = set()
    for b in set(s for _, s, _, _ in anom_edges):
        visited = set(); queue = [b]; visited.add(b); head = 0
        while head < len(queue):
            node = queue[head]; head += 1
            if node in anom_sources:
                for src in anom_target_map.get(b, []):
                    exc_edges.add((src, node))
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt); queue.append(nxt)

    return list(exc_edges), ms


def build_boundary_indices():
    idx = 0
    bnd = [{}, {}, {}, {}, {}]
    for a in range(2):
        for b in range(3):
            bnd[0][(a, b)] = idx; idx += 1
    for a in range(3):
        for b in range(3):
            bnd[1][(a, b)] = idx; idx += 1
    for a in range(3):
        for b in range(3):
            bnd[2][(a, b)] = idx; idx += 1
    for a in range(3):
        for b in range(2):
            bnd[3][(a, b)] = idx; idx += 1
    for a in range(2):
        for b in range(2):
            bnd[4][(a, b)] = idx; idx += 1
    n_bnd = idx
    return bnd, n_bnd


def feat_vector(c, n_val, bnd, n_bnd, int_idx, n_vars):
    n = n_val
    r = [0] * n_vars
    for j in range(n):
        j1 = (j + 1) % n
        a, b = c[j], c[j1]
        bnd_type = None
        if j == 0: bnd_type = 0
        elif j == 1: bnd_type = 1
        elif j == n-3: bnd_type = 2
        elif j == n-2: bnd_type = 3
        elif j == n-1: bnd_type = 4
        if bnd_type is not None:
            k = bnd[bnd_type].get((a, b))
            if k is not None: r[k] += 1
        else:
            k = int_idx[(a, b)]
            r[k] += j
    return r


def bellman_ford_negative_cycle(nodes, edges, weights):
    """
    Detect negative-weight cycle using Bellman-Ford.
    nodes: list of node IDs
    edges: list of (src, dst) pairs
    weights: dict mapping (src, dst) to weight
    Returns: (has_negative_cycle, cycle_edges) or (False, None)
    """
    INF = float('inf')
    n = len(nodes)
    node_idx = {nd: i for i, nd in enumerate(nodes)}
    dist = [0.0] * n  # Start with 0 distances (virtual source)
    pred = [-1] * n

    # n iterations of relaxation
    changed_node = -1
    for iteration in range(n):
        changed_node = -1
        for src, dst in edges:
            u = node_idx[src]
            v = node_idx[dst]
            w = weights[(src, dst)]
            if dist[u] + w < dist[v] - 1e-12:
                dist[v] = dist[u] + w
                pred[v] = u
                changed_node = v

    if changed_node == -1:
        return False, None

    # Trace back to find the negative cycle
    visited = set()
    v = changed_node
    for _ in range(n):
        v = pred[v]

    # v is now in the cycle. Trace it.
    cycle_nodes = []
    u = v
    while True:
        cycle_nodes.append(u)
        u = pred[u]
        if u == v:
            cycle_nodes.append(u)
            break
    cycle_nodes.reverse()

    # Convert to edges
    cycle_edges = []
    idx_to_node = {i: nd for nd, i in node_idx.items()}
    for i in range(len(cycle_nodes) - 1):
        n1 = idx_to_node[cycle_nodes[i]]
        n2 = idx_to_node[cycle_nodes[i+1]]
        cycle_edges.append((n1, n2))

    return True, cycle_edges


def main():
    bnd, n_bnd = build_boundary_indices()
    int_idx = {}
    idx = n_bnd
    for a in range(3):
        for b in range(3):
            int_idx[(a, b)] = idx; idx += 1
    n_vars = idx
    k21 = int_idx[(2, 1)]
    var_map = [i for i in range(n_vars) if i != k21]
    n_sub = len(var_map)

    int_pair_to_sub = {}
    for ki, orig_i in enumerate(var_map):
        if orig_i >= n_bnd:
            for (a, b), idx_val in int_idx.items():
                if idx_val == orig_i:
                    int_pair_to_sub[(a, b)] = ki
                    break

    # ═══════════════════════════════════════════════════════════
    # Build comparison edge graph from data
    # ═══════════════════════════════════════════════════════════
    print("=" * 70)
    print("STEP 1: Build comparison edge graph")
    print("=" * 70)

    all_edges = set()
    all_transitions = set()

    for n_val in [8, 9, 10, 11]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        for u, v in exc_edges:
            d21 = sum(j * (int(u[j] == 2 and u[(j+1)%n] == 1) -
                           int(v[j] == 2 and v[(j+1)%n] == 1))
                       for j in range(2, n-2))
            if d21 != 0:
                continue

            for j in range(2, n-3):
                edge = (u[j], u[j+1], v[j], v[j+1])
                all_edges.add(edge)
                if j + 1 <= n-4:
                    next_edge = (u[j+1], u[j+2], v[j+1], v[j+2])
                    all_transitions.add((edge, next_edge))

        dt = time.time() - t0
        print(f"  n={n_val}: done ({dt:.1f}s)")

    print(f"  Edges (4-tuples): {len(all_edges)}")
    print(f"  Transitions: {len(all_transitions)}")

    # Build adjacency
    edge_adj = defaultdict(set)
    for e1, e2 in all_transitions:
        edge_adj[e1].add(e2)

    # ═══════════════════════════════════════════════════════════
    # Get joint weight vector
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 2: Joint LP for n=5..11")
    print("=" * 70)

    all_constraint_vecs = set()
    for n_val in range(5, 12):
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val
        for u, v in exc_edges:
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            if fu[k21] - fv[k21] == 0:
                all_constraint_vecs.add(tuple(fu[i] - fv[i] for i in var_map))

    unique = list(all_constraint_vecs)
    A = np.array(unique, dtype=float)
    ne = len(unique)

    c_obj = np.ones(2 * n_sub)
    A_split = np.hstack([-A, A])
    b_ub = -np.ones(ne)
    bounds = [(0, None)] * (2 * n_sub)
    res = linprog(c_obj, A_ub=A_split, b_ub=b_ub,
                  bounds=bounds, method='highs')

    w = res.x[:n_sub] - res.x[n_sub:]
    print(f"  ||w||₁={np.sum(np.abs(w)):.2f}")

    alpha = {}
    for (a, b), ki in int_pair_to_sub.items():
        alpha[(a, b)] = w[ki]
    alpha[(2, 1)] = 0

    # ═══════════════════════════════════════════════════════════
    # Compute edge weights and detect negative cycles
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 3: Bellman-Ford negative cycle detection")
    print("=" * 70)

    # Edge weight: h(s0,s1,t0,t1) = α(s0,s1) - α(t0,t1)
    edge_weights = {}
    for e in all_edges:
        s0, s1, t0, t1 = e
        h = alpha.get((s0, s1), 0) - alpha.get((t0, t1), 0)
        edge_weights[e] = h

    n_pos = sum(1 for h in edge_weights.values() if h > 1e-9)
    n_neg = sum(1 for h in edge_weights.values() if h < -1e-9)
    n_zero = sum(1 for h in edge_weights.values() if abs(h) < 1e-9)
    print(f"  Edge h-values: {n_pos} pos, {n_neg} neg, {n_zero} zero")
    print(f"  Range: [{min(edge_weights.values()):.3f}, "
          f"{max(edge_weights.values()):.3f}]")

    # Build weighted transition graph for Bellman-Ford
    nodes = list(all_edges)
    edges_bf = list(all_transitions)
    weights_bf = {}
    for e1, e2 in all_transitions:
        weights_bf[(e1, e2)] = edge_weights[e1]

    print(f"\n  Running Bellman-Ford on {len(nodes)} nodes, "
          f"{len(edges_bf)} edges...")
    t0 = time.time()
    has_neg, cycle = bellman_ford_negative_cycle(nodes, edges_bf, weights_bf)
    dt = time.time() - t0
    print(f"  Done ({dt:.3f}s)")

    if has_neg:
        print(f"\n  NEGATIVE CYCLE FOUND!")
        if cycle:
            total_h = sum(edge_weights[e1] for e1, e2 in cycle)
            print(f"  Cycle length: {len(cycle)}")
            print(f"  Total h: {total_h:.3f}")
            for e1, e2 in cycle:
                print(f"    {e1}: h={edge_weights[e1]:.3f}")
    else:
        print(f"\n  NO NEGATIVE CYCLE!")
        print(f"  All cycles in comparison graph have non-negative h-sum.")
        print(f"  → Pumping argument: for n > verified range,")
        print(f"    interior contribution only increases with length.")
        print(f"  → Finite verification (n=5..11) suffices for ALL n!")

    # ═══════════════════════════════════════════════════════════
    # Also check: Shortest-path (minimum h-sum path) between nodes
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 4: Minimum cycle sum via Floyd-Warshall")
    print("=" * 70)

    # Floyd-Warshall on the edge graph
    # dist[i][j] = min h-sum from edge i to edge j
    n_nodes = len(nodes)
    node_to_idx = {nd: i for i, nd in enumerate(nodes)}
    INF = float('inf')
    dist = [[INF] * n_nodes for _ in range(n_nodes)]

    for i in range(n_nodes):
        dist[i][i] = 0

    for (e1, e2) in all_transitions:
        i = node_to_idx[e1]
        j = node_to_idx[e2]
        w_val = edge_weights[e1]
        if w_val < dist[i][j]:
            dist[i][j] = w_val

    print(f"  Running Floyd-Warshall on {n_nodes} nodes...")
    t0 = time.time()
    for k in range(n_nodes):
        for i in range(n_nodes):
            if dist[i][k] == INF:
                continue
            for j in range(n_nodes):
                if dist[k][j] == INF:
                    continue
                new_dist = dist[i][k] + dist[k][j]
                if new_dist < dist[i][j]:
                    dist[i][j] = new_dist
    dt = time.time() - t0
    print(f"  Done ({dt:.1f}s)")

    # Minimum cycle weight = min dist[i][i] for all i
    min_cycle = INF
    min_cycle_node = None
    for i in range(n_nodes):
        if dist[i][i] < min_cycle:
            min_cycle = dist[i][i]
            min_cycle_node = nodes[i]

    print(f"\n  Minimum cycle weight: {min_cycle:.6f}")
    if min_cycle_node:
        print(f"  At node: {min_cycle_node}")

    if min_cycle >= -1e-9:
        print(f"\n  *** ALL CYCLES NON-NEGATIVE ***")
        print(f"  This means: for any zero-edge excursion with interior")
        print(f"  length > verified range, the interior contribution")
        print(f"  is at least as large as for shorter interiors.")
        print(f"  Combined with boundary type convergence and finite")
        print(f"  verification, this PROVES the LP is feasible for ALL n.")
    else:
        print(f"\n  Minimum cycle is NEGATIVE ({min_cycle:.3f})")
        print(f"  The comparison graph has negative cycles.")
        print(f"  Need different weights or approach.")

    # ═══════════════════════════════════════════════════════════
    # STEP 5: If negative cycles, try LP with cycle constraints
    # ═══════════════════════════════════════════════════════════
    if min_cycle < -1e-9:
        print()
        print("=" * 70)
        print("STEP 5: LP with non-negative cycle constraints")
        print("=" * 70)
        print("Add constraints: for each cycle C in comparison graph,")
        print("Σ_{e in C} h(e) ≥ 0, i.e., Σ α(src_pair) - α(tgt_pair) ≥ 0")
        print()

        # Find ALL negative cycles by checking dist[i][i]
        neg_cycle_nodes = []
        for i in range(n_nodes):
            if dist[i][i] < -1e-9:
                neg_cycle_nodes.append((nodes[i], dist[i][i]))
        print(f"  Nodes on negative cycles: {len(neg_cycle_nodes)}")
        for nd, d in sorted(neg_cycle_nodes, key=lambda x: x[1])[:10]:
            print(f"    {nd}: min_cycle_through={d:.3f}")

        # For the LP: we need to constrain the INTERIOR weights
        # such that no cycle in the comparison graph has negative h-sum.
        # Since h(s0,s1,t0,t1) = α(s0,s1) - α(t0,t1), the cycle sum is:
        # Σ [α(src_pair_of_edge) - α(tgt_pair_of_edge)]
        # This is a linear function of the α's.
        #
        # We need this ≥ 0 for ALL cycles. By LP duality, this is equivalent
        # to requiring no negative cycle in the weighted comparison graph.
        #
        # This is a FEASIBILITY problem: find α such that
        # 1. No negative cycle in comparison graph
        # 2. All boundary+interior constraints from n=5..11 satisfied
        #
        # Condition 1 is equivalent to: the graph with weights
        # h(e) = α(src_pair) - α(tgt_pair) has no negative cycle.
        # By the potential theorem (for shortest paths), this holds iff
        # there exist "node potentials" π(e) such that:
        # h(e1) + π(e2) - π(e1) ≥ 0 for all transitions (e1→e2)
        # i.e., α(src_pair) - α(tgt_pair) + π(e2) - π(e1) ≥ 0
        #
        # So: add π variables (one per edge-node) and constraints:
        # α(src_pair_of_e1) - α(tgt_pair_of_e1) + π(e2) - π(e1) ≥ 0

        n_pot = n_nodes  # potential variables
        n_total = n_sub + n_pot

        # Build transition constraints: for each (e1→e2):
        # α(src_pair(e1)) - α(tgt_pair(e1)) + π(e2) - π(e1) ≥ 0
        trans_A = []
        for e1, e2 in all_transitions:
            row = [0.0] * n_total
            s0, s1, t0, t1 = e1
            if (s0, s1) != (2, 1) and (s0, s1) in int_pair_to_sub:
                row[int_pair_to_sub[(s0, s1)]] += 1
            if (t0, t1) != (2, 1) and (t0, t1) in int_pair_to_sub:
                row[int_pair_to_sub[(t0, t1)]] -= 1
            # Potential: π(e2) - π(e1)
            row[n_sub + node_to_idx[e2]] += 1
            row[n_sub + node_to_idx[e1]] -= 1
            trans_A.append(row)

        # Original constraints (on first n_sub variables only)
        orig_A = np.hstack([A, np.zeros((ne, n_pot))])

        # Combined
        A_trans = np.array(trans_A, dtype=float)
        n_trans = len(trans_A)
        A_combined = np.vstack([-orig_A, -A_trans])
        b_combined = np.concatenate([-np.ones(ne), np.zeros(n_trans)])

        # Objective: minimize ||α||₁ (only the first n_sub variables)
        # Use splitting: α = α⁺ - α⁻
        n_total_split = 2 * n_sub + n_pot
        c_obj = np.zeros(n_total_split)
        c_obj[:n_sub] = 1  # minimize |α⁺|
        c_obj[n_sub:2*n_sub] = 1  # minimize |α⁻|

        # Rebuild constraints with splitting
        # α_i = α⁺_i - α⁻_i, π_j free
        # Original: Σ (α⁺_i - α⁻_i) * A[k,i] ≥ 1
        # Trans: Σ (α⁺_i - α⁻_i) * coeff + π(e2) - π(e1) ≥ 0

        A_orig_split = np.hstack([-orig_A[:, :n_sub], orig_A[:, :n_sub],
                                   np.zeros((ne, n_pot))])
        b_orig_split = -np.ones(ne)

        A_trans_split = np.hstack([-A_trans[:, :n_sub], A_trans[:, :n_sub],
                                    -A_trans[:, n_sub:]])
        b_trans_split = np.zeros(n_trans)

        A_full = np.vstack([A_orig_split, A_trans_split])
        b_full = np.concatenate([b_orig_split, b_trans_split])

        # Bounds: α⁺, α⁻ ≥ 0; π free
        bounds_split = ([(0, None)] * n_sub + [(0, None)] * n_sub
                        + [(None, None)] * n_pot)

        print(f"  LP: {n_total_split} vars, {len(b_full)} constraints")
        t0 = time.time()
        res2 = linprog(c_obj, A_ub=A_full, b_ub=b_full,
                        bounds=bounds_split, method='highs')
        dt = time.time() - t0

        if res2.success:
            w2_plus = res2.x[:n_sub]
            w2_minus = res2.x[n_sub:2*n_sub]
            w2 = w2_plus - w2_minus
            pi = res2.x[2*n_sub:]
            l1 = np.sum(np.abs(w2))
            print(f"  LP with cycle constraints: FEASIBLE! "
                  f"||α||₁={l1:.2f} ({dt:.1f}s)")

            # Verify no negative cycles
            alpha2 = {}
            for (a, b), ki in int_pair_to_sub.items():
                alpha2[(a, b)] = w2[ki]
            alpha2[(2, 1)] = 0

            # Recompute edge weights and check
            for e in all_edges:
                s0, s1, t0, t1 = e
                h = alpha2.get((s0, s1), 0) - alpha2.get((t0, t1), 0)
                edge_weights[e] = h

            # Quick negative cycle check via Bellman-Ford
            weights_bf2 = {}
            for e1, e2 in all_transitions:
                weights_bf2[(e1, e2)] = edge_weights[e1]
            has_neg2, _ = bellman_ford_negative_cycle(nodes, edges_bf, weights_bf2)
            print(f"  Negative cycle with new weights: {has_neg2}")

            # Print new interior weights
            print(f"\n  New interior weights:")
            for (a, b), ki in sorted(int_pair_to_sub.items()):
                if abs(w2[ki]) > 0.001:
                    print(f"    α({a},{b}) = {w2[ki]:.4f}")

            # Verify on original constraints
            gaps = A[:, :n_sub] @ w2
            print(f"\n  Original constraint gaps: min={gaps.min():.3f}")

            # Test these weights on n=12 (if data available)
            print(f"\n  Testing new weights on n=12...")
            exc_12, ms_12 = build_excursion_graph(12)
            n_fail = 0
            n_total_12 = 0
            for u, v in exc_12:
                fu = feat_vector(u, 12, bnd, n_bnd, int_idx, n_vars)
                fv = feat_vector(v, 12, bnd, n_bnd, int_idx, n_vars)
                if fu[k21] - fv[k21] == 0:
                    n_total_12 += 1
                    cvec = np.array([fu[i] - fv[i] for i in var_map[:n_sub]])
                    gap = cvec @ w2
                    if gap < 1 - 1e-9:
                        n_fail += 1
            print(f"  n=12: {n_fail}/{n_total_12} failures")
        else:
            print(f"  LP with cycle constraints: INFEASIBLE ({dt:.1f}s)")
            print("  Cannot find weights with non-negative cycles!")


if __name__ == '__main__':
    main()
