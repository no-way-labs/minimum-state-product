#!/usr/bin/env python3
"""
CONVERGENCE PROOF 47: Comparison Graph Cycle Weight Analysis
==============================================================

KEY INSIGHT: The zero-edge excursion creates a comparison state sequence
(src[j], tgt[j]) at each interior position j. This sequence follows a
FINITE-STATE TRANSDUCER with 9 states and 59 transitions.

The pair potential contribution at position j depends on the "edge label":
h(j) = Σ α(a,b) · ([src has (a,b) at j] - [tgt has (a,b) at j])

This depends on (src[j], src[j+1], tgt[j], tgt[j+1]).

QUESTION: For the optimal weight vector, does every CYCLE in the
comparison transducer have non-negative total h?

If YES → for longer interiors, pumping cycles INCREASES the gap.
So verifying finite n suffices for ALL n.

APPROACH:
1. Build the EDGE-LABELED comparison graph
2. For the per-n weight vectors, compute edge labels
3. Check all cycles for non-negative total
4. If some cycles are negative, find weights that make ALL cycles ≥ 0
   (this is a finite LP on the comparison graph!)
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

    # Interior pair indices in the sub-problem
    int_pair_to_sub = {}
    for ki, orig_i in enumerate(var_map):
        if orig_i >= n_bnd:
            for (a, b), idx_val in int_idx.items():
                if idx_val == orig_i:
                    int_pair_to_sub[(a, b)] = ki
                    break

    # ═══════════════════════════════════════════════════════════
    # PART A: Build the comparison edge graph
    # ═══════════════════════════════════════════════════════════
    print("=" * 70)
    print("PART A: Comparison edge graph from actual data")
    print("=" * 70)

    # An "edge" in the comparison graph is:
    #   (src[j], src[j+1], tgt[j], tgt[j+1]) — 4-tuple at position j
    # The h-value of this edge (for given weights) is:
    #   Σ α(a,b) · ([src has (a,b)] - [tgt has (a,b)])
    #   = α(src[j], src[j+1]) - α(tgt[j], tgt[j+1])
    #   (well, only the interior pair contribution)

    # The "transition" is:
    #   (src[j], src[j+1], tgt[j], tgt[j+1]) →
    #   (src[j+1], src[j+2], tgt[j+1], tgt[j+2])
    # The "node" connecting consecutive edges is: (src[j+1], tgt[j+1])

    # Collect all edges and transitions
    all_edges = set()  # (src_j, src_j1, tgt_j, tgt_j1) 4-tuples
    all_transitions = set()  # (edge1, edge2) consecutive pairs
    all_nodes = set()  # (src_j, tgt_j) 2-tuples

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
                node = (u[j], v[j])
                all_nodes.add(node)

                if j + 1 <= n-3:
                    next_edge = (u[j+1], u[min(j+2, n-1)], v[j+1], v[min(j+2, n-1)])
                    all_transitions.add((edge, next_edge))

        dt = time.time() - t0

    print(f"  Nodes (src_j, tgt_j): {len(all_nodes)}")
    print(f"  Edges (4-tuples): {len(all_edges)}")
    print(f"  Transitions (edge→edge): {len(all_transitions)}")

    # h-value for each edge
    # h(s0, s1, t0, t1) = Σ α(a,b) · ([s0=a,s1=b] - [t0=a,t1=b])
    # With fixed interior weights α, this is just:
    # α(s0,s1) - α(t0,t1) (if both are interior pair types, and (a,b)≠(2,1))
    # Note: α(2,1) = 0 by construction

    # The h-value depends on the weight choice. For each weight vector,
    # h(s0,s1,t0,t1) = α_sub(s0,s1) - α_sub(t0,t1)
    # where α_sub is the interior weight (0 for (2,1))

    # For h to be non-negative on all cycles:
    # Σ_{edges in cycle} h = Σ [α(src pair) - α(tgt pair)]
    # For a cycle of 4-tuple edges:
    # If we go (e1, e2, ..., ek, e1), each edge contributes α(src pair) - α(tgt pair)
    # The sum telescopes... wait, does it?

    # Each 4-tuple edge (s0,s1,t0,t1) contributes h = α(s0,s1) - α(t0,t1).
    # In a cycle of POSITIONS (state sequence repeating):
    # s_j0, s_{j0+1}, ..., s_{j1} = s_{j0}
    # The edge at position j is (src[j], src[j+1], tgt[j], tgt[j+1])
    # h(j) = α(src[j], src[j+1]) - α(tgt[j], tgt[j+1])
    # Sum over j=j0..j1-1:
    # Σ h(j) = Σ α(src[j], src[j+1]) - Σ α(tgt[j], tgt[j+1])

    # These are path sums in the src and tgt pair graphs.
    # They don't telescope in general because the pairs overlap:
    # pair at j = (c[j], c[j+1]) and pair at j+1 = (c[j+1], c[j+2])

    print()
    print("=" * 70)
    print("PART B: Edge h-values and cycle analysis")
    print("=" * 70)

    # For a given α vector, the h-value of edge (s0,s1,t0,t1) is:
    # h = α(s0,s1) - α(t0,t1)
    # Note: only 8 interior pairs have weights (not (2,1))
    # h is 0 when (s0,s1) = (t0,t1) (no change at this position)

    # Get the joint n=5..11 weight vector
    all_constraint_vecs = []
    for n_val in range(5, 12):
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val
        for u, v in exc_edges:
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            if fu[k21] - fv[k21] == 0:
                all_constraint_vecs.append([fu[i] - fv[i] for i in var_map])

    unique = list(set(tuple(v) for v in all_constraint_vecs))
    A = np.array(unique, dtype=float)
    ne = len(unique)
    print(f"  Joint constraints: {ne}")

    c_obj = np.ones(2 * n_sub)
    A_split = np.hstack([-A, A])
    b_ub = -np.ones(ne)
    bounds = [(0, None)] * (2 * n_sub)
    res = linprog(c_obj, A_ub=A_split, b_ub=b_ub,
                  bounds=bounds, method='highs')

    if not res.success:
        print("  Joint LP INFEASIBLE — cannot proceed")
        return

    w = res.x[:n_sub] - res.x[n_sub:]
    print(f"  Joint LP: FEASIBLE, ||w||₁={np.sum(np.abs(w)):.2f}")

    # Extract interior α values
    alpha = {}
    for (a, b), ki in int_pair_to_sub.items():
        alpha[(a, b)] = w[ki]
    alpha[(2, 1)] = 0  # By construction

    print(f"  Interior weights: " + ", ".join(
        f"α{p}={v:.3f}" for p, v in sorted(alpha.items()) if abs(v) > 0.001))

    # Compute h-values for all edges
    print(f"\n  Edge h-values:")
    edge_h = {}
    for e in all_edges:
        s0, s1, t0, t1 = e
        h = alpha.get((s0, s1), 0) - alpha.get((t0, t1), 0)
        edge_h[e] = h

    # Statistics
    h_vals = list(edge_h.values())
    n_pos = sum(1 for h in h_vals if h > 1e-9)
    n_neg = sum(1 for h in h_vals if h < -1e-9)
    n_zero = sum(1 for h in h_vals if abs(h) < 1e-9)
    print(f"    Positive h: {n_pos}, Negative h: {n_neg}, Zero h: {n_zero}")
    print(f"    h range: [{min(h_vals):.3f}, {max(h_vals):.3f}]")

    # ═══════════════════════════════════════════════════════════
    # PART C: Find cycles in the comparison transition graph
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("PART C: Cycles in comparison transition graph")
    print("=" * 70)

    # Build adjacency for the EDGE graph (4-tuple → 4-tuple transitions)
    edge_adj = defaultdict(set)
    for e1, e2 in all_transitions:
        edge_adj[e1].add(e2)

    # Find all SIMPLE cycles using DFS (up to reasonable length)
    # Since the graph is small (≤81 edges), this is feasible
    def find_cycles(adj, max_len=10):
        """Find all simple cycles up to max_len in the edge graph."""
        cycles = []
        edges = list(adj.keys())
        for start in edges:
            stack = [(start, [start], {start})]
            while stack:
                node, path, visited = stack.pop()
                for nxt in adj.get(node, set()):
                    if nxt == start and len(path) >= 2:
                        cycles.append(list(path))
                    elif nxt not in visited and len(path) < max_len:
                        stack.append((nxt, path + [nxt], visited | {nxt}))
        # Deduplicate (cycles are the same under rotation)
        unique_cycles = []
        seen = set()
        for cyc in cycles:
            key = min(tuple(cyc[i:] + cyc[:i]) for i in range(len(cyc)))
            if key not in seen:
                seen.add(key)
                unique_cycles.append(cyc)
        return unique_cycles

    print(f"  Finding cycles in edge graph ({len(all_edges)} edges)...")
    t0 = time.time()
    cycles = find_cycles(edge_adj, max_len=12)
    dt = time.time() - t0
    print(f"  Found {len(cycles)} simple cycles (up to length 12) ({dt:.1f}s)")

    # Compute h-sum for each cycle
    neg_cycles = []
    zero_cycles = []
    pos_cycles = []
    for cyc in cycles:
        h_sum = sum(edge_h.get(e, 0) for e in cyc)
        if h_sum < -1e-9:
            neg_cycles.append((cyc, h_sum))
        elif h_sum > 1e-9:
            pos_cycles.append((cyc, h_sum))
        else:
            zero_cycles.append((cyc, h_sum))

    print(f"  Cycle h-sums: {len(pos_cycles)} positive, "
          f"{len(zero_cycles)} zero, {len(neg_cycles)} negative")

    if neg_cycles:
        print(f"\n  NEGATIVE cycles (problematic):")
        neg_cycles.sort(key=lambda x: x[1])
        for cyc, h_sum in neg_cycles[:10]:
            print(f"    h_sum={h_sum:.3f}, len={len(cyc)}")
            for e in cyc:
                print(f"      {e}: h={edge_h.get(e, 0):.3f}")
    else:
        print(f"\n  ALL CYCLES NON-NEGATIVE! Pumping argument works!")

    if zero_cycles:
        print(f"\n  ZERO cycles: {len(zero_cycles)}")
        for cyc, h_sum in zero_cycles[:5]:
            print(f"    len={len(cyc)}: {cyc}")

    # ═══════════════════════════════════════════════════════════
    # PART D: LP for non-negative cycle weights
    # ═══════════════════════════════════════════════════════════
    if neg_cycles:
        print()
        print("=" * 70)
        print("PART D: LP for non-negative cycle weights")
        print("=" * 70)
        print("Can we find α such that ALL cycles have h-sum ≥ 0")
        print("AND all boundary+interior constraints are satisfied?")

        # For each cycle C = (e1, e2, ..., ek):
        # h_sum = Σ [α(si0,si1) - α(ti0,ti1)]
        # This is a LINEAR function of the α's.
        # Constraint: h_sum ≥ 0

        # Build cycle constraints on α
        # α is indexed by pair (a,b) for (a,b) ≠ (2,1), sub index ki
        cycle_constraints = []
        for cyc, _ in neg_cycles + zero_cycles + pos_cycles:
            # h_sum = Σ_e [α(s0,s1) - α(t0,t1)]
            coeff = [0] * n_sub
            for s0, s1, t0, t1 in cyc:
                if (s0, s1) != (2, 1) and (s0, s1) in int_pair_to_sub:
                    coeff[int_pair_to_sub[(s0, s1)]] += 1
                if (t0, t1) != (2, 1) and (t0, t1) in int_pair_to_sub:
                    coeff[int_pair_to_sub[(t0, t1)]] -= 1
            cycle_constraints.append(coeff)

        print(f"  {len(cycle_constraints)} cycle constraints")

        # Check: is each cycle constraint trivially 0?
        n_trivial = sum(1 for c in cycle_constraints
                        if all(abs(x) < 1e-9 for x in c))
        print(f"  Trivially zero: {n_trivial}")

        # The cycle constraints plus the original LP constraints
        # must all be satisfiable simultaneously
        # Original: A_orig @ w ≥ 1
        # Cycles: A_cyc @ w ≥ 0
        A_orig = A  # already computed
        A_cyc = np.array(cycle_constraints, dtype=float)
        n_cyc = len(cycle_constraints)

        # Combined LP: minimize ||w||₁ subject to:
        # A_orig @ w ≥ 1
        # A_cyc @ w ≥ 0
        # Using variable splitting w = w+ - w-
        c_obj = np.ones(2 * n_sub)
        A_orig_split = np.hstack([-A_orig, A_orig])
        A_cyc_split = np.hstack([-A_cyc, A_cyc])
        b_orig = -np.ones(ne)
        b_cyc = np.zeros(n_cyc)

        A_full = np.vstack([A_orig_split, A_cyc_split])
        b_full = np.concatenate([b_orig, b_cyc])
        bounds = [(0, None)] * (2 * n_sub)

        res2 = linprog(c_obj, A_ub=A_full, b_ub=b_full,
                        bounds=bounds, method='highs')

        if res2.success:
            w2 = res2.x[:n_sub] - res2.x[n_sub:]
            print(f"  Combined LP: FEASIBLE! ||w||₁={np.sum(np.abs(w2)):.2f}")

            # Verify cycle h-sums
            for cyc, _ in neg_cycles[:5]:
                h_sum2 = 0
                for s0, s1, t0, t1 in cyc:
                    a_s = 0 if (s0, s1) == (2, 1) else w2[int_pair_to_sub[(s0, s1)]]
                    a_t = 0 if (t0, t1) == (2, 1) else w2[int_pair_to_sub[(t0, t1)]]
                    h_sum2 += a_s - a_t
                print(f"    Cycle h_sum: {h_sum2:.3f}")
        else:
            print(f"  Combined LP: INFEASIBLE")
            print("  Cannot find weights with non-negative cycle sums!")


if __name__ == '__main__':
    main()
