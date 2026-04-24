#!/usr/bin/env python3
"""
CONVERGENCE PROOF 51: Triple Window Potential + Extended Boundary
==================================================================

Pair potential (8 interior vars) is DEAD for pumping (both cycle directions
infeasible with LP constraints).

NEW IDEAS:
  A. Extended boundary: treat positions 2 and n-3 as boundary (individual
     weights), interior = positions 3..n-4 with uniform φ=1 weights.
     More boundary flexibility, fewer interior constraints.

  B. Triple window: g(c[j-1], c[j], c[j+1]) with 27 interior variables.
     Comparison gain becomes edge-dependent (not node-dependent),
     potentially eliminating negative cycles.

  C. Hybrid: extended boundary + triple interior.

Test each approach: LP feasibility, then cycle analysis.
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


def bellman_ford_negative_cycle(nodes, edges, weights):
    n = len(nodes)
    node_idx = {nd: i for i, nd in enumerate(nodes)}
    dist = [0.0] * n
    pred = [-1] * n

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

    return changed_node != -1


def main():
    # ═══════════════════════════════════════════════════════════
    # PART A: Extended boundary (positions 0,1,2,...,n-3,n-2,n-1)
    # Interior: positions 3..n-4 with uniform φ=1
    # ═══════════════════════════════════════════════════════════
    print("=" * 70)
    print("PART A: Extended boundary + uniform interior (φ=1)")
    print("=" * 70)
    print("Boundary: positions 0,1,2 (left) and n-3,n-2,n-1 (right)")
    print("Interior: positions 3..n-4 with uniform pair weights")
    print()

    # Extended boundary indices:
    # pos 0: c[0] ∈ {0,1}, c[1] ∈ {0,1,2} → 6 vars
    # pos 1: c[1] ∈ {0,1,2}, c[2] ∈ {0,1,2} → 9 vars
    # pos 2: c[2] ∈ {0,1,2}, c[3] ∈ {0,1,2} → 9 vars  (NEW)
    # pos n-3: c[n-3] ∈ {0,1,2}, c[n-2] ∈ {0,1,2} → 9 vars  (existing, renumbered)
    # pos n-2: c[n-2] ∈ {0,1,2}, c[n-1] ∈ {0,1} → 6 vars
    # pos n-1: c[n-1] ∈ {0,1}, c[0] ∈ {0,1} → 4 vars
    # Total boundary: 6+9+9+9+6+4 = 43

    idx = 0
    bnd = [{}, {}, {}, {}, {}, {}]
    # pos 0: (c[0], c[1]) ∈ {0,1} × {0,1,2}
    for a in range(2):
        for b in range(3):
            bnd[0][(a, b)] = idx; idx += 1
    # pos 1: (c[1], c[2])
    for a in range(3):
        for b in range(3):
            bnd[1][(a, b)] = idx; idx += 1
    # pos 2: (c[2], c[3])
    for a in range(3):
        for b in range(3):
            bnd[2][(a, b)] = idx; idx += 1
    # pos n-3: (c[n-3], c[n-2])
    for a in range(3):
        for b in range(3):
            bnd[3][(a, b)] = idx; idx += 1
    # pos n-2: (c[n-2], c[n-1])
    for a in range(3):
        for b in range(2):
            bnd[4][(a, b)] = idx; idx += 1
    # pos n-1: (c[n-1], c[0])
    for a in range(2):
        for b in range(2):
            bnd[5][(a, b)] = idx; idx += 1
    n_bnd = idx
    print(f"  Boundary variables: {n_bnd}")

    # Interior: 9 pair types (uniform weight)
    int_idx = {}
    for a in range(3):
        for b in range(3):
            int_idx[(a, b)] = idx; idx += 1
    n_vars = idx
    k21 = int_idx[(2, 1)]

    # Exclude α(2,1) from sub-LP
    var_map = [i for i in range(n_vars) if i != k21]
    n_sub = len(var_map)
    print(f"  Total variables (excl α(2,1)): {n_sub}")

    int_pair_to_sub = {}
    for ki, orig_i in enumerate(var_map):
        if orig_i >= n_bnd:
            for (a, b), idx_val in int_idx.items():
                if idx_val == orig_i:
                    int_pair_to_sub[(a, b)] = ki
                    break

    def feat_vec_extbnd(c, n_val):
        n = n_val
        r = [0] * n_vars
        for j in range(n):
            j1 = (j + 1) % n
            a, b = c[j], c[j1]
            btype = None
            if j == 0: btype = 0
            elif j == 1: btype = 1
            elif j == 2: btype = 2
            elif j == n-3: btype = 3
            elif j == n-2: btype = 4
            elif j == n-1: btype = 5
            if btype is not None:
                k = bnd[btype].get((a, b))
                if k is not None: r[k] += 1
            else:
                # Interior: positions 3..n-4, uniform weight
                k = int_idx[(a, b)]
                r[k] += 1  # φ=1
        return r

    # Build constraints
    all_cvecs = set()
    comp_edges = set()
    comp_trans = set()

    for n_val in range(5, 12):
        # Need n ≥ 8 for interior to exist (positions 3..n-4 need n-4 > 3, i.e. n > 7)
        # For n < 8: all positions are boundary, no interior
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        for u, v in exc_edges:
            d21 = sum(j * (int(u[j] == 2 and u[(j+1)%n] == 1) -
                           int(v[j] == 2 and v[(j+1)%n] == 1))
                       for j in range(2, n-2))
            if d21 != 0:
                continue

            fu = feat_vec_extbnd(u, n_val)
            fv = feat_vec_extbnd(v, n_val)
            cvec = tuple(fu[i] - fv[i] for i in var_map)
            all_cvecs.add(cvec)

            # Comparison edges for interior positions 3..n-4
            if n >= 8:
                for j in range(3, n-4):
                    edge = (u[j], u[j+1], v[j], v[j+1])
                    comp_edges.add(edge)
                    if j + 1 <= n-5:
                        next_edge = (u[j+1], u[j+2], v[j+1], v[j+2])
                        comp_trans.add((edge, next_edge))

        dt = time.time() - t0
        print(f"  n={n_val}: {len(all_cvecs)} cumulative constraints ({dt:.1f}s)")

    unique = list(all_cvecs)
    A = np.array(unique, dtype=float)
    ne = len(unique)
    print(f"\n  Total unique constraints: {ne}")
    print(f"  Comparison edges: {len(comp_edges)}")
    print(f"  Comparison transitions: {len(comp_trans)}")

    # Solve LP
    c_obj = np.ones(2 * n_sub)
    A_split = np.hstack([-A, A])
    b_ub = -np.ones(ne)
    bounds = [(0, None)] * (2 * n_sub)

    t0 = time.time()
    res = linprog(c_obj, A_ub=A_split, b_ub=b_ub,
                  bounds=bounds, method='highs')
    dt = time.time() - t0

    if res.success:
        w = res.x[:n_sub] - res.x[n_sub:]
        l1 = np.sum(np.abs(w))
        print(f"\n  Extended boundary LP: FEASIBLE! ||w||₁ = {l1:.2f} ({dt:.1f}s)")

        alpha = {}
        for (a, b), ki in int_pair_to_sub.items():
            alpha[(a, b)] = w[ki]
        alpha[(2, 1)] = 0

        print(f"  Interior weights:")
        for (a, b) in sorted(int_pair_to_sub.keys()):
            ki = int_pair_to_sub[(a, b)]
            if abs(w[ki]) > 0.001:
                print(f"    α({a},{b}) = {w[ki]:.4f}")

        # Check comparison cycles (gain convention)
        if comp_edges:
            edge_G = {}
            for e in comp_edges:
                s0, s1, t0, t1 = e
                G = alpha.get((t0, t1), 0) - alpha.get((s0, s1), 0)
                edge_G[e] = G

            nodes = list(comp_edges)
            edges_bf = list(comp_trans)
            weights_G = {}
            for e1, e2 in comp_trans:
                weights_G[(e1, e2)] = edge_G[e1]

            has_neg = bellman_ford_negative_cycle(nodes, edges_bf, weights_G)
            print(f"\n  Negative gain cycle in interior: {has_neg}")

            if not has_neg:
                print(f"  *** ALL INTERIOR CYCLES NON-NEGATIVE ***")
                print(f"  → Pumping works for extended boundary + uniform interior!")
        else:
            print(f"\n  No interior comparison edges (n too small)")
    else:
        print(f"\n  Extended boundary LP: INFEASIBLE ({dt:.1f}s)")

    # ═══════════════════════════════════════════════════════════
    # PART B: Triple window potential
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("PART B: Triple window potential g(c[j-1], c[j], c[j+1])")
    print("=" * 70)
    print("Standard boundary (positions 0,1,n-3,n-2,n-1) with pair weights")
    print("Interior (positions 2..n-3) with triple weights g(a,b,c)")
    print()

    # Boundary: same 5 positions as original (34 vars for pairs)
    idx2 = 0
    bnd2 = [{}, {}, {}, {}, {}]
    for a in range(2):
        for b in range(3):
            bnd2[0][(a, b)] = idx2; idx2 += 1
    for a in range(3):
        for b in range(3):
            bnd2[1][(a, b)] = idx2; idx2 += 1
    for a in range(3):
        for b in range(3):
            bnd2[2][(a, b)] = idx2; idx2 += 1
    for a in range(3):
        for b in range(2):
            bnd2[3][(a, b)] = idx2; idx2 += 1
    for a in range(2):
        for b in range(2):
            bnd2[4][(a, b)] = idx2; idx2 += 1
    n_bnd2 = idx2

    # Interior triple weights: g(a,b,c) for (a,b,c) ∈ {0,1,2}³ → 27 vars
    # But: exclude triples involving (2,1) as the PAIR (b,c)?
    # No — the triple potential is SEPARATE from the pair monotonicity.
    # The (2,1) monotonicity was for the PAIR (c[j], c[j+1]).
    # With triple windows, we're using g(c[j-1], c[j], c[j+1]) as the potential.
    # The (2,1) pair monotonicity still holds and handles positive edges.
    # For zero edges: all 27 triple vars are active.
    #
    # Wait — we need to define what "zero edge" means for triple potential.
    # The split is still: α(2,1) large handles positive edges.
    # But now the potential is triple-based. The pair (c[j], c[j+1]) = (2,1)
    # contributes to multiple triples: g(a, 2, 1) for all a.
    # So the "large α(2,1)" becomes "large g(a, 2, 1)" for all a.
    #
    # Simpler approach: keep PAIR potential for the monotonicity argument,
    # and use TRIPLE potential for the zero-edge sub-LP.
    # But mixing pair and triple potentials is incoherent.
    #
    # Even simpler: use pure triple potential.
    # Φ(c) = Σ_j g(j, c[j-1], c[j], c[j+1])
    # Interior: g_int(a, b, c) with φ=1
    # For Δint(2,1) monotonicity: this was a property of the SYSTEM, not the potential.
    # The unweighted count of interior (2,1) pairs never increases.
    # We can still split: "positive edges" = Δcount(2,1 pairs) > 0 → use large triple weights.
    # "zero edges" = Δcount = 0 → sub-LP with remaining triple weights.
    #
    # Let me use this approach.

    # Interior triple variables
    triple_idx = {}
    idx2_t = n_bnd2
    for a in range(3):
        for b in range(3):
            for c in range(3):
                triple_idx[(a, b, c)] = idx2_t
                idx2_t += 1
    n_vars2 = idx2_t
    print(f"  Boundary variables: {n_bnd2}")
    print(f"  Interior triple variables: 27")
    print(f"  Total: {n_vars2}")

    # For zero-edge sub-LP: exclude triples containing (2,1) pair?
    # The (2,1) pair at position j contributes to triple at position j:
    #   g(c[j-1], 2, 1)  [pair (c[j], c[j+1]) = (2,1)]
    # and triple at position j+1:
    #   g(2, 1, c[j+2])  [pair (c[j], c[j+1]) = (2,1) as left context]
    # To use the "large weight" trick, we need g(a, 2, 1) to be large for all a,
    # and g(2, 1, c) to be large for all c.
    # That's 3 + 3 = 6 triples to make large.
    # But making g(2, 1, c) large would also affect triples where the middle
    # value is 1 with left neighbor 2, regardless of the pair at position j.
    #
    # This is getting complicated. Let me simplify:
    # Just use ALL 27 triple variables in the LP, without the (2,1) split.
    # Check if the LP is feasible for zero edges WITH all 27 variables.

    def feat_vec_triple(c, n_val):
        """Feature vector with triple window at interior, pair at boundary."""
        n = n_val
        r = [0] * n_vars2
        for j in range(n):
            j1 = (j + 1) % n
            a, b = c[j], c[j1]
            # Boundary pair positions
            btype = None
            if j == 0: btype = 0
            elif j == 1: btype = 1
            elif j == n-3: btype = 2
            elif j == n-2: btype = 3
            elif j == n-1: btype = 4
            if btype is not None:
                k = bnd2[btype].get((a, b))
                if k is not None: r[k] += 1

            # Interior triple positions: 2..n-3
            # Triple at j uses (c[j-1], c[j], c[j+1])
            if 2 <= j <= n-3:
                jm1 = (j - 1) % n
                jp1 = (j + 1) % n
                triple = (c[jm1], c[j], c[jp1])
                k = triple_idx[triple]
                r[k] += 1  # φ=1

        return r

    # Build constraints (zero edges only)
    all_cvecs2 = set()
    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        for u, v in exc_edges:
            d21 = sum(j * (int(u[j] == 2 and u[(j+1)%n] == 1) -
                           int(v[j] == 2 and v[(j+1)%n] == 1))
                       for j in range(2, n-2))
            if d21 != 0:
                continue

            fu = feat_vec_triple(u, n_val)
            fv = feat_vec_triple(v, n_val)
            cvec = tuple(fv[i] - fu[i] for i in range(n_vars2))
            all_cvecs2.add(cvec)

        dt = time.time() - t0
        print(f"  n={n_val}: {len(all_cvecs2)} cumulative ({dt:.1f}s)")

    unique2 = list(all_cvecs2)
    A2 = np.array(unique2, dtype=float)
    ne2 = len(unique2)
    print(f"\n  Total unique constraints: {ne2}")

    # Solve LP: min ||w||₁ s.t. A2 @ w ≥ 1
    n_v2 = n_vars2
    c_obj2 = np.ones(2 * n_v2)
    A_split2 = np.hstack([-A2, A2])
    b_ub2 = -np.ones(ne2)
    bounds2 = [(0, None)] * (2 * n_v2)

    t0 = time.time()
    res2 = linprog(c_obj2, A_ub=A_split2, b_ub=b_ub2,
                   bounds=bounds2, method='highs')
    dt = time.time() - t0

    if res2.success:
        w2 = res2.x[:n_v2] - res2.x[n_v2:]
        l12 = np.sum(np.abs(w2))
        print(f"\n  Triple LP: FEASIBLE! ||w||₁ = {l12:.2f} ({dt:.1f}s)")

        # Extract triple weights
        print(f"\n  Interior triple weights (|g| > 0.01):")
        g_triple = {}
        for (a, b, c), ki in triple_idx.items():
            g_triple[(a, b, c)] = w2[ki]
            if abs(w2[ki]) > 0.01:
                print(f"    g({a},{b},{c}) = {w2[ki]:.4f}")

        # Build comparison graph for triple potential
        # The gain at interior position j is:
        #   G_j = g(v[j-1], v[j], v[j+1]) - g(u[j-1], u[j], u[j+1])
        # This depends on the pair comparison states at j-1 and j.
        # Comparison node = (u[j], u[j+1], v[j], v[j+1])
        # Transition = (node_{j-1}, node_j)
        # Gain at j = function of (node_{j-1}, node_j)

        # Build the edge-weighted comparison graph
        print(f"\n  Building edge-weighted comparison graph for triple potential...")

        # Collect actual comparison transitions from excursion data
        edge_gains = {}  # (node_prev, node_curr) → gain
        for n_val in range(8, 12):  # Need n≥8 for enough interior
            exc_edges, ms = build_excursion_graph(n_val)
            n = n_val
            for u, v in exc_edges:
                d21 = sum(j * (int(u[j] == 2 and u[(j+1)%n] == 1) -
                               int(v[j] == 2 and v[(j+1)%n] == 1))
                           for j in range(2, n-2))
                if d21 != 0:
                    continue

                for j in range(3, n-3):  # positions where triple is fully interior
                    node_j = (u[j], u[j+1], v[j], v[j+1])
                    node_jm1 = (u[j-1], u[j], v[j-1], v[j])
                    # Gain at position j
                    gain = (g_triple.get((v[j-1], v[j], v[j+1]), 0) -
                            g_triple.get((u[j-1], u[j], u[j+1]), 0))
                    key = (node_jm1, node_j)
                    if key not in edge_gains:
                        edge_gains[key] = gain
                    else:
                        # Should be the same gain for the same transition
                        assert abs(edge_gains[key] - gain) < 1e-9, \
                            f"Inconsistent gain at {key}: {edge_gains[key]} vs {gain}"

        print(f"  Edge-weighted transitions: {len(edge_gains)}")

        # Check for negative gain cycles using Bellman-Ford
        # Nodes = pair comparison states, edges = transitions
        # Edge weight = gain at the TARGET position
        from collections import defaultdict as dd
        adj = dd(list)
        all_trans_nodes = set()
        for (e1, e2), g in edge_gains.items():
            adj[e1].append((e2, g))
            all_trans_nodes.add(e1)
            all_trans_nodes.add(e2)

        nodes_list = list(all_trans_nodes)
        edges_list = list(edge_gains.keys())
        weights_list = edge_gains

        if nodes_list:
            has_neg = bellman_ford_negative_cycle(
                nodes_list, edges_list, weights_list)
            print(f"  Negative gain cycle: {has_neg}")

            if not has_neg:
                print(f"\n  *** ALL COMPARISON CYCLES NON-NEGATIVE ***")
                print(f"  → Triple potential pumping works!")

                # Test on n=12
                print(f"\n  Testing on n=12...")
                exc_12, _ = build_excursion_graph(12)
                n_fail = 0
                n_total = 0
                for u, v in exc_12:
                    n_t = 12
                    d21 = sum(j * (int(u[j] == 2 and u[(j+1)%n_t] == 1) -
                                   int(v[j] == 2 and v[(j+1)%n_t] == 1))
                               for j in range(2, n_t-2))
                    if d21 != 0:
                        continue
                    n_total += 1
                    fu = feat_vec_triple(u, n_t)
                    fv = feat_vec_triple(v, n_t)
                    gap = sum((fv[i] - fu[i]) * w2[i] for i in range(n_v2))
                    if gap < 1 - 1e-9:
                        n_fail += 1
                print(f"    n=12: {n_fail}/{n_total} failures")
            else:
                # Try combined LP with cycle potential constraints
                print(f"\n  Trying combined LP with cycle constraints...")

                n_pot = len(nodes_list)
                node_to_idx = {nd: i for i, nd in enumerate(nodes_list)}

                # Transition constraints: gain + π(dst) - π(src) ≥ 0
                trans_rows = []
                for (e1, e2), gain in edge_gains.items():
                    row = [0.0] * (n_v2 + n_pot)
                    # Gain = g(v-triple) - g(u-triple)
                    # This is a linear function of the triple weights
                    # e1 = (u[j-1], u[j], v[j-1], v[j])
                    # e2 = (u[j], u[j+1], v[j], v[j+1])
                    # v-triple = (v[j-1], v[j], v[j+1]) = (e1[2], e1[3], e2[3])
                    # u-triple = (u[j-1], u[j], u[j+1]) = (e1[0], e1[1], e2[1])
                    v_triple = (e1[2], e1[3], e2[3])  # WRONG! e1[3]=v[j], e2[3]=v[j+1]
                    u_triple = (e1[0], e1[1], e2[1])  # e1[0]=u[j-1], e1[1]=u[j], e2[1]=u[j+1]

                    # Wait, let me re-check:
                    # e1 = (u[j-1], u[j], v[j-1], v[j]) → NO!
                    # Comparison node at pos j = (u[j], u[j+1], v[j], v[j+1])
                    # So e1 = node at j-1 = (u[j-1], u[j], v[j-1], v[j])
                    #    e2 = node at j   = (u[j], u[j+1], v[j], v[j+1])
                    # Triple at j:
                    #   u-triple = (u[j-1], u[j], u[j+1]) = (e1[0], e2[0], e2[1])
                    #   v-triple = (v[j-1], v[j], v[j+1]) = (e1[2], e2[2], e2[3])
                    u_triple = (e1[0], e2[0], e2[1])
                    v_triple = (e1[2], e2[2], e2[3])

                    ki_u = triple_idx[u_triple]
                    ki_v = triple_idx[v_triple]

                    row[ki_v] += 1   # +g(v-triple)
                    row[ki_u] -= 1   # -g(u-triple)

                    row[n_v2 + node_to_idx[e2]] += 1
                    row[n_v2 + node_to_idx[e1]] -= 1
                    trans_rows.append(row)

                n_trans = len(trans_rows)
                A_trans = np.array(trans_rows, dtype=float)

                # Combined LP
                n_total_split = 2 * n_v2 + n_pot
                c_obj_c = np.zeros(n_total_split)
                c_obj_c[:n_v2] = 1
                c_obj_c[n_v2:2*n_v2] = 1

                A_orig_pad = np.hstack([A2, np.zeros((ne2, n_pot))])
                A_orig_split = np.hstack([
                    -A_orig_pad[:, :n_v2], A_orig_pad[:, :n_v2],
                    np.zeros((ne2, n_pot))
                ])
                b_orig = -np.ones(ne2)

                A_trans_split = np.hstack([
                    -A_trans[:, :n_v2], A_trans[:, :n_v2],
                    -A_trans[:, n_v2:]
                ])
                b_trans = np.zeros(n_trans)

                A_full = np.vstack([A_orig_split, A_trans_split])
                b_full = np.concatenate([b_orig, b_trans])

                bounds_c = ([(0, None)] * n_v2 + [(0, None)] * n_v2
                            + [(None, None)] * n_pot)

                print(f"  LP: {n_total_split} vars, {len(b_full)} constraints")
                t0 = time.time()
                res_c = linprog(c_obj_c, A_ub=A_full, b_ub=b_full,
                                bounds=bounds_c, method='highs')
                dt = time.time() - t0

                if res_c.success:
                    w_c = res_c.x[:n_v2] - res_c.x[n_v2:2*n_v2]
                    l1_c = np.sum(np.abs(w_c))
                    print(f"  *** Combined LP: FEASIBLE! ***  "
                          f"||w||₁ = {l1_c:.2f} ({dt:.1f}s)")
                else:
                    print(f"  Combined LP: INFEASIBLE ({dt:.1f}s)")

                    # Diagnose
                    print(f"\n  Diagnosing: cycle constraints only...")
                    A_trans_only = np.hstack([
                        -A_trans[:, :n_v2], A_trans[:, :n_v2],
                        -A_trans[:, n_v2:]
                    ])
                    b_trans_only = np.zeros(n_trans)
                    c_trans = np.zeros(n_total_split)
                    c_trans[:n_v2] = 1
                    c_trans[n_v2:2*n_v2] = 1
                    res_to = linprog(c_trans, A_ub=A_trans_only,
                                      b_ub=b_trans_only,
                                      bounds=bounds_c, method='highs')
                    print(f"    Cycle constraints alone: "
                          f"{'FEASIBLE' if res_to.success else 'INFEASIBLE'}")
    else:
        print(f"\n  Triple LP: INFEASIBLE ({dt:.1f}s)")


if __name__ == '__main__':
    main()
