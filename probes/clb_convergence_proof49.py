#!/usr/bin/env python3
"""
CONVERGENCE PROOF 49: Uniform Position Weight (φ=1) + Correct Cycle Direction
===============================================================================

KEY INSIGHT: proof48 used position weight φ=j, which makes the comparison
graph cycle weights position-dependent. With UNIFORM weight φ=1, the
comparison graph weights are position-independent.

CRITICAL: proof48 also used the WRONG sign convention for the pumping argument.
The pumping argument requires G_cycle ≥ 0 where G = α(v-pair) - α(u-pair),
NOT h_48 = α(u-pair) - α(v-pair) ≥ 0.

PLAN:
1. Build zero-edge sub-LP with φ=1 for n=5..12
2. Check comparison cycles with GAIN convention (G = α(v) - α(u))
3. If cycles non-negative → pumping argument proves all-n
4. If not: try combined LP (constraints + cycle potential constraints)
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


def feat_vector_uniform(c, n_val, bnd, n_bnd, int_idx, n_vars):
    """Feature vector with UNIFORM interior weight φ=1."""
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
            r[k] += 1  # ← UNIFORM weight (was j in proof48)
    return r


def bellman_ford_negative_cycle(nodes, edges, weights):
    INF = float('inf')
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

    if changed_node == -1:
        return False, None

    visited = set()
    v = changed_node
    for _ in range(n):
        v = pred[v]

    cycle_nodes = []
    u = v
    while True:
        cycle_nodes.append(u)
        u = pred[u]
        if u == v:
            cycle_nodes.append(u)
            break
    cycle_nodes.reverse()

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
    # STEP 1: Build zero-edge sub-LP with φ=1 for n=5..12
    # ═══════════════════════════════════════════════════════════
    print("=" * 70)
    print("STEP 1: Zero-edge sub-LP with UNIFORM weights (φ=1)")
    print("=" * 70)

    all_constraint_vecs = {}  # constraint_tuple → set of n_vals
    comparison_edges = set()
    comparison_transitions = set()

    for n_val in range(5, 13):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        n_zero = 0
        n_new = 0
        for u, v in exc_edges:
            # Check if zero edge (unweighted (2,1) count, not position-weighted)
            d21_unweighted = sum(
                int(u[j] == 2 and u[(j+1)%n] == 1) -
                int(v[j] == 2 and v[(j+1)%n] == 1)
                for j in range(2, n-2))

            # Also check position-weighted
            d21_weighted = sum(
                j * (int(u[j] == 2 and u[(j+1)%n] == 1) -
                     int(v[j] == 2 and v[(j+1)%n] == 1))
                for j in range(2, n-2))

            if d21_weighted != 0:
                continue
            n_zero += 1

            fu = feat_vector_uniform(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector_uniform(v, n_val, bnd, n_bnd, int_idx, n_vars)
            cvec = tuple(fu[i] - fv[i] for i in var_map)
            if cvec not in all_constraint_vecs:
                all_constraint_vecs[cvec] = set()
                n_new += 1
            all_constraint_vecs[cvec].add(n_val)

            # Collect comparison graph edges
            for j in range(2, n-3):
                edge = (u[j], u[j+1], v[j], v[j+1])
                comparison_edges.add(edge)
                if j + 1 <= n-4:
                    next_edge = (u[j+1], u[j+2], v[j+1], v[j+2])
                    comparison_transitions.add((edge, next_edge))

        dt = time.time() - t0
        print(f"  n={n_val}: {n_zero} zero-edges, "
              f"{n_new} new constraints ({dt:.1f}s)")

    total_unique = len(all_constraint_vecs)
    print(f"\n  Total unique constraints (φ=1): {total_unique}")
    print(f"  Comparison edges: {len(comparison_edges)}")
    print(f"  Comparison transitions: {len(comparison_transitions)}")

    # ═══════════════════════════════════════════════════════════
    # STEP 2: Solve the φ=1 sub-LP
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 2: Solve φ=1 sub-LP (joint n=5..12)")
    print("=" * 70)

    unique = list(all_constraint_vecs.keys())
    A = np.array(unique, dtype=float)
    ne = len(unique)

    c_obj = np.ones(2 * n_sub)
    A_split = np.hstack([-A, A])
    b_ub = -np.ones(ne)
    bounds = [(0, None)] * (2 * n_sub)

    t0 = time.time()
    res = linprog(c_obj, A_ub=A_split, b_ub=b_ub,
                  bounds=bounds, method='highs')
    dt = time.time() - t0

    if not res.success:
        print(f"  φ=1 sub-LP: INFEASIBLE ({dt:.1f}s)")
        print(f"  Cannot use uniform interior weights.")
        return

    w = res.x[:n_sub] - res.x[n_sub:]
    l1 = np.sum(np.abs(w))
    print(f"  φ=1 sub-LP: FEASIBLE! ||w||₁ = {l1:.2f} ({dt:.1f}s)")

    alpha = {}
    for (a, b), ki in int_pair_to_sub.items():
        alpha[(a, b)] = w[ki]
    alpha[(2, 1)] = 0

    print(f"\n  Interior weights (α):")
    for (a, b) in sorted(int_pair_to_sub.keys()):
        ki = int_pair_to_sub[(a, b)]
        print(f"    α({a},{b}) = {w[ki]:.4f}")

    # ═══════════════════════════════════════════════════════════
    # STEP 3: Check comparison cycles with GAIN convention
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 3: Comparison cycle check (GAIN convention)")
    print("=" * 70)
    print("G(e) = α(v-pair) - α(u-pair)  [GAIN = potential increase]")
    print("Need: all comparison cycles have Σ G ≥ 0")
    print("Equivalent to: Bellman-Ford with -G weights has no negative cycle")

    edge_gains = {}
    for e in comparison_edges:
        s0, s1, t0, t1 = e
        G = alpha.get((t0, t1), 0) - alpha.get((s0, s1), 0)
        edge_gains[e] = G

    n_pos = sum(1 for g in edge_gains.values() if g > 1e-9)
    n_neg = sum(1 for g in edge_gains.values() if g < -1e-9)
    n_zero = sum(1 for g in edge_gains.values() if abs(g) < 1e-9)
    print(f"\n  Gain values: {n_pos} positive, {n_neg} negative, {n_zero} zero")
    print(f"  Range: [{min(edge_gains.values()):.4f}, "
          f"{max(edge_gains.values()):.4f}]")

    # Bellman-Ford with NEGATIVE gain weights (to find negative gain cycles)
    nodes = list(comparison_edges)
    edges_bf = list(comparison_transitions)
    weights_bf = {}
    for e1, e2 in comparison_transitions:
        # Weight = -G(e1). Negative BF cycle ↔ positive gain cycle (WRONG for us)
        # We want to find cycles with Σ G < 0 (BAD for pumping)
        # So use weight = G(e1). BF finds negative cycle = Σ G < 0.
        weights_bf[(e1, e2)] = edge_gains[e1]

    print(f"\n  Bellman-Ford on {len(nodes)} nodes, {len(edges_bf)} edges...")
    t0 = time.time()
    has_neg, cycle = bellman_ford_negative_cycle(nodes, edges_bf, weights_bf)
    dt = time.time() - t0
    print(f"  Done ({dt:.3f}s)")

    if not has_neg:
        print(f"\n  *** ALL COMPARISON CYCLES HAVE NON-NEGATIVE GAIN ***")
        print(f"  The pumping argument works with φ=1!")
        print(f"  Combined with verified LP (n=5..12), this proves ALL n!")
    else:
        print(f"\n  NEGATIVE GAIN CYCLE FOUND")
        if cycle:
            total_g = sum(edge_gains[e1] for e1, e2 in cycle)
            print(f"  Cycle length: {len(cycle)}")
            print(f"  Total gain: {total_g:.4f}")
            for e1, e2 in cycle:
                print(f"    {e1}: G={edge_gains[e1]:.4f}")

    # ═══════════════════════════════════════════════════════════
    # STEP 4: Combined LP with cycle potential constraints
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 4: Combined LP (constraints + cycle potentials)")
    print("=" * 70)
    print("Find w, π such that:")
    print("  (a) w · Δf ≥ 1  for all zero-edges (n=5..12)")
    print("  (b) G(e) + π(succ) - π(e) ≥ 0  for all transitions")
    print("      where G(e) = α(tgt-pair) - α(src-pair)")
    print("  This ensures all comparison cycles have non-negative gain.")

    n_pot = len(nodes)
    node_to_idx = {nd: i for i, nd in enumerate(nodes)}

    # Build transition constraints: G(e1) + π(e2) - π(e1) ≥ 0
    # G(e1) = α(t0,t1) - α(s0,s1) where e1 = (s0,s1,t0,t1)
    # In terms of LP variables:
    # α(t0,t1) is either a boundary var or interior var
    # For interior: α(a,b) = w[int_pair_to_sub[(a,b)]]
    trans_rows = []
    for e1, e2 in comparison_transitions:
        row = [0.0] * (n_sub + n_pot)
        s0, s1, t0, t1 = e1

        # G(e1) = α(t0,t1) - α(s0,s1)
        # Source pair (s0,s1): in the u-config
        if (s0, s1) != (2, 1) and (s0, s1) in int_pair_to_sub:
            row[int_pair_to_sub[(s0, s1)]] -= 1  # -α(src)
        if (t0, t1) != (2, 1) and (t0, t1) in int_pair_to_sub:
            row[int_pair_to_sub[(t0, t1)]] += 1  # +α(tgt)

        # Potential: π(e2) - π(e1)
        row[n_sub + node_to_idx[e2]] += 1
        row[n_sub + node_to_idx[e1]] -= 1
        trans_rows.append(row)

    n_trans = len(trans_rows)

    # Original constraints (padded with zeros for potentials)
    A_orig = np.hstack([A, np.zeros((ne, n_pot))])

    # Transition constraints
    A_trans = np.array(trans_rows, dtype=float)

    # Combined: -(original) ≤ -1 and -(transition) ≤ 0
    # Use splitting for w: w = w⁺ - w⁻
    n_total_split = 2 * n_sub + n_pot

    # Original constraints with splitting
    A_orig_split = np.hstack([
        -A_orig[:, :n_sub], A_orig[:, :n_sub],  # w⁺, w⁻
        np.zeros((ne, n_pot))  # potentials don't appear
    ])
    b_orig = -np.ones(ne)

    # Transition constraints with splitting
    A_trans_split = np.hstack([
        -A_trans[:, :n_sub], A_trans[:, :n_sub],  # w⁺, w⁻
        -A_trans[:, n_sub:]  # potentials
    ])
    b_trans = np.zeros(n_trans)

    A_full = np.vstack([A_orig_split, A_trans_split])
    b_full = np.concatenate([b_orig, b_trans])

    # Objective: minimize ||w||₁
    c_obj = np.zeros(n_total_split)
    c_obj[:n_sub] = 1
    c_obj[n_sub:2*n_sub] = 1

    # Bounds: w⁺, w⁻ ≥ 0; π free
    bounds_split = ([(0, None)] * n_sub + [(0, None)] * n_sub
                    + [(None, None)] * n_pot)

    print(f"\n  LP size: {n_total_split} vars, {len(b_full)} constraints")
    print(f"    ({ne} original + {n_trans} transition)")
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
        print(f"\n  *** COMBINED LP: FEASIBLE! ***  ||w||₁ = {l1:.2f} ({dt:.1f}s)")

        # Extract and display interior weights
        alpha2 = {}
        for (a, b), ki in int_pair_to_sub.items():
            alpha2[(a, b)] = w2[ki]
        alpha2[(2, 1)] = 0

        print(f"\n  Interior weights with cycle constraints:")
        for (a, b) in sorted(int_pair_to_sub.keys()):
            ki = int_pair_to_sub[(a, b)]
            print(f"    α({a},{b}) = {w2[ki]:.4f}")

        # Verify: check all comparison cycles with new weights
        edge_gains2 = {}
        for e in comparison_edges:
            s0, s1, t0, t1 = e
            G = alpha2.get((t0, t1), 0) - alpha2.get((s0, s1), 0)
            edge_gains2[e] = G

        weights_bf2 = {}
        for e1, e2 in comparison_transitions:
            weights_bf2[(e1, e2)] = edge_gains2[e1]

        has_neg2, cyc2 = bellman_ford_negative_cycle(nodes, edges_bf, weights_bf2)
        print(f"\n  Negative gain cycle with new weights: {has_neg2}")

        # Verify original constraints
        gaps = A @ w2
        print(f"  Original constraint gaps: min={gaps.min():.4f}, "
              f"max={gaps.max():.4f}")

        # Verify transition (potential) constraints
        trans_gaps = A_trans[:, :n_sub] @ w2 + A_trans[:, n_sub:] @ pi
        print(f"  Transition gaps: min={trans_gaps.min():.4f}")

        # ═══════════════════════════════════════════════════════════
        # STEP 5: Test on larger n
        # ═══════════════════════════════════════════════════════════
        print()
        print("=" * 70)
        print("STEP 5: Verify combined weights on n=13, 14")
        print("=" * 70)

        for n_test in [13, 14]:
            print(f"\n  Testing n={n_test}...")
            t0 = time.time()
            exc_test, ms_test = build_excursion_graph(n_test)
            n_fail = 0
            n_total_test = 0
            n_new_cvec = 0
            new_comparison = 0

            for u, v in exc_test:
                n_t = n_test
                d21 = sum(j * (int(u[j] == 2 and u[(j+1)%n_t] == 1) -
                               int(v[j] == 2 and v[(j+1)%n_t] == 1))
                           for j in range(2, n_t-2))
                if d21 != 0:
                    continue
                n_total_test += 1

                fu = feat_vector_uniform(u, n_t, bnd, n_bnd, int_idx, n_vars)
                fv = feat_vector_uniform(v, n_t, bnd, n_bnd, int_idx, n_vars)
                cvec = tuple(fu[i] - fv[i] for i in var_map)

                if cvec not in all_constraint_vecs:
                    n_new_cvec += 1

                gap = sum(cvec[i] * w2[i] for i in range(n_sub))
                if gap < 1 - 1e-9:
                    n_fail += 1

                # Check for new comparison edges
                for j in range(2, n_t-3):
                    edge = (u[j], u[j+1], v[j], v[j+1])
                    if edge not in comparison_edges:
                        new_comparison += 1
                        comparison_edges.add(edge)

            dt = time.time() - t0
            print(f"    {n_fail}/{n_total_test} failures ({dt:.1f}s)")
            print(f"    New constraint vectors: {n_new_cvec}")
            print(f"    New comparison edges: {new_comparison}")

        # ═══════════════════════════════════════════════════════════
        # STEP 6: Constraint convergence analysis
        # ═══════════════════════════════════════════════════════════
        print()
        print("=" * 70)
        print("STEP 6: Constraint vector convergence (φ=1 vs φ=j)")
        print("=" * 70)

        cumulative_phi1 = set()
        cumulative_phij = set()

        for n_val in range(5, 13):
            exc_edges, ms = build_excursion_graph(n_val)
            n = n_val
            n_new_phi1 = 0
            n_new_phij = 0

            for u, v in exc_edges:
                d21 = sum(j * (int(u[j] == 2 and u[(j+1)%n] == 1) -
                               int(v[j] == 2 and v[(j+1)%n] == 1))
                           for j in range(2, n-2))
                if d21 != 0:
                    continue

                # φ=1 constraint vector
                fu1 = feat_vector_uniform(u, n_val, bnd, n_bnd, int_idx, n_vars)
                fv1 = feat_vector_uniform(v, n_val, bnd, n_bnd, int_idx, n_vars)
                cvec1 = tuple(fu1[i] - fv1[i] for i in var_map)
                if cvec1 not in cumulative_phi1:
                    cumulative_phi1.add(cvec1)
                    n_new_phi1 += 1

                # φ=j constraint vector (for comparison)
                fuj = [0] * n_vars
                fvj = [0] * n_vars
                for j in range(n):
                    j1 = (j + 1) % n
                    a_u, b_u = u[j], u[j1]
                    a_v, b_v = v[j], v[j1]
                    bnd_type = None
                    if j == 0: bnd_type = 0
                    elif j == 1: bnd_type = 1
                    elif j == n-3: bnd_type = 2
                    elif j == n-2: bnd_type = 3
                    elif j == n-1: bnd_type = 4
                    if bnd_type is not None:
                        ku = bnd[bnd_type].get((a_u, b_u))
                        kv = bnd[bnd_type].get((a_v, b_v))
                        if ku is not None: fuj[ku] += 1
                        if kv is not None: fvj[kv] += 1
                    else:
                        fuj[int_idx[(a_u, b_u)]] += j
                        fvj[int_idx[(a_v, b_v)]] += j
                cvecj = tuple(fuj[i] - fvj[i] for i in var_map)
                if cvecj not in cumulative_phij:
                    cumulative_phij.add(cvecj)
                    n_new_phij += 1

            print(f"  n={n_val}: φ=1 new={n_new_phi1:>6d} total={len(cumulative_phi1):>7d}  |  "
                  f"φ=j new={n_new_phij:>6d} total={len(cumulative_phij):>7d}")

    else:
        print(f"\n  Combined LP: INFEASIBLE ({dt:.1f}s)")
        print(f"  Cannot find weights with non-negative comparison cycles "
              f"while satisfying all constraints.")

        # ═══════════════════════════════════════════════════════════
        # STEP 4b: Try with fewer n values to find where it breaks
        # ═══════════════════════════════════════════════════════════
        print()
        print("  Testing which n causes infeasibility...")
        for n_max in range(5, 13):
            cvecs = set()
            for cvec, ns in all_constraint_vecs.items():
                if any(n <= n_max for n in ns):
                    cvecs.add(cvec)
            A_sub = np.array(list(cvecs), dtype=float)
            ne_sub = len(cvecs)

            A_orig_sub = np.hstack([A_sub, np.zeros((ne_sub, n_pot))])
            A_orig_split_sub = np.hstack([
                -A_orig_sub[:, :n_sub], A_orig_sub[:, :n_sub],
                np.zeros((ne_sub, n_pot))
            ])
            b_orig_sub = -np.ones(ne_sub)

            A_full_sub = np.vstack([A_orig_split_sub, A_trans_split])
            b_full_sub = np.concatenate([b_orig_sub, b_trans])

            res_sub = linprog(c_obj, A_ub=A_full_sub, b_ub=b_full_sub,
                               bounds=bounds_split, method='highs')
            status = "FEASIBLE" if res_sub.success else "INFEASIBLE"
            l1_sub = np.sum(np.abs(res_sub.x[:n_sub] - res_sub.x[n_sub:2*n_sub])) if res_sub.success else float('inf')
            print(f"    n≤{n_max}: {ne_sub} constraints → {status}"
                  f"{f' ||w||₁={l1_sub:.1f}' if res_sub.success else ''}")


if __name__ == '__main__':
    main()
