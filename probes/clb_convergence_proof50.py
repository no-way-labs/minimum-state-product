#!/usr/bin/env python3
"""
CONVERGENCE PROOF 50: Correct-Sign Gain Cycle Analysis (φ=j)
=============================================================

CRITICAL INSIGHT: proof48 checked if comparison cycles have h-sum ≥ 0
where h = α(u-pair) - α(v-pair). It found negative h-cycles and
concluded the pumping argument fails.

BUT: the pumping argument requires GAIN cycles to be non-negative:
G = α(v-pair) - α(u-pair) = -h

proof48's negative h-cycle had h-sum = -0.227, so G-sum = +0.227 > 0.
This is GOOD for pumping, not bad!

The question is: are there POSITIVE h-cycles (negative G-cycles)?
If all h-cycles have h-sum ≤ 0 (all G-cycles have G-sum ≥ 0),
then the pumping argument works with φ=j.

PLAN:
1. Solve joint LP with φ=j (known feasible)
2. Compute G(e) for each comparison edge
3. Run Bellman-Ford with weight = G to find negative-G cycles
4. If none found → analyze pumping implications
5. If found → build combined LP with CORRECT cycle constraints
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


def feat_vector_phij(c, n_val, bnd, n_bnd, int_idx, n_vars):
    """Feature vector with position weight φ=j."""
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
            r[k] += j  # φ=j position weight
    return r


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
    # STEP 1: Joint LP with φ=j (known feasible)
    # ═══════════════════════════════════════════════════════════
    print("=" * 70)
    print("STEP 1: Joint zero-edge sub-LP with φ=j (n=5..11)")
    print("=" * 70)

    all_constraint_vecs = set()
    comparison_edges = set()
    comparison_transitions = set()

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

            fu = feat_vector_phij(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector_phij(v, n_val, bnd, n_bnd, int_idx, n_vars)
            cvec = tuple(fu[i] - fv[i] for i in var_map)
            all_constraint_vecs.add(cvec)

            for j in range(2, n-3):
                edge = (u[j], u[j+1], v[j], v[j+1])
                comparison_edges.add(edge)
                if j + 1 <= n-4:
                    next_edge = (u[j+1], u[j+2], v[j+1], v[j+2])
                    comparison_transitions.add((edge, next_edge))

        dt = time.time() - t0
        print(f"  n={n_val}: done ({dt:.1f}s)")

    print(f"\n  Unique constraints: {len(all_constraint_vecs)}")
    print(f"  Comparison edges: {len(comparison_edges)}")
    print(f"  Comparison transitions: {len(comparison_transitions)}")

    unique = list(all_constraint_vecs)
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

    w = res.x[:n_sub] - res.x[n_sub:]
    l1 = np.sum(np.abs(w))
    print(f"\n  Joint LP (φ=j, n=5..11): FEASIBLE, ||w||₁ = {l1:.2f} ({dt:.1f}s)")

    alpha = {}
    for (a, b), ki in int_pair_to_sub.items():
        alpha[(a, b)] = w[ki]
    alpha[(2, 1)] = 0

    print(f"\n  Interior weights:")
    for (a, b) in sorted(int_pair_to_sub.keys()):
        ki = int_pair_to_sub[(a, b)]
        if abs(w[ki]) > 0.001:
            print(f"    α({a},{b}) = {w[ki]:.4f}")

    # ═══════════════════════════════════════════════════════════
    # STEP 2: Check comparison cycles with GAIN convention
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 2: Comparison graph cycle analysis (both directions)")
    print("=" * 70)
    print(f"For each comparison edge e = (s0,s1,t0,t1):")
    print(f"  h(e) = α(s0,s1) - α(t0,t1)  [proof48 convention]")
    print(f"  G(e) = α(t0,t1) - α(s0,s1)  [gain convention = -h]")

    edge_h = {}
    edge_G = {}
    for e in comparison_edges:
        s0, s1, t0, t1 = e
        h = alpha.get((s0, s1), 0) - alpha.get((t0, t1), 0)
        G = -h
        edge_h[e] = h
        edge_G[e] = G

    print(f"\n  h values: min={min(edge_h.values()):.4f}, "
          f"max={max(edge_h.values()):.4f}")
    print(f"  G values: min={min(edge_G.values()):.4f}, "
          f"max={max(edge_G.values()):.4f}")

    nodes = list(comparison_edges)
    edges_bf = list(comparison_transitions)

    # Check 1: Negative h-cycle (proof48 found this)
    weights_h = {}
    for e1, e2 in comparison_transitions:
        weights_h[(e1, e2)] = edge_h[e1]

    print(f"\n  Bellman-Ford with h weights (checking for negative h-cycles):")
    has_neg_h, cycle_h = bellman_ford_negative_cycle(nodes, edges_bf, weights_h)
    if has_neg_h:
        total_h = sum(edge_h[e1] for e1, e2 in cycle_h)
        print(f"    FOUND: h-sum = {total_h:.4f} (G-sum = {-total_h:.4f})")
        for e1, e2 in cycle_h:
            print(f"      {e1}: h={edge_h[e1]:.4f}, G={edge_G[e1]:.4f}")
    else:
        print(f"    None found (all h-cycles ≥ 0)")

    # Check 2: Negative G-cycle (THIS is what matters for pumping)
    weights_G = {}
    for e1, e2 in comparison_transitions:
        weights_G[(e1, e2)] = edge_G[e1]

    print(f"\n  Bellman-Ford with G weights (checking for NEGATIVE GAIN cycles):")
    has_neg_G, cycle_G = bellman_ford_negative_cycle(nodes, edges_bf, weights_G)
    if has_neg_G:
        total_G = sum(edge_G[e1] for e1, e2 in cycle_G)
        print(f"    FOUND: G-sum = {total_G:.4f}")
        print(f"    This means pumping argument FAILS (negative gain cycle).")
        for e1, e2 in cycle_G:
            print(f"      {e1}: G={edge_G[e1]:.4f}")
    else:
        print(f"    *** NO NEGATIVE GAIN CYCLES! ***")
        print(f"    All comparison cycles have G-sum ≥ 0!")
        print(f"    → Pumping argument viable (with φ=j position analysis).")

    # ═══════════════════════════════════════════════════════════
    # STEP 3: Enumerate ALL simple cycles and classify
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 3: All simple cycles in comparison graph")
    print("=" * 70)

    # Use Johnson's algorithm or DFS-based approach
    # Graph is small enough (59 nodes, 338 edges) for careful enumeration
    # But cycle count might be large - start with short cycles

    adj = defaultdict(set)
    for e1, e2 in comparison_transitions:
        adj[e1].add(e2)

    # Find all simple cycles up to length 10
    all_cycles = []
    for max_len in [3, 4, 5, 6]:
        count_at_len = 0
        for start in nodes:
            stack = [(start, [start], {start})]
            while stack:
                curr, path, visited = stack.pop()
                for nxt in adj.get(curr, set()):
                    if nxt == start and len(path) >= 2:
                        cycle = list(path)
                        # Normalize: start from smallest node
                        min_idx = cycle.index(min(cycle))
                        cycle = cycle[min_idx:] + cycle[:min_idx]
                        all_cycles.append(tuple(cycle))
                        count_at_len += 1
                    elif nxt not in visited and len(path) < max_len:
                        stack.append((nxt, path + [nxt], visited | {nxt}))

    # Deduplicate cycles
    unique_cycles = list(set(all_cycles))
    print(f"  Found {len(unique_cycles)} unique simple cycles (length ≤ 6)")

    # Classify by gain
    cycle_stats = []
    for cyc in unique_cycles:
        h_sum = sum(edge_h.get(cyc[i], 0) for i in range(len(cyc)))
        G_sum = -h_sum

        # Also compute the position-weighted offset: Σ k * G(e_k)
        G_offset = sum(k * edge_G.get(cyc[k], 0) for k in range(len(cyc)))

        cycle_stats.append((len(cyc), G_sum, G_offset, cyc))

    # Sort by G_sum
    cycle_stats.sort(key=lambda x: x[1])

    n_pos = sum(1 for _, g, _, _ in cycle_stats if g > 1e-9)
    n_neg = sum(1 for _, g, _, _ in cycle_stats if g < -1e-9)
    n_zero = sum(1 for _, g, _, _ in cycle_stats if abs(g) < 1e-9)
    print(f"\n  Gain classification: {n_pos} positive, {n_neg} negative, "
          f"{n_zero} zero")

    if n_neg > 0:
        print(f"\n  NEGATIVE gain cycles (most negative first):")
        for length, G_sum, G_off, cyc in cycle_stats[:10]:
            if G_sum < -1e-9:
                print(f"    len={length}: G={G_sum:.4f}, "
                      f"pos_offset={G_off:.4f}, cycle={cyc}")

    if n_zero > 0:
        print(f"\n  ZERO gain cycles:")
        for length, G_sum, G_off, cyc in cycle_stats:
            if abs(G_sum) < 1e-9:
                print(f"    len={length}: G={G_sum:.6f}, "
                      f"pos_offset={G_off:.4f}, cycle={cyc}")

    # All positive cycles
    if n_pos > 0:
        print(f"\n  Positive gain cycles (smallest first):")
        for length, G_sum, G_off, cyc in sorted(
                [(l, g, o, c) for l, g, o, c in cycle_stats if g > 1e-9],
                key=lambda x: x[1])[:10]:
            print(f"    len={length}: G={G_sum:.4f}, "
                  f"pos_offset={G_off:.4f}")

    # ═══════════════════════════════════════════════════════════
    # STEP 4: Combined LP with CORRECT cycle direction
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 4: Combined LP with CORRECT gain constraints")
    print("=" * 70)
    print("Find w, π such that:")
    print("  (a) w · Δf ≥ 1  for all zero-edges (n=5..11)")
    print("  (b) G(e) + π(succ) - π(e) ≥ 0  for all transitions")
    print("      where G(e) = α(tgt-pair) - α(src-pair)")
    print("  This ensures: for every comparison cycle, Σ G ≥ 0")

    n_pot = len(nodes)
    node_to_idx = {nd: i for i, nd in enumerate(nodes)}

    # Transition constraints: G(e1) + π(e2) - π(e1) ≥ 0
    # G(e1) = α(t0,t1) - α(s0,s1) for e1 = (s0,s1,t0,t1)
    trans_rows = []
    for e1, e2 in comparison_transitions:
        row = [0.0] * (n_sub + n_pot)
        s0, s1, t0, t1 = e1

        # G(e1) = α(t0,t1) - α(s0,s1)
        if (s0, s1) != (2, 1) and (s0, s1) in int_pair_to_sub:
            row[int_pair_to_sub[(s0, s1)]] -= 1  # -α(src_pair)
        if (t0, t1) != (2, 1) and (t0, t1) in int_pair_to_sub:
            row[int_pair_to_sub[(t0, t1)]] += 1  # +α(tgt_pair)

        # π(e2) - π(e1)
        row[n_sub + node_to_idx[e2]] += 1
        row[n_sub + node_to_idx[e1]] -= 1
        trans_rows.append(row)

    n_trans = len(trans_rows)
    A_trans = np.array(trans_rows, dtype=float)

    # Original constraints (padded with zeros for potentials)
    A_orig = np.hstack([A, np.zeros((ne, n_pot))])

    # Splitting: w = w⁺ - w⁻
    n_total_split = 2 * n_sub + n_pot

    A_orig_split = np.hstack([
        -A_orig[:, :n_sub], A_orig[:, :n_sub],
        np.zeros((ne, n_pot))
    ])
    b_orig = -np.ones(ne)

    A_trans_split = np.hstack([
        -A_trans[:, :n_sub], A_trans[:, :n_sub],
        -A_trans[:, n_sub:]
    ])
    b_trans = np.zeros(n_trans)

    A_full = np.vstack([A_orig_split, A_trans_split])
    b_full = np.concatenate([b_orig, b_trans])

    c_obj = np.zeros(n_total_split)
    c_obj[:n_sub] = 1
    c_obj[n_sub:2*n_sub] = 1

    bounds_split = ([(0, None)] * n_sub + [(0, None)] * n_sub
                    + [(None, None)] * n_pot)

    print(f"\n  LP: {n_total_split} vars ({n_sub} w⁺, {n_sub} w⁻, "
          f"{n_pot} π), {len(b_full)} constraints")
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

        alpha2 = {}
        for (a, b), ki in int_pair_to_sub.items():
            alpha2[(a, b)] = w2[ki]
        alpha2[(2, 1)] = 0

        print(f"\n  Interior weights with gain constraints:")
        for (a, b) in sorted(int_pair_to_sub.keys()):
            ki = int_pair_to_sub[(a, b)]
            if abs(w2[ki]) > 0.001:
                print(f"    α({a},{b}) = {w2[ki]:.4f}")

        # Verify no negative gain cycles
        edge_G2 = {}
        for e in comparison_edges:
            s0, s1, t0, t1 = e
            G = alpha2.get((t0, t1), 0) - alpha2.get((s0, s1), 0)
            edge_G2[e] = G

        weights_G2 = {}
        for e1, e2 in comparison_transitions:
            weights_G2[(e1, e2)] = edge_G2[e1]

        has_neg_G2, _ = bellman_ford_negative_cycle(nodes, edges_bf, weights_G2)
        print(f"\n  Negative gain cycle with combined weights: {has_neg_G2}")

        # Verify constraints
        gaps = A @ w2
        print(f"  Original constraint gaps: min={gaps.min():.4f}, "
              f"max={gaps.max():.4f}")

        # Verify transition constraints
        for e1, e2 in comparison_transitions:
            s0, s1, t0, t1 = e1
            G = alpha2.get((t0, t1), 0) - alpha2.get((s0, s1), 0)
            reduced = G + pi[node_to_idx[e2]] - pi[node_to_idx[e1]]
            if reduced < -1e-6:
                print(f"  WARNING: violated transition {e1}->{e2}: "
                      f"G={G:.4f}, reduced={reduced:.6f}")

        # ═══════════════════════════════════════════════════════════
        # STEP 5: Test on n=12
        # ═══════════════════════════════════════════════════════════
        print()
        print("=" * 70)
        print("STEP 5: Test combined weights on n=12, 13")
        print("=" * 70)

        for n_test in [12, 13]:
            print(f"\n  n={n_test}...")
            t0 = time.time()
            exc_test, _ = build_excursion_graph(n_test)
            n_t = n_test
            n_fail = 0
            n_total_test = 0

            for u, v in exc_test:
                d21 = sum(j * (int(u[j] == 2 and u[(j+1)%n_t] == 1) -
                               int(v[j] == 2 and v[(j+1)%n_t] == 1))
                           for j in range(2, n_t-2))
                if d21 != 0:
                    continue
                n_total_test += 1

                fu = feat_vector_phij(u, n_t, bnd, n_bnd, int_idx, n_vars)
                fv = feat_vector_phij(v, n_t, bnd, n_bnd, int_idx, n_vars)
                cvec = np.array([fu[i] - fv[i] for i in var_map], dtype=float)
                gap = cvec @ w2
                if gap < 1 - 1e-9:
                    n_fail += 1

            dt = time.time() - t0
            print(f"    {n_fail}/{n_total_test} failures ({dt:.1f}s)")

        # ═══════════════════════════════════════════════════════════
        # STEP 6: Implications for all-n proof
        # ═══════════════════════════════════════════════════════════
        print()
        print("=" * 70)
        print("STEP 6: Pumping argument analysis")
        print("=" * 70)

        # For each comparison cycle, compute:
        # 1. Unweighted G-sum (Σ G)
        # 2. Position-weighted offset (Σ k * G(e_k))
        # Cycle contribution at position j₀: j₀ * G_sum + G_offset
        # Need this ≥ 0 for all j₀ ≥ 2

        print("For φ=j pumping: cycle at position j₀ contributes")
        print("  j₀ * G_sum + G_offset")
        print("Need this ≥ 0 for all j₀ ≥ 2.")

        # Recompute cycle stats with new weights
        new_edge_G = edge_G2

        for cyc in unique_cycles:
            G_sum = sum(new_edge_G.get(cyc[i], 0) for i in range(len(cyc)))
            G_offset = sum(k * new_edge_G.get(cyc[k], 0)
                          for k in range(len(cyc)))

            # At j₀=2: 2*G_sum + G_offset
            min_contrib = 2 * G_sum + G_offset

            if abs(G_sum) > 1e-9 or abs(G_offset) > 1e-9:
                if G_sum > 1e-9:
                    # Positive gain: contributes more at higher positions
                    # Minimum at j₀=2
                    threshold = None
                    if G_offset < 0:
                        threshold = -G_offset / G_sum
                    print(f"  Cycle len={len(cyc)}: G_sum={G_sum:.4f}, "
                          f"G_off={G_offset:.4f}, "
                          f"min@j₀=2: {min_contrib:.4f}"
                          f"{f', threshold j₀≥{threshold:.1f}' if threshold and threshold > 2 else ''}")
                elif G_sum < -1e-9:
                    print(f"  Cycle len={len(cyc)}: G_sum={G_sum:.4f} "
                          f"*** NEGATIVE GAIN ***")
                else:
                    print(f"  Cycle len={len(cyc)}: G_sum≈0, "
                          f"G_off={G_offset:.4f}")

    else:
        print(f"\n  Combined LP: INFEASIBLE ({dt:.1f}s)")
        print(f"  Cannot simultaneously satisfy constraints + gain ≥ 0.")

        # Step 4b: Try WRONG direction to compare with proof48
        print()
        print("  For comparison: LP with h ≥ 0 (WRONG direction)...")
        trans_rows_wrong = []
        for e1, e2 in comparison_transitions:
            row = [0.0] * (n_sub + n_pot)
            s0, s1, t0, t1 = e1
            # h(e1) = α(s0,s1) - α(t0,t1)
            if (s0, s1) != (2, 1) and (s0, s1) in int_pair_to_sub:
                row[int_pair_to_sub[(s0, s1)]] += 1  # +α(src)
            if (t0, t1) != (2, 1) and (t0, t1) in int_pair_to_sub:
                row[int_pair_to_sub[(t0, t1)]] -= 1  # -α(tgt)
            row[n_sub + node_to_idx[e2]] += 1
            row[n_sub + node_to_idx[e1]] -= 1
            trans_rows_wrong.append(row)

        A_trans_wrong = np.array(trans_rows_wrong, dtype=float)
        A_trans_wrong_split = np.hstack([
            -A_trans_wrong[:, :n_sub], A_trans_wrong[:, :n_sub],
            -A_trans_wrong[:, n_sub:]
        ])

        A_full_wrong = np.vstack([A_orig_split, A_trans_wrong_split])
        b_full_wrong = np.concatenate([b_orig, np.zeros(n_trans)])

        res_wrong = linprog(c_obj, A_ub=A_full_wrong, b_ub=b_full_wrong,
                             bounds=bounds_split, method='highs')
        print(f"  Wrong direction: {'FEASIBLE' if res_wrong.success else 'INFEASIBLE'}")

        # Step 4c: Diagnose which n causes infeasibility
        print()
        print("  Which n causes infeasibility (correct direction)?")
        for n_max in [5, 6, 7, 8, 9, 10, 11]:
            # Only use constraints from n ≤ n_max
            cvecs_sub = set()
            for n_val in range(5, n_max + 1):
                exc_edges, ms = build_excursion_graph(n_val)
                n = n_val
                for u, v in exc_edges:
                    d21 = sum(j * (int(u[j] == 2 and u[(j+1)%n] == 1) -
                                   int(v[j] == 2 and v[(j+1)%n] == 1))
                               for j in range(2, n-2))
                    if d21 != 0:
                        continue
                    fu = feat_vector_phij(u, n_val, bnd, n_bnd, int_idx, n_vars)
                    fv = feat_vector_phij(v, n_val, bnd, n_bnd, int_idx, n_vars)
                    cvec = tuple(fu[i] - fv[i] for i in var_map)
                    cvecs_sub.add(cvec)

            A_sub = np.array(list(cvecs_sub), dtype=float)
            ne_sub = len(cvecs_sub)
            A_orig_sub = np.hstack([A_sub, np.zeros((ne_sub, n_pot))])
            A_orig_split_sub = np.hstack([
                -A_orig_sub[:, :n_sub], A_orig_sub[:, :n_sub],
                np.zeros((ne_sub, n_pot))
            ])

            A_full_sub = np.vstack([A_orig_split_sub, A_trans_split])
            b_full_sub = np.concatenate([-np.ones(ne_sub), b_trans])

            res_sub = linprog(c_obj, A_ub=A_full_sub, b_ub=b_full_sub,
                               bounds=bounds_split, method='highs')

            status = "FEASIBLE" if res_sub.success else "INFEASIBLE"
            if res_sub.success:
                w_sub = res_sub.x[:n_sub] - res_sub.x[n_sub:2*n_sub]
                l1 = np.sum(np.abs(w_sub))
                print(f"    n≤{n_max}: {ne_sub:>7d} constraints → "
                      f"{status} (||w||₁={l1:.1f})")
            else:
                print(f"    n≤{n_max}: {ne_sub:>7d} constraints → {status}")


if __name__ == '__main__':
    main()
