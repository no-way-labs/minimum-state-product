#!/usr/bin/env python3
"""
CONVERGENCE PROOF 52: Iterated Peeling / Monotonicity Chain Extension
======================================================================

Pair/triple potentials with pumping are DEAD. New approach:

ITERATED PEELING:
  Layer 0: Δint(2,1) ≥ 0 on ALL excursion edges (PROVED)
  Layer 1: Δint(2,0) ≥ 0 on zero edges (verified n≤11)
  Layer 2: ??? ≥ 0 on double-zero edges
  ...
  Layer k: if no surviving edges, DAG proved

proof43 found "no more monotone pairs" at layer 2, but only checked
INDIVIDUAL unweighted pair counts. This script checks:
  (a) Position-weighted pair counts Δint_j(a,b) = Σ j·Δ(indicator)
  (b) LINEAR COMBINATIONS of pair counts (LP search)
  (c) TRIPLE window counts on double-zero edges
  (d) How many layers until elimination
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


def interior_pair_deltas(u, v, n):
    """Compute Δcount(a,b) for all 9 pair types in the interior.
    Interior = positions 2..n-3 (pairs at positions 2..n-4)."""
    delta = {}
    for a in range(3):
        for b in range(3):
            count_u = sum(1 for j in range(2, n-2) if u[j] == a and u[(j+1)%n] == b)
            count_v = sum(1 for j in range(2, n-2) if v[j] == a and v[(j+1)%n] == b)
            delta[(a, b)] = count_v - count_u
    return delta


def interior_pair_deltas_weighted(u, v, n):
    """Position-weighted Δint_j(a,b) = Σ_j j * Δ(indicator)."""
    delta = {}
    for a in range(3):
        for b in range(3):
            val = sum(j * (int(v[j] == a and v[(j+1)%n] == b) -
                          int(u[j] == a and u[(j+1)%n] == b))
                     for j in range(2, n-2))
            delta[(a, b)] = val
    return delta


def main():
    pairs = [(a, b) for a in range(3) for b in range(3)]

    # ═══════════════════════════════════════════════════════════
    # STEP 1: Collect layered edge data
    # ═══════════════════════════════════════════════════════════
    print("=" * 70)
    print("STEP 1: Collect excursion edges by layer")
    print("=" * 70)

    for n_val in [9, 10, 11]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        all_edges = []
        zero_edges = []
        double_zero_edges = []

        for u, v in exc_edges:
            deltas = interior_pair_deltas(u, v, n)
            deltas_w = interior_pair_deltas_weighted(u, v, n)

            all_edges.append((u, v, deltas, deltas_w))

            # Layer 0: Δint(2,1) unweighted
            d21 = deltas[(2, 1)]

            if d21 == 0:
                zero_edges.append((u, v, deltas, deltas_w))

                # Layer 1: Δint(2,0) unweighted
                d20 = deltas[(2, 0)]
                if d20 == 0:
                    double_zero_edges.append((u, v, deltas, deltas_w))

        dt = time.time() - t0
        print(f"\n  n={n_val}: ({dt:.1f}s)")
        print(f"    All excursion edges: {len(all_edges)}")
        print(f"    Zero edges (Δ(2,1)=0): {len(zero_edges)} "
              f"({100*len(zero_edges)/len(all_edges):.1f}%)")
        print(f"    Double-zero (Δ(2,0)=0 too): {len(double_zero_edges)} "
              f"({100*len(double_zero_edges)/len(all_edges):.1f}%)")

        # ───────────────────────────────────────────────
        # Layer 2: Check individual pair monotonicity
        # ───────────────────────────────────────────────
        print(f"\n    Layer 2: Individual pair monotonicity on double-zero edges:")
        for a, b in pairs:
            if (a, b) in [(2, 1), (2, 0)]:
                continue
            # Check unweighted
            mins = min(d[(a, b)] for _, _, d, _ in double_zero_edges) if double_zero_edges else 0
            maxs = max(d[(a, b)] for _, _, d, _ in double_zero_edges) if double_zero_edges else 0
            # Check weighted
            mins_w = min(dw[(a, b)] for _, _, _, dw in double_zero_edges) if double_zero_edges else 0
            maxs_w = max(dw[(a, b)] for _, _, _, dw in double_zero_edges) if double_zero_edges else 0

            monotone = "✓ MONOTONE" if mins >= 0 and maxs > 0 else ""
            monotone_w = "✓ W-MONO" if mins_w >= 0 and maxs_w > 0 else ""
            if mins >= 0 or mins_w >= 0:
                print(f"      ({a},{b}): unwt [{mins:+d}, {maxs:+d}]  "
                      f"wt [{mins_w:+d}, {maxs_w:+d}]  {monotone} {monotone_w}")

        # Print all pairs (including non-monotone)
        print(f"\n    All pairs on double-zero edges:")
        for a, b in pairs:
            if (a, b) in [(2, 1), (2, 0)]:
                continue
            mins = min(d[(a, b)] for _, _, d, _ in double_zero_edges) if double_zero_edges else 0
            maxs = max(d[(a, b)] for _, _, d, _ in double_zero_edges) if double_zero_edges else 0
            mins_w = min(dw[(a, b)] for _, _, _, dw in double_zero_edges) if double_zero_edges else 0
            maxs_w = max(dw[(a, b)] for _, _, _, dw in double_zero_edges) if double_zero_edges else 0
            print(f"      ({a},{b}): unwt [{mins:>3d}, {maxs:>3d}]  "
                  f"wt [{mins_w:>4d}, {maxs_w:>4d}]")

    # ═══════════════════════════════════════════════════════════
    # STEP 2: LP search for layer-2 monotone COMBINATION
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 2: LP search for monotone combination on double-zero edges")
    print("=" * 70)

    for n_val in [9, 10, 11]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        # Collect double-zero Δcount vectors (excluding (2,1) and (2,0))
        remaining_pairs = [(a, b) for a, b in pairs if (a, b) not in [(2, 1), (2, 0)]]
        n_rp = len(remaining_pairs)

        dz_vectors = []
        dz_vectors_w = []
        for u, v in exc_edges:
            deltas = interior_pair_deltas(u, v, n)
            if deltas[(2, 1)] != 0 or deltas[(2, 0)] != 0:
                continue
            deltas_w = interior_pair_deltas_weighted(u, v, n)

            vec = tuple(deltas[p] for p in remaining_pairs)
            vec_w = tuple(deltas_w[p] for p in remaining_pairs)
            dz_vectors.append(vec)
            dz_vectors_w.append(vec_w)

        n_dz = len(dz_vectors)
        dt = time.time() - t0

        # UNWEIGHTED: find λ s.t. A λ ≥ 0 with some strict
        # Maximize min gap: max δ s.t. A λ ≥ δ, ||λ||₁ ≤ 1
        # LP: min -δ s.t. A λ - δ·1 ≥ 0, ||λ||₁ ≤ 1
        # Use splitting: λ = λ⁺ - λ⁻

        unique_vecs = list(set(dz_vectors))
        A_dz = np.array(unique_vecs, dtype=float) if unique_vecs else np.zeros((0, n_rp))
        n_unique = len(unique_vecs)

        print(f"\n  n={n_val}: {n_dz} double-zero edges, "
              f"{n_unique} unique vectors ({dt:.1f}s)")

        if n_unique > 0:
            # LP: max δ s.t. A (λ⁺ - λ⁻) ≥ δ, sum(λ⁺ + λ⁻) ≤ 1
            # Variables: [λ⁺ (n_rp), λ⁻ (n_rp), δ (1)]
            n_lp = 2 * n_rp + 1

            # Objective: maximize δ → minimize -δ
            c_lp = np.zeros(n_lp)
            c_lp[-1] = -1  # minimize -δ

            # Constraints: A(λ⁺-λ⁻) - δ ≥ 0 → -(A(λ⁺-λ⁻) - δ) ≤ 0
            A_main = np.hstack([
                -A_dz, A_dz,  # -(λ⁺ - λ⁻)
                np.ones((n_unique, 1))  # +δ
            ])

            # ||λ||₁ ≤ 1: sum(λ⁺ + λ⁻) ≤ 1
            A_norm = np.zeros((1, n_lp))
            A_norm[0, :n_rp] = 1  # λ⁺
            A_norm[0, n_rp:2*n_rp] = 1  # λ⁻

            A_full = np.vstack([A_main, A_norm])
            b_full = np.concatenate([np.zeros(n_unique), [1]])

            bounds_lp = [(0, None)] * (2 * n_rp) + [(None, None)]  # δ free

            res = linprog(c_lp, A_ub=A_full, b_ub=b_full,
                          bounds=bounds_lp, method='highs')

            if res.success:
                lam_plus = res.x[:n_rp]
                lam_minus = res.x[n_rp:2*n_rp]
                lam = lam_plus - lam_minus
                delta_opt = res.x[-1]

                n_elim = sum(1 for vec in dz_vectors
                             if sum(lam[i] * vec[i] for i in range(n_rp)) > 1e-9)

                print(f"    Unweighted LP: δ_opt = {delta_opt:.4f}")
                print(f"    Eliminates: {n_elim}/{n_dz} "
                      f"({100*n_elim/n_dz:.1f}%)")
                if abs(delta_opt) > 1e-9:
                    print(f"    λ weights:")
                    for i, p in enumerate(remaining_pairs):
                        if abs(lam[i]) > 0.001:
                            print(f"      λ({p[0]},{p[1]}) = {lam[i]:.4f}")

            # WEIGHTED: same but with weighted vectors
            unique_vecs_w = list(set(dz_vectors_w))
            A_dz_w = np.array(unique_vecs_w, dtype=float) if unique_vecs_w else np.zeros((0, n_rp))
            n_unique_w = len(unique_vecs_w)

            if n_unique_w > 0:
                A_main_w = np.hstack([
                    -A_dz_w, A_dz_w,
                    np.ones((n_unique_w, 1))
                ])
                A_norm_w = np.zeros((1, n_lp))
                A_norm_w[0, :n_rp] = 1
                A_norm_w[0, n_rp:2*n_rp] = 1

                A_full_w = np.vstack([A_main_w, A_norm_w])
                b_full_w = np.concatenate([np.zeros(n_unique_w), [1]])

                res_w = linprog(c_lp, A_ub=A_full_w, b_ub=b_full_w,
                                bounds=bounds_lp, method='highs')

                if res_w.success:
                    lam_w = res_w.x[:n_rp] - res_w.x[n_rp:2*n_rp]
                    delta_w = res_w.x[-1]

                    n_elim_w = sum(1 for vec in dz_vectors_w
                                   if sum(lam_w[i] * vec[i] for i in range(n_rp)) > 1e-9)

                    print(f"    Weighted LP: δ_opt = {delta_w:.4f}")
                    print(f"    Eliminates: {n_elim_w}/{n_dz} "
                          f"({100*n_elim_w/n_dz:.1f}%)")

    # ═══════════════════════════════════════════════════════════
    # STEP 3: Full iterated peeling (unweighted pair counts)
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 3: Full iterated peeling")
    print("=" * 70)

    for n_val in [9, 10]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        # Start: all excursion edges
        surviving = []
        for u, v in exc_edges:
            deltas = interior_pair_deltas(u, v, n)
            surviving.append((u, v, deltas))

        print(f"\n  n={n_val}: {len(surviving)} excursion edges")

        layer = 0
        while surviving:
            # Find the best single monotone pair
            best_pair = None
            best_elim = 0

            for a, b in pairs:
                min_d = min(d[(a, b)] for _, _, d in surviving)
                if min_d >= 0:
                    n_strict = sum(1 for _, _, d in surviving if d[(a, b)] > 0)
                    if n_strict > best_elim:
                        best_elim = n_strict
                        best_pair = (a, b)

            if best_pair is None or best_elim == 0:
                # Try LP for combination
                remaining = [(a, b) for a, b in pairs]
                n_rp = len(remaining)
                vecs = [tuple(d[p] for p in remaining) for _, _, d in surviving]
                unique_vecs = list(set(vecs))
                A_mat = np.array(unique_vecs, dtype=float)
                n_u = len(unique_vecs)

                n_lp = 2 * n_rp + 1
                c_lp = np.zeros(n_lp)
                c_lp[-1] = -1

                A_main = np.hstack([-A_mat, A_mat, np.ones((n_u, 1))])
                A_norm = np.zeros((1, n_lp))
                A_norm[0, :n_rp] = 1
                A_norm[0, n_rp:2*n_rp] = 1
                A_full = np.vstack([A_main, A_norm])
                b_full = np.concatenate([np.zeros(n_u), [1]])
                bounds_lp = [(0, None)] * (2 * n_rp) + [(None, None)]

                res = linprog(c_lp, A_ub=A_full, b_ub=b_full,
                              bounds=bounds_lp, method='highs')

                if res.success and res.x[-1] > 1e-9:
                    lam = res.x[:n_rp] - res.x[n_rp:2*n_rp]
                    n_elim = sum(1 for v in vecs
                                 if sum(lam[i] * v[i] for i in range(n_rp)) > 1e-9)
                    # Peel using this combination
                    new_surviving = [(u, v, d) for (u, v, d), vec in zip(surviving, vecs)
                                     if sum(lam[i] * vec[i] for i in range(n_rp)) <= 1e-9]
                    active = [f"λ·Δ (δ={res.x[-1]:.4f})"]
                    print(f"    Layer {layer}: LP combo eliminates "
                          f"{len(surviving) - len(new_surviving)}/{len(surviving)}, "
                          f"{len(new_surviving)} remain")
                    surviving = new_surviving
                    layer += 1
                else:
                    print(f"    Layer {layer}: STUCK at {len(surviving)} edges "
                          f"(no monotone quantity)")
                    break
            else:
                # Peel using the best pair
                new_surviving = [(u, v, d) for u, v, d in surviving
                                 if d[best_pair] == 0]
                print(f"    Layer {layer}: Δ{best_pair} eliminates "
                      f"{len(surviving) - len(new_surviving)}/{len(surviving)}, "
                      f"{len(new_surviving)} remain")
                surviving = new_surviving
                layer += 1

        if not surviving:
            print(f"    *** ALL EDGES ELIMINATED in {layer} layers! ***")

        dt = time.time() - t0
        print(f"    ({dt:.1f}s)")

    # ═══════════════════════════════════════════════════════════
    # STEP 4: Direct cycle search in double-zero subgraph
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 4: Direct cycle search in surviving subgraph")
    print("=" * 70)

    for n_val in [9, 10]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        # Build adjacency for double-zero subgraph
        adj = defaultdict(list)
        dz_nodes = set()
        for u, v in exc_edges:
            deltas = interior_pair_deltas(u, v, n)
            if deltas[(2, 1)] == 0 and deltas[(2, 0)] == 0:
                adj[u].append(v)
                dz_nodes.add(u)
                dz_nodes.add(v)

        # Check for cycles using DFS
        # Tarjan's SCC algorithm
        index_counter = [0]
        stack = []
        on_stack = set()
        index_map = {}
        lowlink = {}
        sccs = []

        def strongconnect(v):
            index_map[v] = index_counter[0]
            lowlink[v] = index_counter[0]
            index_counter[0] += 1
            stack.append(v)
            on_stack.add(v)

            for w in adj.get(v, []):
                if w not in index_map:
                    strongconnect(w)
                    lowlink[v] = min(lowlink[v], lowlink[w])
                elif w in on_stack:
                    lowlink[v] = min(lowlink[v], index_map[w])

            if lowlink[v] == index_map[v]:
                scc = []
                while True:
                    w = stack.pop()
                    on_stack.discard(w)
                    scc.append(w)
                    if w == v:
                        break
                if len(scc) > 1:
                    sccs.append(scc)

        sys.setrecursionlimit(1000000)
        for node in dz_nodes:
            if node not in index_map:
                strongconnect(node)

        dt = time.time() - t0
        print(f"\n  n={n_val}: {len(dz_nodes)} double-zero nodes, "
              f"{sum(len(adj[n]) for n in adj)} edges ({dt:.1f}s)")
        if sccs:
            print(f"    NON-TRIVIAL SCCs: {len(sccs)} "
                  f"(sizes: {sorted([len(s) for s in sccs], reverse=True)[:5]})")
        else:
            print(f"    *** NO CYCLES in double-zero subgraph! ***")
            print(f"    → Double-zero subgraph is a DAG!")


if __name__ == '__main__':
    main()
