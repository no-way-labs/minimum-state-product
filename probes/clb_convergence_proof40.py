#!/usr/bin/env python3
"""
CONVERGENCE PROOF 40: Cross-n Weight Transfer & Joint Sub-LP
=============================================================

KEY QUESTION: The 42-var zero-edge sub-LP (α(2,1)=0) is feasible per-n.
Do the weights generalize across n values?

TEST 1: Solve for n=9, test on n=10,11
TEST 2: Joint 42-var LP across n=5..10
TEST 3: Analyze WHY boundary-only fails — what interior directions matter?
TEST 4: Extract and compare per-n weights
"""

import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict
import numpy as np
from scipy.optimize import linprog


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


def get_zero_edge_constraints(n_val, bnd, n_bnd, int_idx, n_vars, k21):
    exc_edges, ms = build_excursion_graph(n_val)
    constraints = []
    for u, v in exc_edges:
        fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
        fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
        if fu[k21] - fv[k21] == 0:
            # Full 43-var constraint, but with k21 removed → 42 vars
            constraints.append(tuple(fu[i] - fv[i]
                                     for i in range(n_vars) if i != k21))
    return constraints


def main():
    bnd, n_bnd = build_boundary_indices()
    int_idx = {}
    idx = n_bnd
    for a in range(3):
        for b in range(3):
            int_idx[(a, b)] = idx; idx += 1
    n_vars = idx  # 43
    k21 = int_idx[(2, 1)]

    # Variable map (excluding k21)
    var_map = [i for i in range(n_vars) if i != k21]
    n_sub = len(var_map)  # 42

    # Interior variable indices in the sub-problem
    int_var_indices = []
    int_pair_names = []
    for ki, orig_i in enumerate(var_map):
        if orig_i >= n_bnd:
            int_var_indices.append(ki)
            # Find which pair this is
            for (a, b), idx_val in int_idx.items():
                if idx_val == orig_i:
                    int_pair_names.append((a, b))
                    break

    print("=" * 70)
    print("TEST 1: Per-n sub-LP weights & cross-n testing")
    print("=" * 70)

    per_n_weights = {}
    per_n_constraints = {}

    for n_val in range(5, 12):
        t0 = time.time()
        constraints = get_zero_edge_constraints(n_val, bnd, n_bnd, int_idx,
                                                 n_vars, k21)
        per_n_constraints[n_val] = constraints

        if not constraints:
            print(f"  n={n_val}: no zero edges")
            continue

        ne = len(constraints)
        A = np.array(constraints, dtype=float)

        # L1-minimal solution
        c_obj = np.ones(2 * n_sub)
        A_split = np.hstack([-A, A])
        b_ub = -np.ones(ne)
        bounds = [(0, None)] * (2 * n_sub)
        res = linprog(c_obj, A_ub=A_split, b_ub=b_ub,
                      bounds=bounds, method='highs')

        dt = time.time() - t0
        if res.success:
            w = res.x[:n_sub] - res.x[n_sub:]
            per_n_weights[n_val] = w
            gaps = A @ w
            l1 = np.sum(np.abs(w))

            # Interior weight values
            int_w = {int_pair_names[i]: w[int_var_indices[i]]
                     for i in range(len(int_var_indices))}
            print(f"  n={n_val}: {ne} zero-edges, ||w||₁={l1:.2f}, "
                  f"min_gap={gaps.min():.3f} ({dt:.1f}s)")
            print(f"    Interior weights: "
                  + ", ".join(f"α{p}={v:.3f}" for p, v in
                              sorted(int_w.items()) if abs(v) > 0.001))
        else:
            print(f"  n={n_val}: INFEASIBLE ({dt:.1f}s)")

    # Cross-n testing
    print()
    print("=" * 70)
    print("TEST 2: Cross-n weight transfer")
    print("=" * 70)

    for n_src in [7, 8, 9, 10]:
        if n_src not in per_n_weights:
            continue
        w = per_n_weights[n_src]
        print(f"\n  Weights from n={n_src}:")
        for n_tgt in range(5, 12):
            if n_tgt not in per_n_constraints:
                continue
            constraints = per_n_constraints[n_tgt]
            if not constraints:
                continue
            A = np.array(constraints, dtype=float)
            gaps = A @ w
            n_fail = np.sum(gaps < 1 - 1e-9)
            print(f"    → n={n_tgt}: {n_fail}/{len(constraints)} failures "
                  f"(min_gap={gaps.min():.3f})")

    # ═══════════════════════════════════════════════════════════
    # TEST 3: Joint 42-var LP across all n
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("TEST 3: Joint 42-var sub-LP for n=5..11")
    print("=" * 70)

    all_constraints = []
    for n_val in range(5, 12):
        all_constraints.extend(per_n_constraints.get(n_val, []))

    # Deduplicate
    unique = list(set(all_constraints))
    print(f"  Total constraints: {len(all_constraints)}")
    print(f"  Unique constraint vectors: {len(unique)}")

    A = np.array(unique, dtype=float)
    ne = len(unique)

    # L1-minimal
    c_obj = np.ones(2 * n_sub)
    A_split = np.hstack([-A, A])
    b_ub = -np.ones(ne)
    bounds = [(0, None)] * (2 * n_sub)
    res = linprog(c_obj, A_ub=A_split, b_ub=b_ub,
                  bounds=bounds, method='highs')

    if res.success:
        w = res.x[:n_sub] - res.x[n_sub:]
        gaps = A @ w
        l1 = np.sum(np.abs(w))
        print(f"  Joint LP: FEASIBLE (||w||₁={l1:.2f}, min_gap={gaps.min():.3f})")

        int_w = {int_pair_names[i]: w[int_var_indices[i]]
                 for i in range(len(int_var_indices))}
        print(f"  Interior weights: "
              + ", ".join(f"α{p}={v:.3f}" for p, v in
                          sorted(int_w.items()) if abs(v) > 0.001))

        # Print boundary weight summary
        print(f"  Boundary weights (non-zero):")
        bnd_labels = []
        for bt in range(5):
            name = ["T_bot", "T_low", "T_midR", "T_highL", "T_top"][bt]
            for (a, b), idx_val in bnd[bt].items():
                ki = var_map.index(idx_val) if idx_val in var_map else None
                if ki is not None and abs(w[ki]) > 0.001:
                    bnd_labels.append(f"    {name}({a},{b}): {w[ki]:.3f}")
        for bl in bnd_labels:
            print(bl)
    else:
        print(f"  Joint LP: INFEASIBLE")

    # ═══════════════════════════════════════════════════════════
    # TEST 4: Analyze the infeasible direction
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("TEST 4: Which constraints conflict across n?")
    print("=" * 70)

    # Try incremental: n=5..k, find where infeasibility starts
    for k in range(5, 12):
        constraints_k = []
        for n_val in range(5, k + 1):
            constraints_k.extend(per_n_constraints.get(n_val, []))
        unique_k = list(set(constraints_k))
        A = np.array(unique_k, dtype=float)
        ne = len(unique_k)

        c_obj = np.zeros(n_sub)
        res = linprog(c_obj, A_ub=-A, b_ub=-np.ones(ne),
                      bounds=[(None, None)] * n_sub, method='highs')

        status = "FEASIBLE" if res.success else "INFEASIBLE"
        print(f"  n=5..{k}: {ne} unique constraints → {status}")


if __name__ == '__main__':
    main()
