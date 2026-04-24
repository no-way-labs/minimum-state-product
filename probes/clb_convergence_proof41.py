#!/usr/bin/env python3
"""
CONVERGENCE PROOF 41: n=12 Verification & Weight Stability
============================================================

The joint 42-var sub-LP is FEASIBLE for n=5..11.
Joint weights: α(0,1)=12.841, α(2,0)=2.188, etc.

TEST 1: Compute n=12 zero-edge constraints
TEST 2: Test joint n=5..11 weights on n=12
TEST 3: If they fail, add n=12 to joint LP and resolve

Also: track how the weight vector changes when adding n=12.
If the weights stabilize (small perturbation), that suggests convergence.
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


def main():
    bnd, n_bnd = build_boundary_indices()
    int_idx = {}
    idx = n_bnd
    for a in range(3):
        for b in range(3):
            int_idx[(a, b)] = idx; idx += 1
    n_vars = idx  # 43
    k21 = int_idx[(2, 1)]
    var_map = [i for i in range(n_vars) if i != k21]
    n_sub = len(var_map)  # 42

    # Interior var indices and names
    int_var_indices = []
    int_pair_names = []
    for ki, orig_i in enumerate(var_map):
        if orig_i >= n_bnd:
            int_var_indices.append(ki)
            for (a, b), idx_val in int_idx.items():
                if idx_val == orig_i:
                    int_pair_names.append((a, b))
                    break

    print("=" * 70)
    print("STEP 1: Build joint LP from n=5..11")
    print("=" * 70)

    all_constraint_vecs = set()
    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val
        n_zero = 0
        for u, v in exc_edges:
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            if fu[k21] - fv[k21] == 0:
                cvec = tuple(fu[i] - fv[i] for i in var_map)
                all_constraint_vecs.add(cvec)
                n_zero += 1
        dt = time.time() - t0
        print(f"  n={n_val}: {n_zero} zero-edges, "
              f"{len(all_constraint_vecs)} cumulative unique ({dt:.1f}s)")

    print(f"\n  Total unique constraints from n=5..11: {len(all_constraint_vecs)}")

    # Solve joint LP
    unique_list = list(all_constraint_vecs)
    ne = len(unique_list)
    A = np.array(unique_list, dtype=float)

    c_obj = np.ones(2 * n_sub)
    A_split = np.hstack([-A, A])
    b_ub = -np.ones(ne)
    bounds = [(0, None)] * (2 * n_sub)
    res = linprog(c_obj, A_ub=A_split, b_ub=b_ub,
                  bounds=bounds, method='highs')

    w_joint_11 = res.x[:n_sub] - res.x[n_sub:]
    print(f"  Joint LP feasible: {res.success}, ||w||₁={np.sum(np.abs(w_joint_11)):.2f}")

    # ═══════════════════════════════════════════════════════════
    # STEP 2: Compute n=12 zero-edge constraints
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 2: n=12 zero-edge constraints")
    print("=" * 70)

    t0 = time.time()
    exc_edges_12, ms_12 = build_excursion_graph(12)
    n = 12
    dt_build = time.time() - t0
    print(f"  n=12 excursion graph: {len(exc_edges_12)} edges ({dt_build:.1f}s)")

    n12_constraints = []
    n12_unique = set()
    for u, v in exc_edges_12:
        fu = feat_vector(u, 12, bnd, n_bnd, int_idx, n_vars)
        fv = feat_vector(v, 12, bnd, n_bnd, int_idx, n_vars)
        if fu[k21] - fv[k21] == 0:
            cvec = tuple(fu[i] - fv[i] for i in var_map)
            n12_constraints.append(cvec)
            n12_unique.add(cvec)

    print(f"  n=12 zero-edges: {len(n12_constraints)}")
    print(f"  n=12 unique constraint vectors: {len(n12_unique)}")

    # How many are NEW (not seen in n=5..11)?
    new_vecs = n12_unique - all_constraint_vecs
    print(f"  New vectors not in n=5..11: {len(new_vecs)}")

    # ═══════════════════════════════════════════════════════════
    # STEP 3: Test joint weights on n=12
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 3: Test n=5..11 joint weights on n=12")
    print("=" * 70)

    A12 = np.array(list(n12_unique), dtype=float)
    gaps_12 = A12 @ w_joint_11
    n_fail = np.sum(gaps_12 < 1 - 1e-9)
    print(f"  n=12: {n_fail}/{len(n12_unique)} unique constraint failures "
          f"(min_gap={gaps_12.min():.3f})")

    if n_fail > 0:
        # Show the failing constraints
        fails = np.where(gaps_12 < 1 - 1e-9)[0]
        print(f"  Worst failures:")
        for idx_f in fails[:5]:
            gap = gaps_12[idx_f]
            cvec = list(n12_unique)[idx_f]
            # Decompose into boundary and interior
            bnd_part = cvec[:n_bnd]
            int_part = {int_pair_names[i]: cvec[int_var_indices[i]]
                        for i in range(len(int_var_indices))}
            print(f"    gap={gap:.3f}, int_Δ: "
                  + ", ".join(f"Δ{p}={v}" for p, v in int_part.items() if v != 0))

    # ═══════════════════════════════════════════════════════════
    # STEP 4: Joint LP including n=12
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 4: Joint LP for n=5..12")
    print("=" * 70)

    all_vecs_12 = all_constraint_vecs | n12_unique
    print(f"  Total unique constraints n=5..12: {len(all_vecs_12)}")

    A_all = np.array(list(all_vecs_12), dtype=float)
    ne = len(all_vecs_12)

    c_obj = np.ones(2 * n_sub)
    A_split = np.hstack([-A_all, A_all])
    b_ub = -np.ones(ne)
    bounds = [(0, None)] * (2 * n_sub)
    res12 = linprog(c_obj, A_ub=A_split, b_ub=b_ub,
                    bounds=bounds, method='highs')

    if res12.success:
        w_joint_12 = res12.x[:n_sub] - res12.x[n_sub:]
        l1 = np.sum(np.abs(w_joint_12))
        gaps_all = A_all @ w_joint_12
        print(f"  Joint LP (n=5..12): FEASIBLE (||w||₁={l1:.2f}, "
              f"min_gap={gaps_all.min():.3f})")

        int_w = {int_pair_names[i]: w_joint_12[int_var_indices[i]]
                 for i in range(len(int_var_indices))}
        print(f"  Interior weights: "
              + ", ".join(f"α{p}={v:.3f}" for p, v in
                          sorted(int_w.items()) if abs(v) > 0.001))

        # Weight change from n=5..11 to n=5..12
        dw = w_joint_12 - w_joint_11
        print(f"  Weight change ||Δw||₁ = {np.sum(np.abs(dw)):.3f}")
        print(f"  Weight change ||Δw||∞ = {np.max(np.abs(dw)):.3f}")

        # Interior weight comparison
        print(f"\n  Interior weight evolution:")
        for i in range(len(int_var_indices)):
            ki = int_var_indices[i]
            p = int_pair_names[i]
            v11 = w_joint_11[ki]
            v12 = w_joint_12[ki]
            if abs(v11) > 0.001 or abs(v12) > 0.001:
                print(f"    α{p}: n≤11={v11:.3f} → n≤12={v12:.3f} "
                      f"(Δ={v12-v11:+.3f})")
    else:
        print(f"  Joint LP (n=5..12): INFEASIBLE")


if __name__ == '__main__':
    main()
