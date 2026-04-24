#!/usr/bin/env python3
"""
CONVERGENCE PROOF 31: Verify Universal Pair Potential on Larger n
================================================================

From proof30: Joint LP with φ=j is FEASIBLE for n=5..9.
This script:
1. Extracts the universal weights from the joint LP
2. Verifies them on n=10, 11, 12 (without adding to LP)
3. Runs L1-minimal joint LP for cleaner weights
4. Tests if a SINGLE set of rounded integer weights works
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict
import numpy as np
from scipy.optimize import linprog
import time


def frontier_type(a, b):
    if a == b:
        return 0
    return (b - a) % 3


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
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c)
                lst[i] = out
                succ = tuple(lst)
                if succ in bad_set:
                    dfc = delta_fc(L, S, R, out)
                    if dfc <= 0:
                        dfc_le0_adj[c].append(succ)
                    if out != L and out != R:
                        anom_edges.append((c, succ, i, dfc))

    anom_sources = set(c for c, _, _, _ in anom_edges)
    anom_target_map = defaultdict(list)
    for c, succ, i, dfc in anom_edges:
        anom_target_map[succ].append(c)

    exc_edges = set()
    for b in set(s for _, s, _, _ in anom_edges):
        visited = set()
        queue = [b]
        visited.add(b)
        head = 0
        while head < len(queue):
            node = queue[head]
            head += 1
            if node in anom_sources:
                for src in anom_target_map.get(b, []):
                    exc_edges.add((src, node))
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt)
                    queue.append(nxt)

    return list(exc_edges), ms


def build_boundary_indices():
    idx = 0
    bnd_0 = {}
    for a in range(2):
        for b in range(3):
            bnd_0[(a, b)] = idx; idx += 1
    bnd_1 = {}
    for a in range(3):
        for b in range(3):
            bnd_1[(a, b)] = idx; idx += 1
    bnd_2 = {}
    for a in range(3):
        for b in range(3):
            bnd_2[(a, b)] = idx; idx += 1
    bnd_3 = {}
    for a in range(3):
        for b in range(2):
            bnd_3[(a, b)] = idx; idx += 1
    bnd_4 = {}
    for a in range(2):
        for b in range(2):
            bnd_4[(a, b)] = idx; idx += 1
    n_bnd = idx
    return bnd_0, bnd_1, bnd_2, bnd_3, bnd_4, n_bnd


def feat_linear(c, n_val, bnd_0, bnd_1, bnd_2, bnd_3, bnd_4, n_bnd,
                int_idx):
    """Feature vector for linear parameterization φ=j."""
    n = n_val
    r = {}
    for j in range(n):
        j1 = (j + 1) % n
        a, b = c[j], c[j1]
        if j == 0:
            k = bnd_0.get((a, b))
        elif j == 1:
            k = bnd_1.get((a, b))
        elif j == n - 3:
            k = bnd_2.get((a, b))
        elif j == n - 2:
            k = bnd_3.get((a, b))
        elif j == n - 1:
            k = bnd_4.get((a, b))
        else:
            # Interior
            k = None
            vi = int_idx.get((a, b))
            if vi is not None:
                r[vi] = r.get(vi, 0) + j
        if k is not None:
            r[k] = r.get(k, 0) + 1
    return r


def compute_potential(c, n_val, weights, bnd_0, bnd_1, bnd_2, bnd_3,
                      bnd_4, int_idx):
    """Compute pair potential value for config c."""
    n = n_val
    total = 0.0
    for j in range(n):
        j1 = (j + 1) % n
        a, b = c[j], c[j1]
        if j == 0:
            k = bnd_0.get((a, b))
            if k is not None:
                total += weights[k]
        elif j == 1:
            k = bnd_1.get((a, b))
            if k is not None:
                total += weights[k]
        elif j == n - 3:
            k = bnd_2.get((a, b))
            if k is not None:
                total += weights[k]
        elif j == n - 2:
            k = bnd_3.get((a, b))
            if k is not None:
                total += weights[k]
        elif j == n - 1:
            k = bnd_4.get((a, b))
            if k is not None:
                total += weights[k]
        else:
            vi = int_idx.get((a, b))
            if vi is not None:
                total += weights[vi] * j
    return total


def joint_lp_l1(n_values):
    """L1-minimal joint LP across multiple n values."""
    bnd_0, bnd_1, bnd_2, bnd_3, bnd_4, n_bnd = build_boundary_indices()

    int_idx = {}
    idx = n_bnd
    for a in range(3):
        for b in range(3):
            int_idx[(a, b)] = idx
            idx += 1
    n_vars = idx  # 34 + 9 = 43

    # Collect edges
    all_edges = []
    for n_val in n_values:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        dt = time.time() - t0
        print(f"  n={n_val}: {len(exc_edges)} exc edges ({dt:.1f}s)")
        for u, v in exc_edges:
            all_edges.append((u, v, n_val))

    ne = len(all_edges)
    print(f"  Total: {ne} constraints, {n_vars} variables")

    # Build constraint matrix
    A = np.zeros((ne, n_vars))
    for ei, (u, v, n_val) in enumerate(all_edges):
        fu = feat_linear(u, n_val, bnd_0, bnd_1, bnd_2, bnd_3, bnd_4,
                         n_bnd, int_idx)
        fv = feat_linear(v, n_val, bnd_0, bnd_1, bnd_2, bnd_3, bnd_4,
                         n_bnd, int_idx)
        for k, val in fu.items():
            A[ei, k] += val
        for k, val in fv.items():
            A[ei, k] -= val

    # L1-minimal: min Σ(w+ + w-) s.t. A(w+ - w-) ≥ 1
    c_obj = np.ones(2 * n_vars)
    A_split = np.hstack([-A, A])
    b_ub = -np.ones(ne)
    bounds = [(0, None)] * (2 * n_vars)

    print(f"  Solving L1-minimal LP...")
    t0 = time.time()
    res = linprog(c_obj, A_ub=A_split, b_ub=b_ub,
                  bounds=bounds, method='highs')
    dt = time.time() - t0
    print(f"  LP solve time: {dt:.1f}s")

    if not res.success:
        print(f"  L1-minimal: INFEASIBLE")
        return None, None, None

    w = res.x[:n_vars] - res.x[n_vars:]
    gaps = A @ w
    l1 = np.sum(np.abs(w))
    print(f"  L1-minimal: FEASIBLE, ||w||₁={l1:.2f}, "
          f"min_gap={gaps.min():.3f}")

    # Also solve plain feasibility to get a different solution
    c_obj2 = np.zeros(n_vars)
    res2 = linprog(c_obj2, A_ub=-A, b_ub=-np.ones(ne),
                   bounds=[(None, None)] * n_vars, method='highs')
    w2 = res2.x if res2.success else None

    return w, w2, (bnd_0, bnd_1, bnd_2, bnd_3, bnd_4, n_bnd, int_idx,
                   n_vars)


def verify_weights(w, n_val, bnd_0, bnd_1, bnd_2, bnd_3, bnd_4,
                   int_idx):
    """Verify weights on excursion graph for a specific n."""
    exc_edges, ms = build_excursion_graph(n_val)
    violations = 0
    min_gap = float('inf')
    for u, v in exc_edges:
        phi_u = compute_potential(u, n_val, w, bnd_0, bnd_1, bnd_2,
                                  bnd_3, bnd_4, int_idx)
        phi_v = compute_potential(v, n_val, w, bnd_0, bnd_1, bnd_2,
                                  bnd_3, bnd_4, int_idx)
        gap = phi_u - phi_v
        min_gap = min(min_gap, gap)
        if gap <= 0:
            violations += 1
    return violations, len(exc_edges), min_gap


def main():
    print(f"{'=' * 65}")
    print(f"PHASE 1: L1-minimal joint LP for n=5..9")
    print(f"{'=' * 65}")

    w_l1, w_feas, info = joint_lp_l1(list(range(5, 10)))
    if w_l1 is None:
        print("FAILED")
        return

    bnd_0, bnd_1, bnd_2, bnd_3, bnd_4, n_bnd, int_idx, n_vars = info

    # Print L1 weights
    print(f"\n  L1-minimal weights:")
    bnd_maps = [
        ("T_bot—T_low", bnd_0),
        ("T_low—T_mid", bnd_1),
        ("T_mid—T_high", bnd_2),
        ("T_high—T_top", bnd_3),
        ("T_top—T_bot", bnd_4),
    ]
    for name, bnd in bnd_maps:
        for (a, b), idx in sorted(bnd.items()):
            if abs(w_l1[idx]) > 0.01:
                print(f"    {name}: g(*,{a},{b}) = {w_l1[idx]:.4f}")

    int_rev = {v: k for k, v in int_idx.items()}
    print(f"  Interior: g(j,a,b) = α(a,b)·j")
    for idx_i in sorted(int_rev.keys()):
        a, b = int_rev[idx_i]
        val = w_l1[idx_i]
        if abs(val) > 0.001:
            ft = frontier_type(a, b)
            print(f"    ({a},{b}) [ft={ft}]: α = {val:.4f}")

    # ── PHASE 2: Verify on n=10,11,12 ──
    print(f"\n{'=' * 65}")
    print(f"PHASE 2: Verify L1-minimal weights on larger n")
    print(f"{'=' * 65}")

    for n_val in range(5, 13):
        t0 = time.time()
        viol, total, mg = verify_weights(
            w_l1, n_val, bnd_0, bnd_1, bnd_2, bnd_3, bnd_4, int_idx)
        dt = time.time() - t0
        status = "✓" if viol == 0 else f"✗ ({viol} violations)"
        print(f"  n={n_val}: {viol}/{total} violations, "
              f"min_gap={mg:.3f} ({dt:.1f}s) {status}")

    # If feasibility solution also works, verify it too
    if w_feas is not None:
        print(f"\n  Also verify feasibility-LP weights:")
        for n_val in range(5, 13):
            viol, total, mg = verify_weights(
                w_feas, n_val, bnd_0, bnd_1, bnd_2, bnd_3, bnd_4,
                int_idx)
            status = "✓" if viol == 0 else f"✗ ({viol})"
            print(f"  n={n_val}: {viol}/{total}, min_gap={mg:.3f} "
                  f"{status}")

    # ── PHASE 3: Joint LP including n=10 ──
    print(f"\n{'=' * 65}")
    print(f"PHASE 3: Joint LP with n=5..10")
    print(f"{'=' * 65}")

    w_ext, _, info_ext = joint_lp_l1(list(range(5, 11)))
    if w_ext is not None:
        bnd_0e, bnd_1e, bnd_2e, bnd_3e, bnd_4e, n_bnde, int_idxe, _ = info_ext
        # Verify on n=11,12
        print(f"\n  Verify extended weights on n=11,12:")
        for n_val in [11, 12]:
            t0 = time.time()
            viol, total, mg = verify_weights(
                w_ext, n_val, bnd_0e, bnd_1e, bnd_2e, bnd_3e, bnd_4e,
                int_idxe)
            dt = time.time() - t0
            status = "✓" if viol == 0 else f"✗ ({viol})"
            print(f"    n={n_val}: {viol}/{total}, min_gap={mg:.3f} "
                  f"({dt:.1f}s) {status}")

        # Print weights comparison
        print(f"\n  Weight comparison (n=5..9 vs n=5..10):")
        print(f"  Interior α(a,b):")
        for idx_i in sorted(int_rev.keys()):
            a, b = int_rev[idx_i]
            v1 = w_l1[idx_i]
            v2 = w_ext[idx_i]
            if abs(v1) > 0.001 or abs(v2) > 0.001:
                ft = frontier_type(a, b)
                print(f"    ({a},{b}) [ft={ft}]: "
                      f"n≤9: {v1:.4f}, n≤10: {v2:.4f}")


if __name__ == '__main__':
    main()
