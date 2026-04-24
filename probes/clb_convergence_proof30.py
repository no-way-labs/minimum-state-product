#!/usr/bin/env python3
"""
CONVERGENCE PROOF 30: Joint LP for Universal Pair Potential
===========================================================

Key finding from proof28-29: pair-based potential is FEASIBLE on the
excursion graph for all n=5..9 individually.

This script tests whether a SINGLE parameterized pair potential works
for ALL n simultaneously:

  g(j, a, b) = α(a,b)·φ(j,n) + β(a,b)   for interior positions
  g(j, a, b) = free per boundary type      for boundary positions

Boundary types (same table-pair structure for all n):
  Type 0: T_bot—T_low  (j=0)
  Type 1: T_low—T_mid  (j=1)
  Type 2: T_mid—T_high (j=n-3)
  Type 3: T_high—T_top (j=n-2)
  Type 4: T_top—T_bot  (j=n-1)

Interior: 2 ≤ j ≤ n-4 (T_mid—T_mid)

Tests multiple position functions φ(j,n):
  A: φ = j           (linear)
  B: φ = j, j²       (quadratic)
  C: φ = j, n-1-j    (two-directional)
  D: φ = j(n-1-j)    (parabolic)
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
    """Build variable indices for boundary pair types."""
    idx = 0

    # Type 0: T_bot—T_low: a∈{0,1}, b∈{0,1,2}
    bnd_0 = {}
    for a in range(2):
        for b in range(3):
            bnd_0[(a, b)] = idx
            idx += 1

    # Type 1: T_low—T_mid: a∈{0,1,2}, b∈{0,1,2}
    bnd_1 = {}
    for a in range(3):
        for b in range(3):
            bnd_1[(a, b)] = idx
            idx += 1

    # Type 2: T_mid—T_high: a∈{0,1,2}, b∈{0,1,2}
    bnd_2 = {}
    for a in range(3):
        for b in range(3):
            bnd_2[(a, b)] = idx
            idx += 1

    # Type 3: T_high—T_top: a∈{0,1,2}, b∈{0,1}
    bnd_3 = {}
    for a in range(3):
        for b in range(2):
            bnd_3[(a, b)] = idx
            idx += 1

    # Type 4: T_top—T_bot: a∈{0,1}, b∈{0,1}
    bnd_4 = {}
    for a in range(2):
        for b in range(2):
            bnd_4[(a, b)] = idx
            idx += 1

    n_bnd = idx  # = 6+9+9+6+4 = 34
    return bnd_0, bnd_1, bnd_2, bnd_3, bnd_4, n_bnd


def test_joint_lp(n_values, phi_name, phi_funcs):
    """
    Joint LP: find a single parameterized pair potential valid for all n.

    phi_funcs: list of functions φ_k(j, n) for interior position weight.
    Interior weight: g(j, a, b) = Σ_k α_k(a,b) · φ_k(j, n)
    """
    bnd_0, bnd_1, bnd_2, bnd_3, bnd_4, n_bnd = build_boundary_indices()

    n_phi = len(phi_funcs)
    # Interior variables: for each pair (a,b) ∈ {0,1,2}², n_phi coefficients
    int_vars = {}
    idx = n_bnd
    for a in range(3):
        for b in range(3):
            int_vars[(a, b)] = []
            for k in range(n_phi):
                int_vars[(a, b)].append(idx)
                idx += 1

    n_vars = idx

    # Feature function
    def feat(c, n_val):
        n = n_val
        r = {}
        for j in range(n):
            j1 = (j + 1) % n
            a, b = c[j], c[j1]

            if j == 0:
                k = bnd_0.get((a, b))
                if k is not None:
                    r[k] = r.get(k, 0) + 1
            elif j == 1:
                k = bnd_1.get((a, b))
                if k is not None:
                    r[k] = r.get(k, 0) + 1
            elif j == n - 3:
                k = bnd_2.get((a, b))
                if k is not None:
                    r[k] = r.get(k, 0) + 1
            elif j == n - 2:
                k = bnd_3.get((a, b))
                if k is not None:
                    r[k] = r.get(k, 0) + 1
            elif j == n - 1:
                k = bnd_4.get((a, b))
                if k is not None:
                    r[k] = r.get(k, 0) + 1
            else:
                # Interior: 2 ≤ j ≤ n-4
                for ki, var_idx in enumerate(int_vars[(a, b)]):
                    phi_val = phi_funcs[ki](j, n)
                    r[var_idx] = r.get(var_idx, 0) + phi_val
        return r

    # Collect all excursion edges
    all_edges = []
    for n_val in n_values:
        exc_edges, ms = build_excursion_graph(n_val)
        print(f"  n={n_val}: {len(exc_edges)} excursion edges")
        for u, v in exc_edges:
            all_edges.append((u, v, n_val))

    ne = len(all_edges)
    print(f"  Total: {ne} constraints, {n_vars} variables")

    # Build LP
    A = np.zeros((ne, n_vars))
    for ei, (u, v, n_val) in enumerate(all_edges):
        fu = feat(u, n_val)
        fv = feat(v, n_val)
        for k, val in fu.items():
            A[ei, k] += val
        for k, val in fv.items():
            A[ei, k] -= val

    c_obj = np.zeros(n_vars)
    res = linprog(c_obj, A_ub=-A, b_ub=-np.ones(ne),
                  bounds=[(None, None)] * n_vars, method='highs')

    if res.success:
        w = res.x
        gaps = A @ w
        print(f"  {phi_name}: *** FEASIBLE *** "
              f"(min_gap={gaps.min():.3f})")

        # Print boundary weights
        bnd_names = [
            ("T_bot—T_low", bnd_0, [(0, 1), (0, 1, 2)]),
            ("T_low—T_mid", bnd_1, [(0, 1, 2), (0, 1, 2)]),
            ("T_mid—T_high", bnd_2, [(0, 1, 2), (0, 1, 2)]),
            ("T_high—T_top", bnd_3, [(0, 1, 2), (0, 1)]),
            ("T_top—T_bot", bnd_4, [(0, 1), (0, 1)]),
        ]
        print(f"\n  Boundary weights:")
        for name, bnd, (avals, bvals) in bnd_names:
            nz = [(k, w[v]) for k, v in bnd.items() if abs(w[v]) > 0.01]
            if nz:
                for (a, b), wt in sorted(nz):
                    print(f"    {name}: g(*,{a},{b}) = {wt:.3f}")

        print(f"\n  Interior weights (g = Σ α_k · φ_k):")
        for a in range(3):
            for b in range(3):
                vars_ab = int_vars[(a, b)]
                coeffs = [w[vi] for vi in vars_ab]
                if any(abs(c) > 0.01 for c in coeffs):
                    ft = frontier_type(a, b)
                    cstr = ", ".join(f"α_{k}={c:.3f}" for k, c in
                                    enumerate(coeffs))
                    print(f"    ({a},{b}) [ft={ft}]: {cstr}")

        return w
    else:
        print(f"  {phi_name}: INFEASIBLE")
        return None


def main():
    n_values = list(range(5, 10))

    print(f"{'=' * 65}")
    print(f"JOINT LP: Testing universal pair potential across n={n_values}")
    print(f"{'=' * 65}")

    # Test A: φ = j (linear)
    print(f"\n── Test A: φ(j,n) = j ──")
    test_joint_lp(n_values, "Linear φ=j",
                  [lambda j, n: j])

    # Test B: φ = j, j² (quadratic)
    print(f"\n── Test B: φ(j,n) = j, j² ──")
    test_joint_lp(n_values, "Quadratic φ=j,j²",
                  [lambda j, n: j, lambda j, n: j * j])

    # Test C: φ = j, n-1-j (bidirectional)
    print(f"\n── Test C: φ(j,n) = j, n-1-j ──")
    test_joint_lp(n_values, "Bidir φ=j,n-1-j",
                  [lambda j, n: j, lambda j, n: n - 1 - j])

    # Test D: φ = j(n-1-j) (parabolic)
    print(f"\n── Test D: φ(j,n) = j(n-1-j) ──")
    test_joint_lp(n_values, "Parabolic φ=j(n-1-j)",
                  [lambda j, n: j * (n - 1 - j)])

    # Test E: φ = 1, j (constant + linear = α·j + β)
    print(f"\n── Test E: φ(j,n) = 1, j ──")
    test_joint_lp(n_values, "Affine φ=1,j",
                  [lambda j, n: 1, lambda j, n: j])

    # Test F: φ = 1, j, n-1-j (constant + both directions)
    print(f"\n── Test F: φ(j,n) = 1, j, n-1-j ──")
    test_joint_lp(n_values, "Full-affine φ=1,j,n-1-j",
                  [lambda j, n: 1, lambda j, n: j,
                   lambda j, n: n - 1 - j])

    # Test G: φ = 1, j, j², j(n-1-j) (rich)
    print(f"\n── Test G: φ(j,n) = 1, j, j², j(n-1-j) ──")
    test_joint_lp(n_values, "Rich basis",
                  [lambda j, n: 1, lambda j, n: j,
                   lambda j, n: j * j,
                   lambda j, n: j * (n - 1 - j)])

    # Test H: only n=6..9 (skip n=5 which has no interior)
    print(f"\n── Test H: n=6..9 only, φ=1,j ──")
    test_joint_lp(list(range(6, 10)), "n≥6 affine",
                  [lambda j, n: 1, lambda j, n: j])

    # Test I: Position functions motivated by Ψ weights
    # w₁(j) = j+1 for interior, w₂(j) = n-1-j for interior
    print(f"\n── Test I: φ(j,n) = j+1, n-1-j (Ψ-like) ──")
    test_joint_lp(n_values, "Ψ-like weights",
                  [lambda j, n: j + 1, lambda j, n: n - 1 - j])


if __name__ == '__main__':
    main()
