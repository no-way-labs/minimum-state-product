#!/usr/bin/env python3
"""
CONVERGENCE PROOF 32: N-Dependent Basis Functions for Universal Potential
=========================================================================

From proof31: linear φ=j works per-range but α values GROW with n.
The interior weight needs to SCALE with n.

Tests n-dependent basis functions:
A: φ = j·(n-4)         [scale by half excursion depth]
B: φ = j, j·(n-4)      [two basis: static + n-scaled]
C: φ = j, j²            [quadratic position]
D: φ = j·(n-3)          [scale by interior length]
E: φ = j·(n-1-j)        [parabolic, n-dependent]

Also: joint LP for n=5..11 with best basis, verify on n=12.
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
    bnd = [{}, {}, {}, {}, {}]
    # T_bot—T_low
    for a in range(2):
        for b in range(3):
            bnd[0][(a, b)] = idx; idx += 1
    # T_low—T_mid
    for a in range(3):
        for b in range(3):
            bnd[1][(a, b)] = idx; idx += 1
    # T_mid—T_high
    for a in range(3):
        for b in range(3):
            bnd[2][(a, b)] = idx; idx += 1
    # T_high—T_top
    for a in range(3):
        for b in range(2):
            bnd[3][(a, b)] = idx; idx += 1
    # T_top—T_bot
    for a in range(2):
        for b in range(2):
            bnd[4][(a, b)] = idx; idx += 1
    n_bnd = idx
    return bnd, n_bnd


def test_basis(n_values, basis_name, phi_funcs, verify_extra=None):
    """Joint LP with given basis functions."""
    print(f"\n  ── {basis_name} ──")
    bnd, n_bnd = build_boundary_indices()

    n_phi = len(phi_funcs)
    int_idx = {}
    idx = n_bnd
    for a in range(3):
        for b in range(3):
            int_idx[(a, b)] = list(range(idx, idx + n_phi))
            idx += n_phi
    n_vars = idx

    def feat(c, n_val):
        n = n_val
        r = {}
        for j in range(n):
            j1 = (j + 1) % n
            a, b = c[j], c[j1]
            bnd_type = None
            if j == 0:
                bnd_type = 0
            elif j == 1:
                bnd_type = 1
            elif j == n - 3:
                bnd_type = 2
            elif j == n - 2:
                bnd_type = 3
            elif j == n - 1:
                bnd_type = 4

            if bnd_type is not None:
                k = bnd[bnd_type].get((a, b))
                if k is not None:
                    r[k] = r.get(k, 0) + 1
            else:
                for ki, var_i in enumerate(int_idx[(a, b)]):
                    pv = phi_funcs[ki](j, n)
                    r[var_i] = r.get(var_i, 0) + pv
        return r

    # Collect edges
    all_edges = []
    for n_val in n_values:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        dt = time.time() - t0
        print(f"    n={n_val}: {len(exc_edges)} edges ({dt:.1f}s)")
        for u, v in exc_edges:
            all_edges.append((u, v, n_val))

    ne = len(all_edges)
    print(f"    Total: {ne} constraints, {n_vars} variables")

    # Build LP
    A = np.zeros((ne, n_vars))
    for ei, (u, v, n_val) in enumerate(all_edges):
        fu = feat(u, n_val)
        fv = feat(v, n_val)
        for k, val in fu.items():
            A[ei, k] += val
        for k, val in fv.items():
            A[ei, k] -= val

    # L1-minimal
    c_obj = np.ones(2 * n_vars)
    A_split = np.hstack([-A, A])
    b_ub = -np.ones(ne)
    bounds = [(0, None)] * (2 * n_vars)

    t0 = time.time()
    res = linprog(c_obj, A_ub=A_split, b_ub=b_ub,
                  bounds=bounds, method='highs')
    dt = time.time() - t0

    if not res.success:
        print(f"    {basis_name}: INFEASIBLE ({dt:.1f}s)")
        return None

    w = res.x[:n_vars] - res.x[n_vars:]
    gaps = A @ w
    l1 = np.sum(np.abs(w))
    print(f"    {basis_name}: FEASIBLE, ||w||₁={l1:.1f}, "
          f"min_gap={gaps.min():.3f} ({dt:.1f}s)")

    # Print interior weights
    int_rev = {}
    for (a, b), idxs in int_idx.items():
        for ki, vi in enumerate(idxs):
            int_rev[vi] = (a, b, ki)

    has_nonzero = False
    for vi in sorted(int_rev.keys()):
        a, b, ki = int_rev[vi]
        if abs(w[vi]) > 0.001:
            if not has_nonzero:
                print(f"    Interior coefficients:")
                has_nonzero = True
            ft = frontier_type(a, b)
            print(f"      ({a},{b}) [ft={ft}]: α_{ki} = {w[vi]:.4f}")

    # Verify on extra n values
    if verify_extra:
        print(f"    Verification:")
        for n_val in verify_extra:
            t0 = time.time()
            exc_edges_v, _ = build_excursion_graph(n_val)
            viol = 0
            min_g = float('inf')
            for u, v in exc_edges_v:
                fu = feat(u, n_val)
                fv = feat(v, n_val)
                gap = sum(w[k] * val for k, val in fu.items()) - \
                    sum(w[k] * val for k, val in fv.items())
                min_g = min(min_g, gap)
                if gap <= 0:
                    viol += 1
            dt = time.time() - t0
            status = "✓" if viol == 0 else f"✗ ({viol})"
            print(f"      n={n_val}: {viol}/{len(exc_edges_v)}, "
                  f"min_gap={min_g:.3f} ({dt:.1f}s) {status}")

    return w


def main():
    print(f"{'=' * 65}")
    print(f"N-dependent basis function search")
    print(f"{'=' * 65}")

    # First: test on n=5..10 with various bases, verify on n=11
    n_train = list(range(5, 11))

    # A: φ = j·(n-4)
    test_basis(n_train, "A: j·(n-4)",
               [lambda j, n: j * (n - 4)],
               verify_extra=[11])

    # B: φ = j, j·(n-4)
    test_basis(n_train, "B: j, j·(n-4)",
               [lambda j, n: j, lambda j, n: j * (n - 4)],
               verify_extra=[11])

    # C: φ = j, j²
    test_basis(n_train, "C: j, j²",
               [lambda j, n: j, lambda j, n: j * j],
               verify_extra=[11])

    # D: φ = j·(n-3)
    test_basis(n_train, "D: j·(n-3)",
               [lambda j, n: j * (n - 3)],
               verify_extra=[11])

    # E: φ = j·(n-1-j) (parabolic)
    test_basis(n_train, "E: j·(n-1-j)",
               [lambda j, n: j * (n - 1 - j)],
               verify_extra=[11])

    # F: φ = 1, j, j·(n-4)
    test_basis(n_train, "F: 1, j, j·(n-4)",
               [lambda j, n: 1, lambda j, n: j,
                lambda j, n: j * (n - 4)],
               verify_extra=[11])

    # G: φ = j·n
    test_basis(n_train, "G: j·n",
               [lambda j, n: j * n],
               verify_extra=[11])

    # H: φ = j, j·n
    test_basis(n_train, "H: j, j·n",
               [lambda j, n: j, lambda j, n: j * n],
               verify_extra=[11])

    # I: φ = j, (n-1-j)
    test_basis(n_train, "I: j, n-1-j",
               [lambda j, n: j, lambda j, n: n - 1 - j],
               verify_extra=[11])

    # J: φ = j, j*(j-1)/2 (triangular)
    test_basis(n_train, "J: j, j(j-1)/2",
               [lambda j, n: j,
                lambda j, n: j * (j - 1) // 2],
               verify_extra=[11])

    # K: φ = j², j·(n-4)
    test_basis(n_train, "K: j², j·(n-4)",
               [lambda j, n: j * j,
                lambda j, n: j * (n - 4)],
               verify_extra=[11])

    # Now find the best basis and test on n=5..11, verify n=12
    print(f"\n{'=' * 65}")
    print(f"Extended test: n=5..11, verify n=12")
    print(f"{'=' * 65}")

    n_train2 = list(range(5, 12))

    # Best candidates from above
    test_basis(n_train2, "BEST-B: j, j·(n-4)",
               [lambda j, n: j, lambda j, n: j * (n - 4)],
               verify_extra=[12])

    test_basis(n_train2, "BEST-H: j, j·n",
               [lambda j, n: j, lambda j, n: j * n],
               verify_extra=[12])


if __name__ == '__main__':
    main()
