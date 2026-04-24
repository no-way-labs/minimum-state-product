#!/usr/bin/env python3
"""
CONVERGENCE PROOF 39: Boundary-Only Weights & Additional Monotonicity
=====================================================================

KEY FINDINGS from proof38:
  - Interior Δ ranges grow with n (NOT bounded) for most pairs
  - BUT: Δint(2,0) ≥ 0 for ALL n (another monotonicity!)
  - AND: Δint(0,1) ≥ -2 for ALL n (bounded below)

APPROACH: Can we close the proof without relying on interior weights?

TEST 1: Boundary-only sub-LP (34 vars, all interior α=0 except α(2,1)=0)
  If feasible for all zero edges at each n: proof done!

TEST 2: Verify Δint(2,0) ≥ 0 analytically (same method as proof36)
  If yes: three-component potential (α(2,1), α(2,0), boundary weights)

TEST 3: Fixed universal boundary weights across n values
  Solve joint LP for boundary-only constraints from n=5..11
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
    k20 = int_idx[(2, 0)]

    # ═══════════════════════════════════════════════════════════
    # TEST 1: Boundary-only sub-LP for zero edges
    # ═══════════════════════════════════════════════════════════
    print("=" * 70)
    print("TEST 1: Boundary-only weights for zero edges")
    print("=" * 70)
    print("Setting ALL interior α(a,b) = 0. Can boundary weights alone satisfy?")
    print()

    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        # Get zero edges
        zero_edges = []
        for u, v in exc_edges:
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            if fu[k21] - fv[k21] == 0:
                zero_edges.append((u, v))

        if not zero_edges:
            print(f"  n={n_val}: no zero edges")
            continue

        ne = len(zero_edges)

        # Build boundary-only LP (34 vars)
        A = np.zeros((ne, n_bnd))
        for ei, (u, v) in enumerate(zero_edges):
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            for ki in range(n_bnd):
                A[ei, ki] = fu[ki] - fv[ki]

        c_obj = np.zeros(n_bnd)
        res = linprog(c_obj, A_ub=-A, b_ub=-np.ones(ne),
                      bounds=[(None, None)] * n_bnd, method='highs')

        dt = time.time() - t0
        if res.success:
            gaps = A @ res.x
            print(f"  n={n_val}: {ne} zero-edges, BOUNDARY-ONLY FEASIBLE "
                  f"(min_gap={gaps.min():.3f}) ({dt:.1f}s)")
        else:
            print(f"  n={n_val}: {ne} zero-edges, BOUNDARY-ONLY INFEASIBLE ({dt:.1f}s)")

    # ═══════════════════════════════════════════════════════════
    # TEST 2: Verify Δint(2,0) ≥ 0 for all excursion edges
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("TEST 2: Δint(2,0) ≥ 0 on ALL excursion edges (not just zero)")
    print("=" * 70)

    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        min_d20 = float('inf')
        min_d01 = float('inf')
        for u, v in exc_edges:
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            d20 = fu[k20] - fv[k20]
            d01 = fu[int_idx[(0, 1)]] - fv[int_idx[(0, 1)]]
            min_d20 = min(min_d20, d20)
            min_d01 = min(min_d01, d01)

        dt = time.time() - t0
        print(f"  n={n_val}: min Δint(2,0)={min_d20}, "
              f"min Δint(0,1)={min_d01} ({dt:.1f}s)")

    # ═══════════════════════════════════════════════════════════
    # TEST 3: Joint boundary-only LP across all n
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("TEST 3: Joint boundary-only LP for n=5..10")
    print("=" * 70)
    print("Solve for ONE set of 34 boundary weights that works for ALL n.")
    print()

    all_bnd_constraints = []
    for n_val in range(5, 11):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        for u, v in exc_edges:
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            if fu[k21] - fv[k21] == 0:
                bvec = tuple(fu[i] - fv[i] for i in range(n_bnd))
                all_bnd_constraints.append(bvec)

        dt = time.time() - t0
        print(f"  n={n_val}: accumulated {len(all_bnd_constraints)} constraints ({dt:.1f}s)")

    # Deduplicate
    unique_constraints = list(set(all_bnd_constraints))
    print(f"\n  Unique boundary constraint vectors: {len(unique_constraints)}")

    ne = len(unique_constraints)
    A = np.array(unique_constraints, dtype=float)

    c_obj = np.zeros(n_bnd)
    res = linprog(c_obj, A_ub=-A, b_ub=-np.ones(ne),
                  bounds=[(None, None)] * n_bnd, method='highs')

    if res.success:
        gaps = A @ res.x
        print(f"  Joint LP (n=5..10): FEASIBLE (min_gap={gaps.min():.3f})")

        # Test these weights on n=11
        print(f"  Testing joint weights on n=11...")
        exc_11, ms_11 = build_excursion_graph(11)
        n_fail = 0
        n_total = 0
        for u, v in exc_11:
            fu = feat_vector(u, 11, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, 11, bnd, n_bnd, int_idx, n_vars)
            if fu[k21] - fv[k21] == 0:
                n_total += 1
                bvec = np.array([fu[i] - fv[i] for i in range(n_bnd)])
                gap = bvec @ res.x
                if gap < 1 - 1e-9:
                    n_fail += 1

        print(f"  n=11 zero-edge violations: {n_fail}/{n_total}")
    else:
        print(f"  Joint LP (n=5..10): INFEASIBLE")

    # ═══════════════════════════════════════════════════════════
    # TEST 4: Boundary + monotone interior (α(2,0) free) sub-LP
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("TEST 4: Boundary + α(2,0) for zero edges")
    print("=" * 70)
    print("Since Δint(2,0) ≥ 0, we can freely use α(2,0) > 0.")
    print("Variables: 34 boundary + 1 interior = 35 vars")
    print()

    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        zero_edges = []
        for u, v in exc_edges:
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            if fu[k21] - fv[k21] == 0:
                zero_edges.append((u, v))

        if not zero_edges:
            print(f"  n={n_val}: no zero edges")
            continue

        ne = len(zero_edges)
        n_sub = n_bnd + 1  # 34 + 1 = 35

        A = np.zeros((ne, n_sub))
        for ei, (u, v) in enumerate(zero_edges):
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            for ki in range(n_bnd):
                A[ei, ki] = fu[ki] - fv[ki]
            A[ei, n_bnd] = fu[k20] - fv[k20]  # α(2,0) column

        c_obj = np.zeros(n_sub)
        res = linprog(c_obj, A_ub=-A, b_ub=-np.ones(ne),
                      bounds=[(None, None)] * n_sub, method='highs')

        dt = time.time() - t0
        if res.success:
            gaps = A @ res.x
            print(f"  n={n_val}: {ne} zero-edges, BND+α(2,0) FEASIBLE "
                  f"(min_gap={gaps.min():.3f}, α(2,0)={res.x[n_bnd]:.3f}) ({dt:.1f}s)")
        else:
            print(f"  n={n_val}: {ne} zero-edges, BND+α(2,0) INFEASIBLE ({dt:.1f}s)")

    # ═══════════════════════════════════════════════════════════
    # TEST 5: Which other pairs have Δint ≥ 0 on ALL exc edges?
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("TEST 5: Monotone interior pairs (Δint ≥ 0 on ALL edges)")
    print("=" * 70)

    pairs = [(a, b) for a in range(3) for b in range(3)]
    monotone = {(a, b): True for a, b in pairs}

    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        for u, v in exc_edges:
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            for a, b in pairs:
                k = int_idx[(a, b)]
                if fu[k] - fv[k] < 0:
                    monotone[(a, b)] = False

        dt = time.time() - t0
        still_mono = [(a, b) for (a, b) in pairs if monotone[(a, b)]]
        print(f"  n={n_val}: monotone pairs = {still_mono} ({dt:.1f}s)")


if __name__ == '__main__':
    main()
