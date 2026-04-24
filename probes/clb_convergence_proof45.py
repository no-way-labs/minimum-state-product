#!/usr/bin/env python3
"""
CONVERGENCE PROOF 45: Minimal Interior Variables & Cascade Decomposition
========================================================================

Finding: boundary-only fails, but 42-var works. What's the MINIMUM
number of interior variables needed?

TEST 1: For each interior pair, try boundary + that single pair
TEST 2: Try boundary + 2 pairs, find the minimal sufficient set
TEST 3: Analyze which pairs the LP solution actually uses (nonzero α)
TEST 4: Cascade decomposition — can we express interior Δ as
        a function of "cascade type" (left, right, bidirectional)?

KEY OBSERVATION: (0,1) has bounded minimum (-2) on all zero/double-zero
edges. This is remarkable and might be analytically provable.
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
from itertools import combinations


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
    n_vars = idx
    k21 = int_idx[(2, 1)]
    k20 = int_idx[(2, 0)]

    # Variable map (excluding k21)
    var_map = [i for i in range(n_vars) if i != k21]
    n_sub = len(var_map)

    # Build per-n zero-edge constraint matrices
    per_n_data = {}
    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        constraints = []
        for u, v in exc_edges:
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            if fu[k21] - fv[k21] == 0:
                constraints.append([fu[i] - fv[i] for i in var_map])

        per_n_data[n_val] = np.array(constraints, dtype=float) if constraints else None
        dt = time.time() - t0
        ne = len(constraints)
        print(f"  n={n_val}: {ne} zero-edges ({dt:.1f}s)")

    # ═══════════════════════════════════════════════════════════
    # TEST 1: Boundary + single interior pair
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("TEST 1: Boundary + single interior pair")
    print("=" * 70)

    int_pairs = [(a, b) for a in range(3) for b in range(3) if (a, b) != (2, 1)]
    int_orig_indices = {}
    for ki, orig_i in enumerate(var_map):
        if orig_i >= n_bnd:
            for (a, b), idx_val in int_idx.items():
                if idx_val == orig_i and (a, b) != (2, 1):
                    int_orig_indices[(a, b)] = ki
                    break

    # Test each interior pair individually for n=7..11
    for n_val in [7, 8, 9, 10, 11]:
        A = per_n_data.get(n_val)
        if A is None:
            continue
        ne = A.shape[0]

        print(f"\n  n={n_val}: {ne} zero-edges")
        results = []
        for pair in int_pairs:
            ki = int_orig_indices[pair]
            # Variables: 34 boundary + 1 interior = 35
            cols = list(range(n_bnd)) + [ki]
            A_sub = A[:, cols]
            n_v = len(cols)

            c_obj = np.zeros(n_v)
            res = linprog(c_obj, A_ub=-A_sub, b_ub=-np.ones(ne),
                          bounds=[(None, None)] * n_v, method='highs')
            status = "F" if res.success else "X"
            results.append((pair, status))

        feas = [p for p, s in results if s == "F"]
        infeas = [p for p, s in results if s == "X"]
        print(f"    Feasible with boundary + single pair: {feas}")
        print(f"    Infeasible: {infeas}")

    # ═══════════════════════════════════════════════════════════
    # TEST 2: Boundary + 2 pairs (systematic search)
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("TEST 2: Boundary + 2 interior pairs (n=9)")
    print("=" * 70)

    n_val = 9
    A = per_n_data[n_val]
    ne = A.shape[0]

    feasible_pairs = []
    for p1, p2 in combinations(int_pairs, 2):
        ki1 = int_orig_indices[p1]
        ki2 = int_orig_indices[p2]
        cols = list(range(n_bnd)) + [ki1, ki2]
        A_sub = A[:, cols]
        n_v = len(cols)

        c_obj = np.zeros(n_v)
        res = linprog(c_obj, A_ub=-A_sub, b_ub=-np.ones(ne),
                      bounds=[(None, None)] * n_v, method='highs')
        if res.success:
            feasible_pairs.append((p1, p2))

    print(f"  n=9: {ne} zero-edges")
    print(f"  Feasible with boundary + 2 pairs:")
    for p1, p2 in feasible_pairs:
        print(f"    {p1}, {p2}")

    # Check which of these work for ALL n=7..11
    print(f"\n  Cross-n check:")
    for p1, p2 in feasible_pairs:
        ki1 = int_orig_indices[p1]
        ki2 = int_orig_indices[p2]
        cols = list(range(n_bnd)) + [ki1, ki2]
        all_ok = True
        for n_t in [7, 8, 9, 10, 11]:
            A_t = per_n_data[n_t]
            if A_t is None:
                continue
            A_sub = A_t[:, cols]
            n_v = len(cols)
            c_obj = np.zeros(n_v)
            res = linprog(c_obj, A_ub=-A_sub, b_ub=-np.ones(A_t.shape[0]),
                          bounds=[(None, None)] * n_v, method='highs')
            if not res.success:
                all_ok = False
                break
        status = "ALL n=7..11" if all_ok else "NOT all"
        print(f"    {p1}, {p2}: {status}")

    # ═══════════════════════════════════════════════════════════
    # TEST 3: What variables does the per-n solution use?
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("TEST 3: Per-n solution variable usage")
    print("=" * 70)

    for n_val in range(7, 12):
        A = per_n_data[n_val]
        if A is None:
            continue
        ne = A.shape[0]

        c_obj = np.ones(2 * n_sub)
        A_split = np.hstack([-A, A])
        b_ub = -np.ones(ne)
        bounds = [(0, None)] * (2 * n_sub)
        res = linprog(c_obj, A_ub=A_split, b_ub=b_ub,
                      bounds=bounds, method='highs')

        if res.success:
            w = res.x[:n_sub] - res.x[n_sub:]
            # Which interior variables are used?
            used = {}
            for pair in int_pairs:
                ki = int_orig_indices[pair]
                if abs(w[ki]) > 0.001:
                    used[pair] = w[ki]
            print(f"  n={n_val}: interior vars used: "
                  + ", ".join(f"α{p}={v:.3f}" for p, v in sorted(used.items())))

    # ═══════════════════════════════════════════════════════════
    # TEST 4: Cascade type analysis
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("TEST 4: Cascade direction on zero edges")
    print("=" * 70)

    for n_val in [8, 9, 10]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        left_only = 0
        right_only = 0
        both = 0
        neither = 0
        total = 0

        for u, v in exc_edges:
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            if fu[k21] - fv[k21] != 0:
                continue
            total += 1

            # Find which positions differ
            diffs = [j for j in range(n) if u[j] != v[j]]
            if not diffs:
                neither += 1
                continue

            has_left = any(j <= n // 2 for j in diffs if 2 <= j <= n-3)
            has_right = any(j > n // 2 for j in diffs if 2 <= j <= n-3)

            if has_left and has_right:
                both += 1
            elif has_left:
                left_only += 1
            elif has_right:
                right_only += 1
            else:
                neither += 1

        dt = time.time() - t0
        print(f"  n={n_val}: {total} zero-edges ({dt:.1f}s)")
        print(f"    Left-only: {left_only} ({100*left_only/total:.1f}%)")
        print(f"    Right-only: {right_only} ({100*right_only/total:.1f}%)")
        print(f"    Both: {both} ({100*both/total:.1f}%)")
        print(f"    Neither (boundary only): {neither} ({100*neither/total:.1f}%)")


if __name__ == '__main__':
    main()
