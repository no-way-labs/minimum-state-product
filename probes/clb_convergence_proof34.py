#!/usr/bin/env python3
"""
CONVERGENCE PROOF 34: Δint(2,1) Monotonicity & Proof Strategy
==============================================================

KEY DISCOVERY from proof28-33:
1. Pair potential Φ(c) = Σ_j g(j, c[j], c[j+1]) is FEASIBLE on excursion graph
   for all n=5..11 individually.
2. The excursion DAG has a UNIQUE SINK: (0,0,2,0,...,0) for n≥6.
3. Max rank = 2(n-4), depth exactly 2(n-4).
4. Δint(2,1) ≥ 0 for ALL excursion edges (n=5..11):
   The position-weighted interior (2,1) pair count NEVER increases.
   This is the ONLY pair with this monotonicity for n≥7.

This script:
A. Proves Δint(2,1) ≥ 0 analytically by examining the cascade mechanism.
B. Characterizes the Δint(2,1)=0 edges (the "hard" constraints).
C. Builds a TWO-COMPONENT potential:
   - Large α(2,1) handles Δint(2,1)>0 edges trivially
   - Boundary weights + small other α handle Δint(2,1)=0 edges
D. Checks if the Δint(2,1)=0 sub-LP is BOUNDED (finite # constraint types).
"""

import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter
import numpy as np
from scipy.optimize import linprog


def frontier_type(a, b):
    if a == b:
        return 0
    return (b - a) % 3


def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))


def fc_val(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def Q_val(c, n):
    return sum(1 for j in range(n)
               if c[j] == c[(j + 1) % n] and c[j] in (0, 1))


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

    return list(exc_edges), ms, anom_edges, dfc_le0_adj, anom_sources


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
    """Feature vector for pair potential with φ=j."""
    n = n_val
    r = [0] * n_vars
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
                r[k] += 1
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
            int_idx[(a, b)] = idx
            idx += 1
    n_vars = idx  # 43

    print(f"{'=' * 70}")
    print(f"PART A: Δint(2,1) ≥ 0 Characterization")
    print(f"{'=' * 70}")

    k21 = int_idx[(2, 1)]

    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms, anom_raw, dfc_le0_adj, anom_sources = \
            build_excursion_graph(n_val)
        n = n_val
        dt = time.time() - t0

        # Compute Δint(2,1) for all edges, characterize zero cases
        zero_edges = []
        pos_edges = []
        min_delta = float('inf')
        total = len(exc_edges)

        for u, v in exc_edges:
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            d21 = fu[k21] - fv[k21]
            min_delta = min(min_delta, d21)
            if d21 == 0:
                zero_edges.append((u, v))
            else:
                pos_edges.append((u, v, d21))

        print(f"\n  n={n_val}: {total} edges, min Δint(2,1)={min_delta}, "
              f"zeros={len(zero_edges)} ({100*len(zero_edges)/total:.1f}%) ({dt:.1f}s)")

        # Characterize the anomalous type of zero edges
        if zero_edges:
            # What anomalous entries do the SOURCES of zero edges have?
            src_types = Counter()
            for u, v in zero_edges:
                for i in range(n):
                    L = u[(i-1) % n]; S = u[i]; R = u[(i+1) % n]
                    out = ms_val = ms[i]  # not needed
                    out = build_system(n_val)[1][i](L, S, R)
                    if out != S and out != L and out != R:
                        if i == 0:
                            src_types[f"T_bot({L}{S}{R}→{out})"] += 1
                        elif i == n - 2:
                            src_types[f"T_high({L}{S}{R}→{out})"] += 1
                        elif i == n - 1:
                            src_types[f"T_top({L}{S}{R}→{out})"] += 1
                        else:
                            src_types[f"T_mid@{i}({L}{S}{R}→{out})"] += 1

            print(f"    Zero-edge src anomalous types (top 5): "
                  f"{dict(src_types.most_common(5))}")

    print(f"\n{'=' * 70}")
    print(f"PART B: Δint(2,1)=0 Sub-LP Analysis")
    print(f"{'=' * 70}")
    print(f"If we set α(2,1) = 0, can the remaining 42 variables")
    print(f"satisfy ALL Δint(2,1)=0 constraints?")

    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms, _, _, _ = build_excursion_graph(n_val)
        n = n_val

        # Separate into zero and positive
        zero_edges_sub = []
        for u, v in exc_edges:
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            if fu[k21] - fv[k21] == 0:
                zero_edges_sub.append((u, v))

        if not zero_edges_sub:
            print(f"\n  n={n_val}: no zero edges (trivial)")
            continue

        ne = len(zero_edges_sub)

        # Build LP with α(2,1) removed (variable k21 excluded)
        # Variables: 42 (all except k21)
        var_map = []
        for i in range(n_vars):
            if i != k21:
                var_map.append(i)
        n_sub = len(var_map)

        A = np.zeros((ne, n_sub))
        for ei, (u, v) in enumerate(zero_edges_sub):
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            for ki, orig_i in enumerate(var_map):
                A[ei, ki] = fu[orig_i] - fv[orig_i]

        # Feasibility check
        c_obj = np.zeros(n_sub)
        res = linprog(c_obj, A_ub=-A, b_ub=-np.ones(ne),
                      bounds=[(None, None)] * n_sub, method='highs')
        dt = time.time() - t0

        if res.success:
            w = res.x
            gaps = A @ w
            print(f"\n  n={n_val}: {ne} zero-edges, FEASIBLE "
                  f"(min_gap={gaps.min():.3f}) ({dt:.1f}s)")

            # Check: how many distinct constraint vectors?
            vecs = set()
            for ei in range(ne):
                vecs.add(tuple(A[ei]))
            print(f"    Distinct constraint vectors: {len(vecs)}")
        else:
            print(f"\n  n={n_val}: {ne} zero-edges, INFEASIBLE ({dt:.1f}s)")

    print(f"\n{'=' * 70}")
    print(f"PART C: Two-Component Potential Strategy")
    print(f"{'=' * 70}")
    print(f"For each n: solve LP with α(2,1)=0 on zero edges,")
    print(f"then add α(2,1) large enough for positive edges.")

    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms, _, _, _ = build_excursion_graph(n_val)
        n = n_val

        zero_edges_sub = []
        pos_edges_sub = []
        for u, v in exc_edges:
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            d21 = fu[k21] - fv[k21]
            if d21 == 0:
                zero_edges_sub.append((u, v))
            else:
                pos_edges_sub.append((u, v, d21))

        if not zero_edges_sub:
            print(f"\n  n={n_val}: no zero edges")
            continue

        ne_z = len(zero_edges_sub)
        ne_p = len(pos_edges_sub)

        # Step 1: Solve LP on zero edges with α(2,1)=0
        var_map = [i for i in range(n_vars) if i != k21]
        n_sub = len(var_map)

        A_z = np.zeros((ne_z, n_sub))
        for ei, (u, v) in enumerate(zero_edges_sub):
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            for ki, orig_i in enumerate(var_map):
                A_z[ei, ki] = fu[orig_i] - fv[orig_i]

        # L1-minimal
        c_obj = np.ones(2 * n_sub)
        A_split = np.hstack([-A_z, A_z])
        b_ub = -np.ones(ne_z)
        bounds = [(0, None)] * (2 * n_sub)
        res = linprog(c_obj, A_ub=A_split, b_ub=b_ub,
                      bounds=bounds, method='highs')

        if not res.success:
            print(f"\n  n={n_val}: zero-edge LP INFEASIBLE")
            continue

        w_sub = res.x[:n_sub] - res.x[n_sub:]
        gaps_z = A_z @ w_sub
        l1 = np.sum(np.abs(w_sub))

        # Step 2: Check what α(2,1) is needed for positive edges
        # For each positive edge: need (other terms) + α(2,1) * d21 ≥ 1
        # other terms = Σ w_sub[k] * (fu[var_map[k]] - fv[var_map[k]])
        # So α(2,1) ≥ (1 - other terms) / d21

        min_alpha = float('-inf')
        for u, v, d21 in pos_edges_sub:
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            other = sum(w_sub[ki] * (fu[orig_i] - fv[orig_i])
                        for ki, orig_i in enumerate(var_map))
            needed = (1 - other) / d21
            min_alpha = max(min_alpha, needed)

        dt = time.time() - t0
        print(f"\n  n={n_val}: zero={ne_z}, pos={ne_p}, "
              f"||w_sub||₁={l1:.1f}, min_gap_z={gaps_z.min():.3f}, "
              f"min α(2,1) needed={min_alpha:.3f} ({dt:.1f}s)")

    print(f"\n{'=' * 70}")
    print(f"PART D: Constraint Type Analysis for Zero Edges")
    print(f"{'=' * 70}")
    print(f"Do the zero-edge constraints come from finitely many 'types'?")
    print(f"(boundary part only, since interior Δ(2,1)=0)")

    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms, _, _, _ = build_excursion_graph(n_val)
        n = n_val

        zero_bnd_types = set()
        zero_full_types = set()

        for u, v in exc_edges:
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            if fu[k21] - fv[k21] == 0:
                bnd_part = tuple(fu[i] - fv[i] for i in range(n_bnd))
                full_part = tuple(fu[i] - fv[i] for i in range(n_vars))
                zero_bnd_types.add(bnd_part)
                zero_full_types.add(full_part)

        dt = time.time() - t0
        print(f"  n={n_val}: boundary types={len(zero_bnd_types)}, "
              f"full types={len(zero_full_types)} ({dt:.1f}s)")


if __name__ == '__main__':
    main()
