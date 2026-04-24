#!/usr/bin/env python3
"""
CONVERGENCE PROOF 42: Weight Scaling Law & Interior Contribution Analysis
=========================================================================

The joint 42-var LP is feasible through n=12, but weights grow ~4x per n.

HYPOTHESIS: The weights scale as c·r^n for some rate r.
If true: the NORMALIZED weights converge, and we need to prove that
the gap scales at least as fast as r^n.

TEST 1: Per-n weight scaling (normalize by ||w||₁, check convergence)
TEST 2: Interior contribution lower bound per-n
TEST 3: Boundary type vs interior contribution decomposition
TEST 4: Can we factor the constraint as boundary_gap + scaling·interior_gap?
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
    n_vars = idx
    k21 = int_idx[(2, 1)]
    var_map = [i for i in range(n_vars) if i != k21]
    n_sub = len(var_map)

    int_var_indices = []
    int_pair_names = []
    for ki, orig_i in enumerate(var_map):
        if orig_i >= n_bnd:
            int_var_indices.append(ki)
            for (a, b), idx_val in int_idx.items():
                if idx_val == orig_i:
                    int_pair_names.append((a, b))
                    break

    # ═══════════════════════════════════════════════════════════
    # TEST 1: Per-n weight scaling
    # ═══════════════════════════════════════════════════════════
    print("=" * 70)
    print("TEST 1: Per-n weight scaling analysis")
    print("=" * 70)

    per_n_weights = {}
    per_n_constraints_raw = {}
    per_n_l1 = {}

    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        constraints = []
        for u, v in exc_edges:
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            if fu[k21] - fv[k21] == 0:
                cvec = [fu[i] - fv[i] for i in var_map]
                constraints.append(cvec)

        per_n_constraints_raw[n_val] = constraints

        if not constraints:
            print(f"  n={n_val}: no zero edges")
            continue

        ne = len(constraints)
        A = np.array(constraints, dtype=float)

        # L1-minimal
        c_obj = np.ones(2 * n_sub)
        A_split = np.hstack([-A, A])
        b_ub = -np.ones(ne)
        bounds = [(0, None)] * (2 * n_sub)
        res = linprog(c_obj, A_ub=A_split, b_ub=b_ub,
                      bounds=bounds, method='highs')

        if res.success:
            w = res.x[:n_sub] - res.x[n_sub:]
            per_n_weights[n_val] = w
            l1 = np.sum(np.abs(w))
            per_n_l1[n_val] = l1

    # Print scaling
    print(f"\n  Per-n L1 norms:")
    prev_l1 = None
    for n_val in sorted(per_n_l1.keys()):
        l1 = per_n_l1[n_val]
        ratio = l1 / prev_l1 if prev_l1 else 0
        print(f"    n={n_val}: ||w||₁={l1:.2f}"
              + (f" (ratio={ratio:.3f})" if prev_l1 else ""))
        prev_l1 = l1

    # Normalized interior weights
    print(f"\n  Normalized interior weights (α/||w||₁):")
    for n_val in sorted(per_n_weights.keys()):
        if n_val < 7:
            continue
        w = per_n_weights[n_val]
        l1 = per_n_l1[n_val]
        norm_int = {int_pair_names[i]: w[int_var_indices[i]] / l1
                    for i in range(len(int_var_indices))}
        vals = ", ".join(f"{p}={v:+.4f}" for p, v in
                         sorted(norm_int.items()) if abs(v) > 0.001)
        print(f"    n={n_val}: {vals}")

    # ═══════════════════════════════════════════════════════════
    # TEST 2: Interior contribution decomposition
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("TEST 2: Interior contribution decomposition")
    print("=" * 70)
    print("For each zero edge, decompose gap into boundary + interior parts.")
    print()

    for n_val in [8, 9, 10, 11]:
        if n_val not in per_n_weights:
            continue
        w = per_n_weights[n_val]
        constraints = per_n_constraints_raw[n_val]
        A = np.array(constraints, dtype=float)

        # Boundary contribution: sum over boundary variables only
        bnd_contrib = A[:, :n_bnd] @ w[:n_bnd]
        int_contrib = A[:, n_bnd:] @ w[n_bnd:]
        total = A @ w

        print(f"  n={n_val}: {len(constraints)} zero-edges")
        print(f"    Boundary: min={bnd_contrib.min():.2f}, "
              f"max={bnd_contrib.max():.2f}, mean={bnd_contrib.mean():.2f}")
        print(f"    Interior: min={int_contrib.min():.2f}, "
              f"max={int_contrib.max():.2f}, mean={int_contrib.mean():.2f}")
        print(f"    Total:    min={total.min():.2f}, "
              f"max={total.max():.2f}, mean={total.mean():.2f}")

        # What fraction of the gap comes from interior?
        pos_int = np.sum(int_contrib > 0)
        neg_int = np.sum(int_contrib < 0)
        zero_int = np.sum(np.abs(int_contrib) < 1e-9)
        print(f"    Interior sign: pos={pos_int}, neg={neg_int}, zero={zero_int}")

    # ═══════════════════════════════════════════════════════════
    # TEST 3: Cascade structure — max cascade depth in zero edges
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("TEST 3: Zero-edge position change depth")
    print("=" * 70)
    print("How many interior positions change in zero edges?")
    print()

    for n_val in [7, 8, 9, 10, 11]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        max_depth = 0
        depth_dist = defaultdict(int)
        for u, v in exc_edges:
            fu = feat_vector(u, n_val, bnd, n_bnd, int_idx, n_vars)
            fv = feat_vector(v, n_val, bnd, n_bnd, int_idx, n_vars)
            if fu[k21] - fv[k21] == 0:
                # Count interior positions that change
                n_changed = sum(1 for j in range(2, n-2) if u[j] != v[j])
                max_depth = max(max_depth, n_changed)
                depth_dist[n_changed] += 1

        dt = time.time() - t0
        total = sum(depth_dist.values())
        print(f"  n={n_val}: max interior changes={max_depth}/{n-4} "
              f"({dt:.1f}s)")
        for d in sorted(depth_dist.keys()):
            pct = 100 * depth_dist[d] / total
            print(f"    {d} changes: {depth_dist[d]:>7} ({pct:.1f}%)")

    # ═══════════════════════════════════════════════════════════
    # TEST 4: Is the gap always ≥ C·(max_interior_Δ)?
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("TEST 4: Gap vs interior magnitude correlation")
    print("=" * 70)
    print("Does the gap scale with the interior Δ magnitude?")
    print()

    for n_val in [9, 10, 11]:
        if n_val not in per_n_weights:
            continue
        w = per_n_weights[n_val]
        constraints = per_n_constraints_raw[n_val]
        A = np.array(constraints, dtype=float)

        gaps = A @ w
        int_mag = np.sum(np.abs(A[:, n_bnd:]), axis=1)

        # Correlation
        corr = np.corrcoef(gaps, int_mag)[0, 1]

        # Gap / (1 + int_mag)
        ratios = gaps / (1 + int_mag)

        print(f"  n={n_val}: corr(gap, |int|)={corr:.3f}, "
              f"min(gap/(1+|int|))={ratios.min():.4f}, "
              f"mean(gap/(1+|int|))={ratios.mean():.4f}")

        # Classify by interior magnitude
        for threshold in [0, 5, 10, 20, 50]:
            mask = int_mag > threshold
            if np.any(mask):
                print(f"    |int|>{threshold}: {np.sum(mask)} edges, "
                      f"min_gap={gaps[mask].min():.2f}, "
                      f"mean_gap={gaps[mask].mean():.2f}")


if __name__ == '__main__':
    main()
