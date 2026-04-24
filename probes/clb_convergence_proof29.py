#!/usr/bin/env python3
"""
CONVERGENCE PROOF 29: Structured Pair Potential Analysis
========================================================

From proof28: pair-based potential is FEASIBLE on the excursion graph
for all tested n=5..9. This script:

1. Tests finer potential families to find minimal structure needed:
   - fc with position weights (n params)
   - weighted Q (n params)
   - frontier-type potential (3n params)
   - pair potential (Σ mj*mj+1 params)

2. Computes L1-minimal pair potential (sparsest solution)

3. Tests parameterized weight families:
   - g(j, a, b) = α(a,b) · j + β(a,b) for interior positions

4. Checks if a SINGLE formula works for all n
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


def fc_val(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


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

    # Build adjacencies
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

    # BFS from each anomalous target
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


def solve_lp(edges, feat_func, n_feat, name, minimize_l1=False):
    """Solve LP for potential feasibility or L1-minimization."""
    ne = len(edges)
    if ne == 0:
        return None

    A = np.zeros((ne, n_feat))
    for ei, (u, v) in enumerate(edges):
        fu = feat_func(u)
        fv = feat_func(v)
        for k, val in fu.items():
            A[ei, k] += val
        for k, val in fv.items():
            A[ei, k] -= val

    if minimize_l1:
        # min Σ(w+ + w-) s.t. A(w+ - w-) ≥ 1, w+,w- ≥ 0
        c_obj = np.ones(2 * n_feat)
        A_split = np.hstack([-A, A])  # -A·w+ + A·w- ≤ -1
        b_ub = -np.ones(ne)
        bounds = [(0, None)] * (2 * n_feat)
        res = linprog(c_obj, A_ub=A_split, b_ub=b_ub,
                      bounds=bounds, method='highs')
        if res.success:
            w = res.x[:n_feat] - res.x[n_feat:]
            gaps = A @ w
            l1 = np.sum(np.abs(w))
            print(f"  {name} (L1-min): FEASIBLE, ||w||₁={l1:.2f}, "
                  f"min_gap={gaps.min():.3f}")
            return w
        else:
            print(f"  {name} (L1-min): INFEASIBLE")
            return None
    else:
        c_obj = np.zeros(n_feat)
        res = linprog(c_obj, A_ub=-A, b_ub=-np.ones(ne),
                      bounds=[(None, None)] * n_feat, method='highs')
        if res.success:
            w = res.x
            gaps = A @ w
            print(f"  {name}: FEASIBLE ({n_feat} feats, {ne} edges, "
                  f"min_gap={gaps.min():.3f})")
            return w
        else:
            print(f"  {name}: INFEASIBLE ({n_feat} feats, {ne} edges)")
            return None


def analyze(n_val):
    exc_edges, ms = build_excursion_graph(n_val)
    n = n_val

    exc_nodes = set()
    for a, b in exc_edges:
        exc_nodes.add(a)
        exc_nodes.add(b)

    print(f"\n{'=' * 65}")
    print(f"n = {n}: excursion graph {len(exc_nodes)} nodes, "
          f"{len(exc_edges)} edges")
    print(f"{'=' * 65}")

    # ── Feature families ──

    # 1. fc with position weights: Σ wⱼ · 1[c[j]≠c[j+1]]
    def fc_w_feat(c):
        return {j: 1 for j in range(n) if c[j] != c[(j + 1) % n]}

    # 2. Weighted Q: Σ wⱼ · 1[c[j]=c[j+1] ∈ {0,1}]
    def q_w_feat(c):
        r = {}
        for j in range(n):
            if c[j] == c[(j + 1) % n] and c[j] in (0, 1):
                r[j] = 1
        return r

    # 3. Frontier-type: g(j, ft) for ft ∈ {0,1,2}
    ft_idx = {}
    idx = 0
    for j in range(n):
        for ft in range(3):
            ft_idx[(j, ft)] = idx
            idx += 1
    n_ft = idx

    def ft_feat(c):
        return {ft_idx[(j, frontier_type(c[j], c[(j + 1) % n]))]: 1
                for j in range(n)}

    # 4. Pair: g(j, c[j], c[j+1])
    pair_idx = {}
    pair_rev = {}
    idx = 0
    for j in range(n):
        j1 = (j + 1) % n
        for a in range(ms[j]):
            for b in range(ms[j1]):
                pair_idx[(j, a, b)] = idx
                pair_rev[idx] = (j, a, b)
                idx += 1
    n_pair = idx

    def pair_feat(c):
        return {pair_idx[(j, c[j], c[(j + 1) % n])]: 1 for j in range(n)}

    # 5. Specific (2,1) frontier only: Σ wⱼ · 1[(c[j],c[j+1])=(2,1)]
    def f21_feat(c):
        r = {}
        for j in range(n):
            if c[j] == 2 and c[(j + 1) % n] == 1:
                r[j] = 1
        return r

    # 6. Type-2 frontiers only: Σ wⱼ · 1[ft(j)=2]
    def ft2_feat(c):
        r = {}
        for j in range(n):
            if frontier_type(c[j], c[(j + 1) % n]) == 2:
                r[j] = 1
        return r

    # ── Test hierarchy ──
    print(f"\n  ── Potential family hierarchy ──")
    solve_lp(exc_edges, fc_w_feat, n, "fc-weighted")
    solve_lp(exc_edges, q_w_feat, n, "Q-weighted")
    solve_lp(exc_edges, f21_feat, n, "(2,1)-only")
    solve_lp(exc_edges, ft2_feat, n, "type-2-only")
    solve_lp(exc_edges, ft_feat, n_ft, "frontier-type")

    # ── L1-minimal pair potential ──
    print(f"\n  ── L1-minimal pair potential ──")
    w_l1 = solve_lp(exc_edges, pair_feat, n_pair, "Pair",
                     minimize_l1=True)

    if w_l1 is not None:
        # Print nonzero weights grouped by pair value
        print(f"\n  Nonzero weights by pair (a,b):")
        pair_groups = defaultdict(list)
        for i in range(n_pair):
            if abs(w_l1[i]) > 0.01:
                j, a, b = pair_rev[i]
                pair_groups[(a, b)].append((j, w_l1[i]))

        for (a, b) in sorted(pair_groups.keys()):
            ft = frontier_type(a, b)
            entries = sorted(pair_groups[(a, b)])
            wts = ", ".join(f"j={j}:{w:.1f}" for j, w in entries)
            print(f"    ({a},{b}) [ft={ft}]: {wts}")

    # ── Test parameterized: g(j,a,b) = α(a,b)·(j-1) + β(a,b) ──
    # For interior positions 2..n-3, the weight at (j, a, b) should be
    # α(a,b)·(j-1) + β(a,b). Boundary positions get free weights.
    # Parameters: 9 pairs × 2 (α, β) for interior + boundary weights
    print(f"\n  ── Parameterized interior weights ──")
    # Interior pairs: (a,b) with a,b ∈ {0,1,2} = 9 combinations
    # For each pair (a,b), weight at interior position j = α(a,b)·j + β(a,b)
    # Boundary positions (0, 1, n-2, n-1): free weights per (j, a, b)

    # Count boundary features
    bnd_feat_map = {}
    idx = 0
    for j in [0, 1, n - 2, n - 1]:
        j1 = (j + 1) % n
        for a in range(ms[j]):
            for b in range(ms[j1]):
                bnd_feat_map[(j, a, b)] = idx
                idx += 1
    n_bnd = idx

    # Interior parameterized features: for each (a,b), two params: α, β
    int_pairs = [(a, b) for a in range(3) for b in range(3)]
    int_feat_alpha = {}
    int_feat_beta = {}
    for pi, (a, b) in enumerate(int_pairs):
        int_feat_alpha[(a, b)] = n_bnd + 2 * pi
        int_feat_beta[(a, b)] = n_bnd + 2 * pi + 1
    n_param = n_bnd + 18

    def param_feat(c):
        r = {}
        for j in range(n):
            j1 = (j + 1) % n
            a, b = c[j], c[j1]
            if j in [0, 1, n - 2, n - 1]:
                key = (j, a, b)
                if key in bnd_feat_map:
                    r[bnd_feat_map[key]] = r.get(bnd_feat_map[key], 0) + 1
            else:
                # Interior: weight = α(a,b)·j + β(a,b)
                ap = int_feat_alpha[(a, b)]
                bp = int_feat_beta[(a, b)]
                r[ap] = r.get(ap, 0) + j
                r[bp] = r.get(bp, 0) + 1
        return r

    w_param = solve_lp(exc_edges, param_feat, n_param, "parameterized")

    if w_param is not None:
        print(f"\n  Parameterized weights:")
        print(f"  Boundary weights:")
        rev_bnd = {v: k for k, v in bnd_feat_map.items()}
        for i in range(n_bnd):
            if abs(w_param[i]) > 0.01:
                j, a, b = rev_bnd[i]
                print(f"    g({j},{a},{b}) = {w_param[i]:.4f}")
        print(f"  Interior: g(j,a,b) = α(a,b)·j + β(a,b)")
        for a, b in int_pairs:
            ai = int_feat_alpha[(a, b)]
            bi = int_feat_beta[(a, b)]
            alpha = w_param[ai]
            beta = w_param[bi]
            if abs(alpha) > 0.01 or abs(beta) > 0.01:
                ft = frontier_type(a, b)
                print(f"    ({a},{b}) [ft={ft}]: α={alpha:.4f}, β={beta:.4f}")

    # ── Even simpler: interior g depends ONLY on frontier type ──
    # g(j, ft) = α(ft)·j + β(ft) for interior, free for boundary
    print(f"\n  ── Interior frontier-type parameterized ──")
    # 3 frontier types × 2 params = 6 interior params + boundary
    int_ft_alpha = {}
    int_ft_beta = {}
    for ft in range(3):
        int_ft_alpha[ft] = n_bnd + 2 * ft
        int_ft_beta[ft] = n_bnd + 2 * ft + 1
    n_ft_param = n_bnd + 6

    def ft_param_feat(c):
        r = {}
        for j in range(n):
            j1 = (j + 1) % n
            a, b = c[j], c[j1]
            if j in [0, 1, n - 2, n - 1]:
                key = (j, a, b)
                if key in bnd_feat_map:
                    r[bnd_feat_map[key]] = r.get(bnd_feat_map[key], 0) + 1
            else:
                ft = frontier_type(a, b)
                ap = int_ft_alpha[ft]
                bp = int_ft_beta[ft]
                r[ap] = r.get(ap, 0) + j
                r[bp] = r.get(bp, 0) + 1
        return r

    solve_lp(exc_edges, ft_param_feat, n_ft_param,
             "ft-parameterized")


if __name__ == '__main__':
    for nv in range(5, 10):
        prod = 4 * 3 ** (nv - 2)
        if prod > 30000:
            break
        analyze(nv)
