#!/usr/bin/env python3
"""
CONVERGENCE PROOF 28: LP-Based Structured Potential Search
==========================================================

For each n, solve a linear program to determine whether a structured
potential Φ(c) exists such that Φ(u) > Φ(v) for every edge u→v in the
bad-config transition DAG.

Potential families (increasing richness):
1. Separable:  Φ(c) = Σⱼ f(j, c[j])
2. Pair-based: Φ(c) = Σⱼ g(j, c[j], c[j+1 mod n])
3. Triple-based: Φ(c) = Σⱼ h(j, c[j-1], c[j], c[j+1])

Also tests on the excursion graph (much smaller than full graph).
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


def w1(j, n):
    if j == n - 1:
        return 0
    if j == n - 2:
        return 1
    return j + 1


def w2(j, n):
    if j == n - 1:
        return 0
    if 1 <= j <= n - 2:
        return n - 1 - j
    return n - 1


def psi(c, n):
    total = 0
    for j in range(n):
        ft = frontier_type(c[j], c[(j + 1) % n])
        if ft == 1:
            total += w1(j, n)
        elif ft == 2:
            total += w2(j, n)
    return total


def Q_val(c, n):
    return sum(1 for j in range(n)
               if c[j] == c[(j + 1) % n] and c[j] in (0, 1))


def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))


def solve_structured_lp(edges, feat_func, n_feat, name):
    """
    Solve: find w ∈ R^n_feat such that for every edge (u,v):
      Σ w[k] · (feat(u)[k] - feat(v)[k]) ≥ 1
    """
    ne = len(edges)
    if ne == 0:
        print(f"  {name}: no edges")
        return None

    # Build constraint matrix
    A = np.zeros((ne, n_feat))
    for ei, (u, v) in enumerate(edges):
        fu = feat_func(u)
        fv = feat_func(v)
        for k, val in fu.items():
            A[ei, k] += val
        for k, val in fv.items():
            A[ei, k] -= val

    # LP: min 0 s.t. A @ w >= 1  ⟺  -A @ w <= -1
    c_obj = np.zeros(n_feat)
    res = linprog(c_obj, A_ub=-A, b_ub=-np.ones(ne),
                  bounds=[(None, None)] * n_feat, method='highs')

    if res.success:
        w = res.x
        gaps = A @ w
        min_gap = gaps.min()
        print(f"  {name}: FEASIBLE ({n_feat} feats, {ne} edges, "
              f"min_gap={min_gap:.3f})")
        return w
    else:
        print(f"  {name}: INFEASIBLE ({n_feat} feats, {ne} edges)")
        return None


def analyze(n_val):
    ms, fs = build_system(n_val)
    n = n_val
    result = verify_system(ms, fs)
    assert result['valid']

    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    # ── Collect ALL edges ──
    edges = []
    anom_edges = []
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
                    edges.append((c, succ))
                    dfc = delta_fc(L, S, R, out)
                    if out != L and out != R:
                        anom_edges.append((c, succ, i, dfc))

    print(f"\n{'=' * 65}")
    print(f"n = {n}: {len(bad_list)} bad, {len(edges)} edges, "
          f"{len(anom_edges)} anomalous")
    print(f"{'=' * 65}")

    # ── Feature index builders ──

    # 1. Separable: f(j, v)
    sep_idx = {}
    idx = 0
    for j in range(n):
        for v in range(ms[j]):
            sep_idx[(j, v)] = idx
            idx += 1
    n_sep = idx

    def sep_feat(c):
        return {sep_idx[(j, c[j])]: 1 for j in range(n)}

    # 2. Pair: g(j, c[j], c[(j+1)%n])
    pair_idx = {}
    idx = 0
    for j in range(n):
        j1 = (j + 1) % n
        for a in range(ms[j]):
            for b in range(ms[j1]):
                pair_idx[(j, a, b)] = idx
                idx += 1
    n_pair = idx

    def pair_feat(c):
        return {pair_idx[(j, c[j], c[(j + 1) % n])]: 1 for j in range(n)}

    # 3. Triple: h(j, c[(j-1)%n], c[j], c[(j+1)%n])
    tri_idx = {}
    idx = 0
    for j in range(n):
        jm = (j - 1) % n
        jp = (j + 1) % n
        for a in range(ms[jm]):
            for b in range(ms[j]):
                for d in range(ms[jp]):
                    tri_idx[(j, a, b, d)] = idx
                    idx += 1
    n_tri = idx

    def tri_feat(c):
        return {tri_idx[(j, c[(j - 1) % n], c[j], c[(j + 1) % n])]: 1
                for j in range(n)}

    # ── Solve LPs on FULL graph ──
    print(f"\n  ── Full graph LPs ──")
    w_sep = solve_structured_lp(edges, sep_feat, n_sep, "Separable")
    w_pair = solve_structured_lp(edges, pair_feat, n_pair, "Pair-based")

    if n_tri <= 500:  # only for small n
        w_tri = solve_structured_lp(edges, tri_feat, n_tri, "Triple-based")
    else:
        print(f"  Triple-based: skipped ({n_tri} features)")
        w_tri = None

    # ── Build excursion graph ──
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

    anom_sources = set(c for c, _, _, _ in anom_edges)
    anom_target_map = defaultdict(list)
    for c, succ, i, dfc in anom_edges:
        anom_target_map[succ].append(c)

    # BFS from each anomalous target to find reachable anomalous sources
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
                # b is reached from some anomalous source(s)
                for src in anom_target_map.get(b, []):
                    if node != src:
                        exc_edges.add((src, node))
                    elif node == src:
                        exc_edges.add((src, node))
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt)
                    queue.append(nxt)

    exc_edges = list(exc_edges)
    exc_nodes = set()
    for a, b in exc_edges:
        exc_nodes.add(a)
        exc_nodes.add(b)

    print(f"\n  ── Excursion graph: {len(exc_nodes)} nodes, "
          f"{len(exc_edges)} edges ──")

    # Solve LPs on excursion graph
    if exc_edges:
        w_sep_e = solve_structured_lp(exc_edges, sep_feat, n_sep,
                                       "Exc-Separable")
        w_pair_e = solve_structured_lp(exc_edges, pair_feat, n_pair,
                                        "Exc-Pair-based")

        # If separable works on excursion graph, print the weights
        if w_sep_e is not None:
            print(f"\n  Separable excursion weights:")
            rev_sep = {v: k for k, v in sep_idx.items()}
            for i in range(n_sep):
                j, v = rev_sep[i]
                if abs(w_sep_e[i]) > 0.001:
                    print(f"    f({j}, {v}) = {w_sep_e[i]:.4f}")

        # If pair works on excursion graph, print weights
        if w_pair_e is not None:
            print(f"\n  Pair excursion weights (nonzero):")
            rev_pair = {v: k for k, v in pair_idx.items()}
            nz = [(i, w_pair_e[i]) for i in range(n_pair)
                  if abs(w_pair_e[i]) > 0.01]
            for i, wi in sorted(nz, key=lambda x: -abs(x[1]))[:30]:
                j, a, b = rev_pair[i]
                print(f"    g({j}, {a}, {b}) = {wi:.4f}")

    # ── If pair-based works on full graph, analyze weights ──
    if w_pair is not None:
        print(f"\n  ── Pair-based full-graph weight analysis ──")
        rev_pair = {v: k for k, v in pair_idx.items()}
        # Group by position
        for j in range(n):
            print(f"  Position {j}:")
            for idx_p in range(n_pair):
                if idx_p in rev_pair:
                    jj, a, b = rev_pair[idx_p]
                    if jj == j and abs(w_pair[idx_p]) > 0.001:
                        ft = frontier_type(a, b)
                        same = "=" if a == b else "≠"
                        print(f"    g({j},{a},{b}) [ft={ft}] = "
                              f"{w_pair[idx_p]:.4f}")

    # ── Also test: (fc, Ψ, Q) as linear combination ──
    print(f"\n  ── Linear α·fc + β·Ψ + γ·Q LP ──")
    fcpq_idx = {'fc': 0, 'psi': 1, 'Q': 2}
    n_fcpq = 3

    def fcpq_feat(c):
        return {0: fc_val(c, n), 1: psi(c, n), 2: Q_val(c, n)}

    solve_structured_lp(edges, fcpq_feat, n_fcpq, "α·fc+β·Ψ+γ·Q")

    # Extended: add fc², Ψ², Q², fc·Ψ, fc·Q, Ψ·Q
    n_fcpq2 = 9

    def fcpq2_feat(c):
        f = fc_val(c, n)
        p = psi(c, n)
        q = Q_val(c, n)
        return {0: f, 1: p, 2: q,
                3: f * f, 4: p * p, 5: q * q,
                6: f * p, 7: f * q, 8: p * q}

    solve_structured_lp(edges, fcpq2_feat, n_fcpq2,
                        "quadratic(fc,Ψ,Q)")

    return w_pair is not None


if __name__ == '__main__':
    for nv in range(5, 10):
        prod = 4 * 3 ** (nv - 2)
        if prod > 30000:
            break
        analyze(nv)
