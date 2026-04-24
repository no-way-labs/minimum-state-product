#!/usr/bin/env python3
"""
CONVERGENCE PROOF 61: Extended Boundary Parameterization
=========================================================

α*j+β BREAKS at n=12 (δ=0). Per-n position-pair LP works (δ=13 at n=11).
The non-linearity is at boundary-adjacent positions.

Try:
1. Extended boundary: pos 0,1,2 and n-3,n-2,n-1 are FREE
   Interior (pos 3..n-4): α*j + β
   Total: 18 (interior) + 6*9 (boundary) = 72 vars

2. Even more extended: pos 0,1,2,3 and n-4,n-3,n-2,n-1
   Interior (pos 4..n-5): α*j + β

3. Try α*min(j-2, n-2-j) + β for interior (distance from boundary)

4. Structural analysis: why does α*j+β fail?
   Analyze the 183 n=12 failures.
"""

import sys
import os
import time
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict


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


def int_21(c, n):
    return sum(1 for j in range(2, n-2) if c[j] == 2 and c[(j+1)%n] == 1)

def int_j_20(c, n):
    return sum(j for j in range(2, n-2) if c[j] == 2 and c[(j+1)%n] == 0)


def build_feat_extended(u, v, n, ms, n_bnd_left, n_bnd_right, int_func):
    """
    Extended boundary parameterization.
    Boundary: positions 0..n_bnd_left-1 and n-n_bnd_right..n-1
    Interior: positions n_bnd_left..n-n_bnd_right-1, w = α(a,b)*f(j,n) + β(a,b)

    Variables:
    - 9*n_bnd_left (left boundary, ternary×ternary except pos0 which is 2×3)
    - 9*n_bnd_right (right boundary)
    - 18 (α(a,b) and β(a,b) for interior)
    """
    # Simplification: all boundary pairs get 9 vars (even if some are unused due to m<3)
    n_left = 9 * n_bnd_left
    n_right = 9 * n_bnd_right
    n_int = 18
    np_total = n_left + n_right + n_int

    feat = np.zeros(np_total)

    for j in range(n):
        au, bu = u[j], u[(j+1) % n]
        av, bv = v[j], v[(j+1) % n]
        if au == av and bu == bv:
            continue

        if j < n_bnd_left:  # Left boundary
            base = 9 * j
            feat[base + av*3+bv] += 1; feat[base + au*3+bu] -= 1
        elif j >= n - n_bnd_right:  # Right boundary
            bnd_idx = j - (n - n_bnd_right)  # 0..n_bnd_right-1
            base = n_left + 9 * bnd_idx
            feat[base + av*3+bv] += 1; feat[base + au*3+bu] -= 1
        else:  # Interior
            pv = av*3+bv; pu = au*3+bu
            fj = int_func(j, n)
            base = n_left + n_right
            feat[base + pv] += fj; feat[base + pu] -= fj
            feat[base + 9 + pv] += 1; feat[base + 9 + pu] -= 1

    return feat, np_total


def test_parameterization(name, n_bnd_left, n_bnd_right, int_func, edges_by_n, max_train_n):
    """Test a parameterization on jdz edges."""
    all_feats = []
    for n_val in range(5, max_train_n + 1):
        exc_edges, ms = edges_by_n[n_val]
        n = n_val
        if n <= n_bnd_left + n_bnd_right + 1:
            continue  # No interior positions
        for u, v in exc_edges:
            if int_21(v, n) - int_21(u, n) != 0:
                continue
            if int_j_20(v, n) - int_j_20(u, n) != 0:
                continue
            feat, np_t = build_feat_extended(u, v, n, ms, n_bnd_left, n_bnd_right, int_func)
            all_feats.append(feat)

    if not all_feats:
        return -1, np_t, None

    A = np.array(all_feats)
    E = A.shape[0]
    tv = np_t + 1
    c_obj = np.zeros(tv); c_obj[-1] = -1
    A_ub = np.zeros((E, tv)); b_ub = np.zeros(E)
    A_ub[:, :np_t] = A; A_ub[:, -1] = 1.0
    bounds = [(-1000, 1000)] * np_t + [(0, None)]
    res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')

    d = res.x[-1] if res.success else -1
    p = res.x[:np_t] if res.success else None
    return d, np_t, p


def main():
    print("=" * 70)
    print("Building excursion graphs...")
    print("=" * 70)

    edges_by_n = {}
    for n_val in range(5, 13):
        t0 = time.time()
        edges_by_n[n_val] = build_excursion_graph(n_val)
        print(f"  n={n_val}: {len(edges_by_n[n_val][0])} edges ({time.time()-t0:.1f}s)")

    # ═══════════════════════════════════════════════════════════
    # STEP 1: Extended boundary parameterizations on jdz edges
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 1: Extended boundary on jdz edges, n=5..12")
    print("=" * 70)

    int_j = lambda j, n: j
    int_nj = lambda j, n: n - j
    int_djn = lambda j, n: min(j, n-1-j)  # distance from boundary

    configs = [
        # (name, n_bnd_left, n_bnd_right, func)
        ("L=2,R=2,f=j", 2, 2, int_j),
        ("L=3,R=2,f=j", 3, 2, int_j),
        ("L=2,R=3,f=j", 2, 3, int_j),
        ("L=3,R=3,f=j", 3, 3, int_j),
        ("L=4,R=3,f=j", 4, 3, int_j),
        ("L=3,R=4,f=j", 3, 4, int_j),
        ("L=4,R=4,f=j", 4, 4, int_j),
        ("L=5,R=5,f=j", 5, 5, int_j),
        ("L=3,R=3,f=n-j", 3, 3, int_nj),
        ("L=3,R=3,f=d(j)", 3, 3, int_djn),
    ]

    print(f"\n  {'Config':>25} | {'#vars':>5} | {'δ':>10}")
    print(f"  {'-'*45}")

    for name, nbl, nbr, func in configs:
        t0 = time.time()
        d, nv, p = test_parameterization(name, nbl, nbr, func, edges_by_n, 12)
        dt = time.time() - t0
        marker = " ← WORKS!" if d > 1e-6 else ""
        print(f"  {name:>25} | {nv:>5} | {d:>10.4f} ({dt:.1f}s){marker}")

    # ═══════════════════════════════════════════════════════════
    # STEP 2: δ decay for best parameterization
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 2: δ decay for extended boundary configs")
    print("=" * 70)

    # Test the best configs from Step 1
    best_configs = [
        ("L=3,R=3,f=j", 3, 3, int_j),
        ("L=4,R=4,f=j", 4, 4, int_j),
        ("L=5,R=5,f=j", 5, 5, int_j),
    ]

    for name, nbl, nbr, func in best_configs:
        print(f"\n  {name}:")
        print(f"  {'Max n':>6} | {'δ':>10}")
        print(f"  {'-'*20}")
        for max_n in range(max(5, nbl+nbr+2), 13):
            d, nv, _ = test_parameterization(name, nbl, nbr, func, edges_by_n, max_n)
            print(f"  n≤{max_n:>2}   | {d:>10.4f}")

    # ═══════════════════════════════════════════════════════════
    # STEP 3: ALL excursion edges (not just jdz) with extended boundary
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 3: Extended boundary on ALL excursion edges")
    print("=" * 70)

    # Test L=3,R=3,f=j on ALL edges
    for nbl, nbr in [(3, 3), (4, 4)]:
        name = f"L={nbl},R={nbr},f=j"
        all_feats = []
        for n_val in range(5, 12):  # n=5..11 (skip 12 for ALL)
            exc_edges, ms = edges_by_n[n_val]
            n = n_val
            if n <= nbl + nbr + 1:
                continue
            for u, v in exc_edges:
                feat, np_t = build_feat_extended(u, v, n, ms, nbl, nbr, int_j)
                all_feats.append(feat)

        if not all_feats:
            continue
        A = np.array(all_feats)
        E = A.shape[0]
        tv = np_t + 1
        c_obj = np.zeros(tv); c_obj[-1] = -1
        A_ub = np.zeros((E, tv)); b_ub = np.zeros(E)
        A_ub[:, :np_t] = A; A_ub[:, -1] = 1.0
        bounds = [(-1000, 1000)] * np_t + [(0, None)]
        res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')

        d = res.x[-1] if res.success else -1
        p_all = res.x[:np_t] if res.success else None
        print(f"  {name} (ALL, n≤11): δ = {d:.4f} ({np_t} vars, {E} edges)")

        # Test on n=12
        if p_all is not None and d > 1e-6:
            exc_12, ms_12 = edges_by_n[12]
            n_fail = 0; n_test = 0
            for u, v in exc_12:
                feat, _ = build_feat_extended(u, v, 12, ms_12, nbl, nbr, int_j)
                gain = -np.dot(p_all, feat)
                n_test += 1
                if gain < 1e-8:
                    n_fail += 1
            print(f"    n=12 test: {n_fail}/{n_test} failures")

    # ═══════════════════════════════════════════════════════════
    # SUMMARY
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print()
    print("The key question: does ANY parameterization stabilize for all n?")
    print("If δ→0 for all tried forms, a different proof strategy is needed.")
    print()
    print("Per-n position-pair LP ALWAYS works (verified n=5..11).")
    print("The challenge: proving feasibility for all n analytically.")


if __name__ == '__main__':
    main()
