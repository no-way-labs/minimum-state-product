#!/usr/bin/env python3
"""
CONVERGENCE PROOF 58: Position-Pair Potential Deep Analysis
============================================================

BREAKTHROUGH from proof57: Per-n position-pair potential
  Φ(c) = Σ_j w(j, c[j], c[j+1])
gives STRICT DECREASE on j-double-zero edges (δ=57 at n=8, δ=33 at n=9).

This script:
1. Extract per-n weights and analyze patterns
2. Check if it works on FULL zero-edge subgraph (not just jdz)
3. Check if it works on ALL excursion edges
4. Try universal parameterizations for w(j,a,b)
5. Test joint LP with best parameterization
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
    return sum(1 for j in range(2, n-2) if c[j] == 2 and c[(j+1) % n] == 1)

def int_j_20(c, n):
    return sum(j for j in range(2, n-2) if c[j] == 2 and c[(j+1) % n] == 0)


def solve_position_pair_lp(edges, n, ms, edge_type=""):
    """Solve position-pair LP: max δ s.t. Σ_j Δw(j,pair) + δ ≤ 0."""
    var_idx = {}
    n_vars = 0
    for j in range(n):
        m_j = ms[j]
        m_j1 = ms[(j+1) % n]
        for a in range(m_j):
            for b in range(m_j1):
                var_idx[(j, a, b)] = n_vars
                n_vars += 1

    E = len(edges)
    if E == 0:
        return 0.0, None, n_vars

    A_feat = np.zeros((E, n_vars))
    for ei, (u, v) in enumerate(edges):
        for j in range(n):
            a_u, b_u = u[j], u[(j+1) % n]
            a_v, b_v = v[j], v[(j+1) % n]
            if a_u != a_v or b_u != b_v:
                A_feat[ei, var_idx[(j, a_v, b_v)]] += 1
                A_feat[ei, var_idx[(j, a_u, b_u)]] -= 1

    total_vars = n_vars + 1
    c_obj = np.zeros(total_vars)
    c_obj[-1] = -1

    A_ub = np.zeros((E, total_vars))
    b_ub = np.zeros(E)
    A_ub[:, :n_vars] = A_feat
    A_ub[:, -1] = 1.0

    bounds = [(-100, 100)] * n_vars + [(0, None)]
    res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')

    if res.success:
        delta = res.x[-1]
        w = res.x[:n_vars]
        return delta, {k: w[v] for k, v in var_idx.items()}, n_vars
    else:
        return -1, None, n_vars


def main():
    # ═══════════════════════════════════════════════════════════
    # STEP 1: Position-pair LP on different edge types
    # ═══════════════════════════════════════════════════════════
    print("=" * 70)
    print("STEP 1: Position-pair LP on different edge types")
    print("=" * 70)
    print()

    for n_val in [8, 9, 10]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        all_edges = exc_edges
        zero_edges = [(u,v) for u,v in exc_edges
                      if int_21(v,n) - int_21(u,n) == 0]
        jdz_edges = [(u,v) for u,v in zero_edges
                     if int_j_20(v,n) - int_j_20(u,n) == 0]

        for etype, edges in [('ALL excursion', all_edges),
                             ('zero', zero_edges),
                             ('jdz', jdz_edges)]:
            delta, w, nv = solve_position_pair_lp(edges, n, ms)
            dt = time.time() - t0
            print(f"  n={n_val} {etype:>15}: δ={delta:>8.3f} "
                  f"({len(edges):>7} edges, {nv:>3} vars)")

    # ═══════════════════════════════════════════════════════════
    # STEP 2: Extract and analyze per-n weights
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 2: Per-n position-pair weights analysis")
    print("=" * 70)

    weights_by_n = {}
    for n_val in [7, 8, 9, 10]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        jdz_edges = [(u,v) for u,v in exc_edges
                     if int_21(v,n) - int_21(u,n) == 0 and
                        int_j_20(v,n) - int_j_20(u,n) == 0]

        delta, w, nv = solve_position_pair_lp(jdz_edges, n, ms)
        weights_by_n[n_val] = w
        dt = time.time() - t0

        print(f"\n  n={n_val}: δ={delta:.3f} ({dt:.1f}s)")
        if w is None:
            continue

        # Show weights for interior positions (2 ≤ j ≤ n-3)
        # Only show non-negligible weights
        print(f"    Interior weights (positions 2..{n-3}):")
        for j in range(2, n-2):
            parts = []
            for a in range(3):
                for b in range(3):
                    val = w.get((j, a, b), 0)
                    if abs(val) > 0.1:
                        parts.append(f"w({a},{b})={val:>7.2f}")
            if parts:
                print(f"      pos {j}: {', '.join(parts)}")

    # ═══════════════════════════════════════════════════════════
    # STEP 3: Check weight patterns across positions
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 3: Weight patterns across positions")
    print("=" * 70)

    for n_val in [9, 10]:
        w = weights_by_n.get(n_val)
        if w is None:
            continue
        ms_n, _ = build_system(n_val)
        n = n_val

        print(f"\n  n={n_val}: Weight as function of position")
        print(f"    {'pair':>6}", end="")
        for j in range(n):
            print(f"  pos{j:>2}", end="")
        print()

        for a in range(3):
            for b in range(3):
                if a >= ms_n[0] or b >= ms_n[1]:
                    continue
                vals = []
                for j in range(n):
                    m_j = ms_n[j]
                    m_j1 = ms_n[(j+1) % n]
                    if a < m_j and b < m_j1:
                        val = w.get((j, a, b), 0)
                        vals.append(f"{val:>7.2f}")
                    else:
                        vals.append(f"{'n/a':>7}")
                print(f"    ({a},{b}):", "".join(vals))

    # ═══════════════════════════════════════════════════════════
    # STEP 4: Universal parameterization search
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 4: Universal parameterization for position-pair weights")
    print("=" * 70)
    print()
    print("Testing: w(j,a,b) = α(a,b)*f(j) + β(a,b) for various f(j)")
    print("on j-double-zero edges across n=5..11")

    # Position functions to try
    def make_pos_funcs():
        return {
            'j': lambda j, n: j,
            'j²': lambda j, n: j*j,
            'j³': lambda j, n: j**3,
            'n-j': lambda j, n: n-j,
            '(n-j)²': lambda j, n: (n-j)**2,
            'j(n-j)': lambda j, n: j*(n-j),
            'j(n-1-j)': lambda j, n: j*(n-1-j),
            'min(j,n-j)': lambda j, n: min(j, n-j),
            'max(j,n-j)': lambda j, n: max(j, n-j),
        }

    pos_funcs = make_pos_funcs()

    for fname, f_func in pos_funcs.items():
        # Parameters: α(a,b) for 9 pairs, β(a,b) for 9 pairs = 18 interior params
        # + boundary: free weights for pos 0,1,n-2,n-1
        # Boundary: 4 positions × variable pair counts

        # For simplicity, use free boundary weights per position type
        # bot(0-1)*top(0-1) = 2*2=4 boundary pair types for pos 0
        # Actually, boundary weights are per-n because pair types depend on ms

        # Use a simpler parameterization: just interior with α(a,b)*f(j) + β(a,b)
        # For boundary positions, add fixed variables per table type

        n_interior = 18  # α(0..2, 0..2) + β(0..2, 0..2)
        # Boundary: bot has 2*3 pairs (pos0: binary × ternary)
        #           low has 3*3 pairs (pos1: ternary × ternary)
        #           high has 3*3 pairs
        #           top has 3*2 pairs (pos n-1: ternary × binary)
        n_boundary = 6 + 9 + 9 + 6  # bot, low, high, top
        n_params = n_interior + n_boundary

        # Map pair to boundary variable index
        # bot: (a,b) for a in {0,1}, b in {0,1,2} → indices 18..23
        # low: (a,b) for a in {0,1,2}, b in {0,1,2} → indices 24..32
        # high: (a,b) for a in {0,1,2}, b in {0,1,2} → indices 33..41
        # top: (a,b) for a in {0,1,2}, b in {0,1} → indices 42..47

        all_feats = []
        for n_val in range(5, 12):
            exc_edges, ms = build_excursion_graph(n_val)
            n = n_val

            for u, v in exc_edges:
                if int_21(v, n) - int_21(u, n) != 0:
                    continue
                if int_j_20(v, n) - int_j_20(u, n) != 0:
                    continue

                feat = np.zeros(n_params)
                for j in range(n):
                    a_u, b_u = u[j], u[(j+1) % n]
                    a_v, b_v = v[j], v[(j+1) % n]
                    if a_u == a_v and b_u == b_v:
                        continue

                    if j == 0:  # bot
                        idx_v = 18 + a_v * 3 + b_v
                        idx_u = 18 + a_u * 3 + b_u
                        feat[idx_v] += 1; feat[idx_u] -= 1
                    elif j == 1:  # low
                        idx_v = 24 + a_v * 3 + b_v
                        idx_u = 24 + a_u * 3 + b_u
                        feat[idx_v] += 1; feat[idx_u] -= 1
                    elif j == n-2:  # high
                        idx_v = 33 + a_v * 3 + b_v
                        idx_u = 33 + a_u * 3 + b_u
                        feat[idx_v] += 1; feat[idx_u] -= 1
                    elif j == n-1:  # top
                        idx_v = 42 + a_v * 2 + b_v
                        idx_u = 42 + a_u * 2 + b_u
                        feat[idx_v] += 1; feat[idx_u] -= 1
                    else:  # interior
                        fj = f_func(j, n)
                        # w(j,a,b) = α(a,b)*f(j) + β(a,b)
                        # Δw = [α(av,bv)*f(j) + β(av,bv)] - [α(au,bu)*f(j) + β(au,bu)]
                        idx_v_a = a_v * 3 + b_v  # α index
                        idx_u_a = a_u * 3 + b_u
                        idx_v_b = 9 + a_v * 3 + b_v  # β index
                        idx_u_b = 9 + a_u * 3 + b_u
                        feat[idx_v_a] += fj; feat[idx_u_a] -= fj
                        feat[idx_v_b] += 1; feat[idx_u_b] -= 1

                all_feats.append(feat)

        A = np.array(all_feats)
        E = A.shape[0]

        # LP: max δ s.t. A@p + δ ≤ 0
        total_vars = n_params + 1
        c_obj = np.zeros(total_vars)
        c_obj[-1] = -1

        A_ub = np.zeros((E, total_vars))
        b_ub = np.zeros(E)
        A_ub[:, :n_params] = A
        A_ub[:, -1] = 1.0

        bounds = [(-1000, 1000)] * n_params + [(0, None)]
        res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')

        if res.success:
            delta = res.x[-1]
            marker = " ← WORKS!" if delta > 1e-6 else ""
            print(f"  f(j) = {fname:>15}: δ = {delta:>10.4f}  ({E} edges){marker}")
        else:
            print(f"  f(j) = {fname:>15}: INFEASIBLE")

    # ═══════════════════════════════════════════════════════════
    # STEP 5: Two-term parameterization
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 5: Two-term parameterization w(j,a,b) = α*f1(j) + β*f2(j) + γ")
    print("=" * 70)

    import itertools
    func_list = [
        ('j', lambda j, n: j),
        ('j²', lambda j, n: j*j),
        ('n-j', lambda j, n: n-j),
        ('(n-j)²', lambda j, n: (n-j)**2),
        ('j(n-j)', lambda j, n: j*(n-j)),
    ]

    for (f1name, f1), (f2name, f2) in itertools.combinations(func_list, 2):
        # 3 coefficients per pair × 9 pairs = 27 interior params
        # + 30 boundary params
        n_int = 27  # α(a,b), β(a,b), γ(a,b) for 9 pairs
        n_bnd = 30
        n_params = n_int + n_bnd

        all_feats = []
        for n_val in range(5, 12):
            exc_edges, ms = build_excursion_graph(n_val)
            n = n_val

            for u, v in exc_edges:
                if int_21(v, n) - int_21(u, n) != 0:
                    continue
                if int_j_20(v, n) - int_j_20(u, n) != 0:
                    continue

                feat = np.zeros(n_params)
                for j in range(n):
                    a_u, b_u = u[j], u[(j+1) % n]
                    a_v, b_v = v[j], v[(j+1) % n]
                    if a_u == a_v and b_u == b_v:
                        continue

                    if j == 0:
                        idx_v = 27 + a_v * 3 + b_v
                        idx_u = 27 + a_u * 3 + b_u
                        feat[idx_v] += 1; feat[idx_u] -= 1
                    elif j == 1:
                        idx_v = 33 + a_v * 3 + b_v
                        idx_u = 33 + a_u * 3 + b_u
                        feat[idx_v] += 1; feat[idx_u] -= 1
                    elif j == n-2:
                        idx_v = 42 + a_v * 3 + b_v
                        idx_u = 42 + a_u * 3 + b_u
                        feat[idx_v] += 1; feat[idx_u] -= 1
                    elif j == n-1:
                        idx_v = 48 + a_v * 2 + b_v
                        idx_u = 48 + a_u * 2 + b_u
                        feat[idx_v] += 1; feat[idx_u] -= 1
                    else:
                        fj1 = f1(j, n)
                        fj2 = f2(j, n)
                        pair_base_v = a_v * 3 + b_v
                        pair_base_u = a_u * 3 + b_u
                        # α(a,b)*f1(j): indices 0..8
                        feat[pair_base_v] += fj1; feat[pair_base_u] -= fj1
                        # β(a,b)*f2(j): indices 9..17
                        feat[9+pair_base_v] += fj2; feat[9+pair_base_u] -= fj2
                        # γ(a,b)*1: indices 18..26
                        feat[18+pair_base_v] += 1; feat[18+pair_base_u] -= 1

                all_feats.append(feat)

        A = np.array(all_feats)
        E = A.shape[0]

        total_vars = n_params + 1
        c_obj = np.zeros(total_vars)
        c_obj[-1] = -1

        A_ub = np.zeros((E, total_vars))
        b_ub = np.zeros(E)
        A_ub[:, :n_params] = A
        A_ub[:, -1] = 1.0

        bounds = [(-1000, 1000)] * n_params + [(0, None)]
        res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')

        if res.success:
            delta = res.x[-1]
            marker = " ← WORKS!" if delta > 1e-6 else ""
            print(f"  f1={f1name:>8}, f2={f2name:>8}: δ = {delta:>10.4f}{marker}")
        else:
            print(f"  f1={f1name:>8}, f2={f2name:>8}: INFEASIBLE")

    # ═══════════════════════════════════════════════════════════
    # STEP 6: Try on FULL zero-edge or ALL excursion edges
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 6: Position-pair LP on zero edges and all excursion edges")
    print("=" * 70)

    # Use the best parameterization found above (or per-n)
    for n_val in [8, 9, 10]:
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        zero_edges = [(u,v) for u,v in exc_edges
                      if int_21(v,n) - int_21(u,n) == 0]

        for etype, edges in [('zero', zero_edges), ('ALL', exc_edges)]:
            delta, w, nv = solve_position_pair_lp(edges, n, ms)
            print(f"  n={n_val} {etype:>5}: δ={delta:>8.3f} "
                  f"({len(edges):>7} edges, {nv} vars)")

    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print()
    print("Position-pair potential Φ(c) = Σ_j w(j,c[j],c[j+1]):")
    print("  Per-n: WORKS on jdz edges")
    print("  Universal parameterization: depends on Step 4-5 results")


if __name__ == '__main__':
    main()
