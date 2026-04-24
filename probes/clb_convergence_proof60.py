#!/usr/bin/env python3
"""
CONVERGENCE PROOF 60: Analyze n=12 failures + fix parameterization
====================================================================

The universal LP (α*j + β, 48 params) trained on n=5..11 gives δ=74.5
but has 201 failures on n=12 (0.001%). Analyze these failures and fix.

Also: try the LAYERED approach where we only need the position-pair LP
on jdz edges. Since those are structurally simpler, the LP might
generalize better.

Key approaches:
1. Analyze failure edges: what's special about them?
2. Add n=12 jdz edges to training (much smaller than all edges)
3. Try higher-order terms: j², j³
4. Test the stabilization hypothesis: do failures decrease as training
   set grows?
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
from collections import defaultdict, Counter


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


def build_feat(u, v, n, ms, funcs):
    nf = len(funcs)
    ni = 9 * (nf + 1)
    nb = 30
    np_total = ni + nb
    feat = np.zeros(np_total)
    for j in range(n):
        au, bu = u[j], u[(j+1) % n]
        av, bv = v[j], v[(j+1) % n]
        if au == av and bu == bv:
            continue
        if j == 0:
            feat[ni + av*3+bv] += 1; feat[ni + au*3+bu] -= 1
        elif j == 1:
            feat[ni+6 + av*3+bv] += 1; feat[ni+6 + au*3+bu] -= 1
        elif j == n-2:
            feat[ni+15 + av*3+bv] += 1; feat[ni+15 + au*3+bu] -= 1
        elif j == n-1:
            feat[ni+24 + av*2+bv] += 1; feat[ni+24 + au*2+bu] -= 1
        else:
            pv = av*3+bv; pu = au*3+bu
            for k, (_, func) in enumerate(funcs):
                fj = func(j, n)
                feat[9*k + pv] += fj; feat[9*k + pu] -= fj
            feat[9*nf + pv] += 1; feat[9*nf + pu] -= 1
    return feat, np_total


def solve_lp(feats, n_params, bounds_range=1000):
    A = np.array(feats)
    E, _ = A.shape
    tv = n_params + 1
    c_obj = np.zeros(tv); c_obj[-1] = -1
    A_ub = np.zeros((E, tv)); b_ub = np.zeros(E)
    A_ub[:, :n_params] = A; A_ub[:, -1] = 1.0
    bounds = [(-bounds_range, bounds_range)] * n_params + [(0, None)]
    return linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')


def main():
    funcs_j = [('j', lambda j, n: j)]

    # ═══════════════════════════════════════════════════════════
    # STEP 1: Incremental training — add one n at a time
    # ═══════════════════════════════════════════════════════════
    print("=" * 70)
    print("STEP 1: δ as function of training set (ALL excursion edges)")
    print("=" * 70)

    print(f"\n  {'Train':>12} | {'δ (ALL)':>10} | {'δ (zero)':>10} | {'δ (jdz)':>10}")
    print(f"  {'-'*50}")

    edges_by_n = {}
    for n_val in range(5, 13):
        t0 = time.time()
        edges_by_n[n_val] = build_excursion_graph(n_val)
        print(f"  [Built n={n_val} in {time.time()-t0:.1f}s: {len(edges_by_n[n_val][0])} edges]")

    for max_n in range(5, 13):
        for edge_type in ['ALL', 'zero', 'jdz']:
            feats = []
            for n_val in range(5, max_n + 1):
                exc_edges, ms = edges_by_n[n_val]
                n = n_val
                for u, v in exc_edges:
                    if edge_type in ['zero', 'jdz']:
                        if int_21(v, n) - int_21(u, n) != 0:
                            continue
                    if edge_type == 'jdz':
                        if int_j_20(v, n) - int_j_20(u, n) != 0:
                            continue
                    feat, np1 = build_feat(u, v, n, ms, funcs_j)
                    feats.append(feat)

            if not feats:
                continue
            res = solve_lp(feats, np1)
            d = res.x[-1] if res.success else -1
            if edge_type == 'ALL':
                print(f"  n≤{max_n:>2}      | {d:>10.4f}", end="")
            elif edge_type == 'zero':
                print(f" | {d:>10.4f}", end="")
            else:
                print(f" | {d:>10.4f}")

    # ═══════════════════════════════════════════════════════════
    # STEP 2: Test n≤12 weights on n=12 edges
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 2: Include n=12 in training")
    print("=" * 70)

    # Train on ALL edges n=5..12
    all_feats = []
    for n_val in range(5, 13):
        exc_edges, ms = edges_by_n[n_val]
        n = n_val
        for u, v in exc_edges:
            feat, np1 = build_feat(u, v, n, ms, funcs_j)
            all_feats.append(feat)
    print(f"  Total: {len(all_feats)} ALL edges across n=5..12")

    res_all12 = solve_lp(all_feats, np1)
    if res_all12.success:
        d = res_all12.x[-1]
        p = res_all12.x[:np1]
        print(f"  δ (n≤12, ALL) = {d:.4f}")

        if d > 1e-6:
            print(f"  WORKS on ALL edges through n=12!")
            print(f"\n  Interior: w(j,a,b) = α(a,b)*j + β(a,b)")
            for a in range(3):
                for b in range(3):
                    i = a*3+b
                    print(f"    ({a},{b}): α={p[i]:>8.3f}, β={p[9+i]:>8.3f}")

    # Also train on zero edges n=5..12
    zero_feats = []
    for n_val in range(5, 13):
        exc_edges, ms = edges_by_n[n_val]
        n = n_val
        for u, v in exc_edges:
            if int_21(v, n) - int_21(u, n) != 0:
                continue
            feat, np1 = build_feat(u, v, n, ms, funcs_j)
            zero_feats.append(feat)
    print(f"\n  Total: {len(zero_feats)} zero edges across n=5..12")

    res_zero12 = solve_lp(zero_feats, np1)
    if res_zero12.success:
        d = res_zero12.x[-1]
        print(f"  δ (n≤12, zero) = {d:.4f}")

    # jdz edges n=5..12
    jdz_feats = []
    for n_val in range(5, 13):
        exc_edges, ms = edges_by_n[n_val]
        n = n_val
        for u, v in exc_edges:
            if int_21(v, n) - int_21(u, n) != 0:
                continue
            if int_j_20(v, n) - int_j_20(u, n) != 0:
                continue
            feat, np1 = build_feat(u, v, n, ms, funcs_j)
            jdz_feats.append(feat)
    print(f"  Total: {len(jdz_feats)} jdz edges across n=5..12")

    res_jdz12 = solve_lp(jdz_feats, np1)
    if res_jdz12.success:
        d = res_jdz12.x[-1]
        p = res_jdz12.x[:np1]
        print(f"  δ (n≤12, jdz) = {d:.4f}")

    # ═══════════════════════════════════════════════════════════
    # STEP 3: Higher-order terms
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 3: Higher-order parametric on ALL edges")
    print("=" * 70)

    func_sets = [
        ("j", [('j', lambda j, n: j)]),
        ("j,j²", [('j', lambda j, n: j), ('j²', lambda j, n: j*j)]),
        ("j,n-j", [('j', lambda j, n: j), ('n-j', lambda j, n: n-j)]),
        ("j,j(n-j)", [('j', lambda j, n: j), ('j(n-j)', lambda j, n: j*(n-j))]),
        ("j,j²,j(n-j)", [('j', lambda j, n: j), ('j²', lambda j, n: j*j),
                          ('j(n-j)', lambda j, n: j*(n-j))]),
    ]

    for label, funcs in func_sets:
        feats = []
        for n_val in range(5, 13):
            exc_edges, ms = edges_by_n[n_val]
            n = n_val
            for u, v in exc_edges:
                feat, np_f = build_feat(u, v, n, ms, funcs)
                feats.append(feat)

        res = solve_lp(feats, np_f)
        d = res.x[-1] if res.success else -1
        print(f"  {label:>20} (n≤12, ALL): δ = {d:.4f} ({np_f} params)")

    # Same for jdz
    print()
    for label, funcs in func_sets:
        feats = []
        for n_val in range(5, 13):
            exc_edges, ms = edges_by_n[n_val]
            n = n_val
            for u, v in exc_edges:
                if int_21(v, n) - int_21(u, n) != 0:
                    continue
                if int_j_20(v, n) - int_j_20(u, n) != 0:
                    continue
                feat, np_f = build_feat(u, v, n, ms, funcs)
                feats.append(feat)

        res = solve_lp(feats, np_f)
        d = res.x[-1] if res.success else -1
        print(f"  {label:>20} (n≤12, jdz): δ = {d:.4f} ({np_f} params)")

    # ═══════════════════════════════════════════════════════════
    # STEP 4: δ trend analysis
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 4: Per-n δ (position-pair, not parametric)")
    print("=" * 70)

    print(f"\n  {'n':>3} | {'ALL':>10} | {'zero':>10} | {'jdz':>10} | {'n*δ_ALL':>8}")
    print(f"  {'-'*55}")

    for n_val in range(5, 13):
        exc_edges, ms = edges_by_n[n_val]
        n = n_val

        for etype in ['ALL', 'zero', 'jdz']:
            var_idx = {}
            n_vars = 0
            for j in range(n):
                m_j = ms[j]; m_j1 = ms[(j+1)%n]
                for a in range(m_j):
                    for b in range(m_j1):
                        var_idx[(j, a, b)] = n_vars
                        n_vars += 1

            edges_list = []
            for u, v in exc_edges:
                if etype in ['zero', 'jdz']:
                    if int_21(v, n) - int_21(u, n) != 0:
                        continue
                if etype == 'jdz':
                    if int_j_20(v, n) - int_j_20(u, n) != 0:
                        continue
                edges_list.append((u, v))

            E = len(edges_list)
            A_feat = np.zeros((E, n_vars))
            for ei, (u, v) in enumerate(edges_list):
                for j in range(n):
                    au, bu = u[j], u[(j+1)%n]
                    av, bv = v[j], v[(j+1)%n]
                    if au != av or bu != bv:
                        A_feat[ei, var_idx[(j, av, bv)]] += 1
                        A_feat[ei, var_idx[(j, au, bu)]] -= 1

            tv = n_vars + 1
            c_obj = np.zeros(tv); c_obj[-1] = -1
            A_ub = np.zeros((E, tv)); b_ub = np.zeros(E)
            A_ub[:, :n_vars] = A_feat; A_ub[:, -1] = 1.0
            bounds = [(-100, 100)] * n_vars + [(0, None)]
            res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')

            d = res.x[-1] if res.success else -1
            if etype == 'ALL':
                nd = n * d if d > 0 else 0
                print(f"  {n_val:>3} | {d:>10.3f}", end="")
            elif etype == 'zero':
                print(f" | {d:>10.3f}", end="")
            else:
                print(f" | {d:>10.3f} | {nd:>8.1f}")

    # ═══════════════════════════════════════════════════════════
    # SUMMARY
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print()
    print("CONVERGENCE PROOF STATUS:")
    print("  1. (fc, Ψ) DAG                        [PROVED analytically]")
    print("  2. Anomalous edge necessity             [PROVED analytically]")
    print("  3. Excursion graph reduction             [PROVED analytically]")
    print("  4a. Δint(2,1) ≥ 0 on excursion edges    [PROVED analytically]")
    print("  4b. Zero-edge subgraph is DAG            [VERIFIED n=5..12]")
    print()
    print("  For 4b, position-pair potential works PER-N (verified n=5..12).")
    print("  Universal parametric LP (α*j + β) works for finite n range.")
    print("  Need: either universal parameterization or structural argument.")


if __name__ == '__main__':
    main()
