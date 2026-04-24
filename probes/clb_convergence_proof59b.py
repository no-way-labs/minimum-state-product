#!/usr/bin/env python3
"""
CONVERGENCE PROOF 59b: Universal Position-Pair Potential (focused)
===================================================================

Train on n=5..11, test on n=12. Don't include n=12 in training (too large).
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


def build_feat(u, v, n, ms, funcs):
    """Feature for parametric LP: w(j,a,b) = Σ_k α_k(a,b)*f_k(j,n) + β(a,b)."""
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


def solve_lp(feats, n_params):
    A = np.array(feats)
    E = A.shape[0]
    tv = n_params + 1
    c_obj = np.zeros(tv); c_obj[-1] = -1
    A_ub = np.zeros((E, tv)); b_ub = np.zeros(E)
    A_ub[:, :n_params] = A; A_ub[:, -1] = 1.0
    bounds = [(-1000, 1000)] * n_params + [(0, None)]
    return linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')


def main():
    # ═══════════════════════════════════════════════════════════
    # STEP 1: Train f(j)=j on ALL excursion edges, n=5..11
    # ═══════════════════════════════════════════════════════════
    print("=" * 70)
    print("STEP 1: f(j)=j on ALL excursion edges, n=5..11")
    print("=" * 70)

    funcs1 = [('j', lambda j, n: j)]
    all_feats = []
    edges_by_n = {}
    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        edges_by_n[n_val] = (exc_edges, ms)
        n = n_val
        for u, v in exc_edges:
            feat, np1 = build_feat(u, v, n, ms, funcs1)
            all_feats.append(feat)
        print(f"  n={n_val}: cum={len(all_feats):>7} ({time.time()-t0:.1f}s)")

    res1 = solve_lp(all_feats, np1)
    if res1.success:
        d1 = res1.x[-1]; p1 = res1.x[:np1]
        print(f"\n  δ = {d1:.4f} ({len(all_feats)} edges, {np1} params)")
        if d1 > 1e-6:
            print("  WORKS!")
            print("\n  Interior: w(j,a,b) = α(a,b)*j + β(a,b)")
            for a in range(3):
                for b in range(3):
                    i = a*3+b
                    print(f"    ({a},{b}): α={p1[i]:>8.3f}, β={p1[9+i]:>8.3f}")
    else:
        print("  INFEASIBLE")
        p1 = None; d1 = 0

    # ═══════════════════════════════════════════════════════════
    # STEP 2: Train f1=j, f2=j(n-j) on ALL excursion, n=5..11
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 2: f1=j, f2=j(n-j) on ALL excursion edges, n=5..11")
    print("=" * 70)

    funcs2 = [('j', lambda j, n: j), ('j(n-j)', lambda j, n: j*(n-j))]
    all_feats2 = []
    for n_val in range(5, 12):
        exc_edges, ms = edges_by_n[n_val]
        n = n_val
        for u, v in exc_edges:
            feat, np2 = build_feat(u, v, n, ms, funcs2)
            all_feats2.append(feat)

    res2 = solve_lp(all_feats2, np2)
    if res2.success:
        d2 = res2.x[-1]; p2 = res2.x[:np2]
        print(f"  δ = {d2:.4f} ({len(all_feats2)} edges, {np2} params)")
        if d2 > 1e-6:
            print("  WORKS!")
            print("\n  Interior: w(j,a,b) = α₁(a,b)*j + α₂(a,b)*j(n-j) + β(a,b)")
            for a in range(3):
                for b in range(3):
                    i = a*3+b
                    print(f"    ({a},{b}): α₁={p2[i]:>8.3f}, α₂={p2[9+i]:>8.3f}, β={p2[18+i]:>8.3f}")
    else:
        print("  INFEASIBLE")
        p2 = None; d2 = 0

    # ═══════════════════════════════════════════════════════════
    # STEP 3: Test generalization to n=12
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 3: Test on n=12 (out-of-sample)")
    print("=" * 70)

    t0 = time.time()
    exc_edges_12, ms_12 = build_excursion_graph(12)
    print(f"  Built n=12 excursion graph: {len(exc_edges_12)} edges ({time.time()-t0:.1f}s)")

    for label, p, funcs, delta in [("f(j)=j", p1, funcs1, d1),
                                    ("f1=j,f2=j(n-j)", p2, funcs2, d2)]:
        if p is None:
            continue
        n_fail = 0; n_test = 0; min_gain = float('inf')
        for u, v in exc_edges_12:
            feat, _ = build_feat(u, v, 12, ms_12, funcs)
            gain = -np.dot(p, feat)  # gain = Φ(u) - Φ(v)
            n_test += 1
            if gain < 1e-8:
                n_fail += 1
            min_gain = min(min_gain, gain)
        print(f"\n  {label}: {n_fail}/{n_test} failures, min gain = {min_gain:.4f}")

    # ═══════════════════════════════════════════════════════════
    # STEP 4: Retrain on n=5..11 ZERO edges only (simpler proof)
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 4: Train on ZERO edges only, n=5..11")
    print("=" * 70)

    def int_21(c, n):
        return sum(1 for j in range(2, n-2) if c[j] == 2 and c[(j+1)%n] == 1)

    for label, funcs in [("f(j)=j", funcs1), ("f1=j,f2=j(n-j)", funcs2)]:
        all_feats_z = []
        for n_val in range(5, 12):
            exc_edges, ms = edges_by_n[n_val]
            n = n_val
            for u, v in exc_edges:
                if int_21(v, n) - int_21(u, n) != 0:
                    continue
                feat, np_z = build_feat(u, v, n, ms, funcs)
                all_feats_z.append(feat)

        res_z = solve_lp(all_feats_z, np_z)
        if res_z.success:
            dz = res_z.x[-1]; pz = res_z.x[:np_z]
            print(f"  {label} on zero edges: δ = {dz:.4f} ({len(all_feats_z)} edges)")

            # Test on n=12 zero edges
            n_fail = 0; n_test = 0
            for u, v in exc_edges_12:
                if int_21(v, 12) - int_21(u, 12) != 0:
                    continue
                feat, _ = build_feat(u, v, 12, ms_12, funcs)
                gain = -np.dot(pz, feat)
                n_test += 1
                if gain < 1e-8:
                    n_fail += 1
            print(f"    → n=12 zero edges: {n_fail}/{n_test} failures")
        else:
            print(f"  {label} on zero edges: INFEASIBLE")

    # ═══════════════════════════════════════════════════════════
    # STEP 5: Extract clean weights for simplest working version
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 5: Clean weight extraction (f(j)=j, trained on ALL edges)")
    print("=" * 70)

    if p1 is not None and d1 > 1e-6:
        # Normalize: set α(0,0) = 0
        alpha = {}; beta = {}
        for a in range(3):
            for b in range(3):
                i = a*3+b
                alpha[(a,b)] = p1[i]
                beta[(a,b)] = p1[9+i]

        # Shift so min(α) = 0
        min_a = min(alpha.values())
        for k in alpha: alpha[k] -= min_a

        print(f"\n  α coefficients (weight of j):")
        print(f"  {'':>8}", end="")
        for b in range(3): print(f"  b={b:>5}", end="")
        print()
        for a in range(3):
            print(f"  a={a:>2}:", end="")
            for b in range(3):
                print(f"  {alpha[(a,b)]:>7.2f}", end="")
            print()

        print(f"\n  β coefficients (constant):")
        print(f"  {'':>8}", end="")
        for b in range(3): print(f"  b={b:>5}", end="")
        print()
        for a in range(3):
            print(f"  a={a:>2}:", end="")
            for b in range(3):
                print(f"  {beta[(a,b)]:>7.2f}", end="")
            print()

        # Check: are rational?
        print(f"\n  Checking rationality (α/d1):")
        for a in range(3):
            for b in range(3):
                ratio = alpha[(a,b)] / d1 if d1 > 0 else 0
                print(f"    α({a},{b})/δ = {ratio:.4f}")

    # ═══════════════════════════════════════════════════════════
    # STEP 6: Comparison transducer gain analysis
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 6: Comparison transducer gain structure")
    print("=" * 70)

    if p1 is not None and d1 > 1e-6:
        alpha = {}; beta = {}
        for a in range(3):
            for b in range(3):
                i = a*3+b
                alpha[(a,b)] = p1[i]
                beta[(a,b)] = p1[9+i]

        # For comparison pair ((u_j,v_j), (u_{j+1},v_{j+1})):
        # gain at position j = j * [α(u_j,u_{j+1}) - α(v_j,v_{j+1})]
        #                     + [β(u_j,u_{j+1}) - β(v_j,v_{j+1})]
        # α-part coefficient:
        print("\n  α-diff table: α(a,b) - α(c,d) for comparison bigram (a,b)→(c,d)")
        print("  If always positive along excursion edges → rightward drift → gain")

        # Key question: are the α values such that the transducer output
        # is always positive? Or do we need the β correction?

        # Classify α-diffs by comparison state
        # State (u_j, v_j) has 9 possibilities
        print("\n  α values per pair:")
        for a in range(3):
            for b in range(3):
                print(f"    α({a},{b}) = {alpha[(a,b)]:>8.3f}")

        # The gain from interior position j is:
        # g(j) = j * α_diff + β_diff
        # where α_diff = α(u_j,u_{j+1}) - α(v_j,v_{j+1})
        # and β_diff = β(u_j,u_{j+1}) - β(v_j,v_{j+1})

        # For this to sum to > 0, we need:
        # Σ_j [j * α_diff_j + β_diff_j] > 0
        # = Σ_j j * α_diff_j + Σ_j β_diff_j > 0

        # The first sum gives more weight to later positions.
        # The second sum is position-independent (just depends on pair counts).

        # Check: on actual excursion edges, what are the distributions?
        print("\n  Gain decomposition on excursion edges:")
        for n_val in [8, 9]:
            exc_edges, ms = edges_by_n[n_val]
            n = n_val

            a_sum_list = []; b_sum_list = []; total_list = []
            for u, v in exc_edges:
                a_sum = 0; b_sum = 0
                for j in range(2, n-2):
                    a_diff = alpha.get((u[j],u[(j+1)%n]), 0) - alpha.get((v[j],v[(j+1)%n]), 0)
                    b_diff = beta.get((u[j],u[(j+1)%n]), 0) - beta.get((v[j],v[(j+1)%n]), 0)
                    a_sum += j * a_diff
                    b_sum += b_diff
                a_sum_list.append(a_sum)
                b_sum_list.append(b_sum)
                total_list.append(a_sum + b_sum)

            print(f"\n  n={n_val}: {len(exc_edges)} edges")
            print(f"    α-sum (position-weighted): min={min(a_sum_list):.1f}, max={max(a_sum_list):.1f}")
            print(f"    β-sum (position-indep):    min={min(b_sum_list):.1f}, max={max(b_sum_list):.1f}")
            print(f"    Total gain (interior):     min={min(total_list):.1f}, max={max(total_list):.1f}")
            n_a_neg = sum(1 for x in a_sum_list if x < -1e-6)
            n_b_neg = sum(1 for x in b_sum_list if x < -1e-6)
            n_t_neg = sum(1 for x in total_list if x < -1e-6)
            print(f"    α<0: {n_a_neg}/{len(exc_edges)}, β<0: {n_b_neg}/{len(exc_edges)}, total<0: {n_t_neg}/{len(exc_edges)}")


if __name__ == '__main__':
    main()
