#!/usr/bin/env python3
"""
CONVERGENCE PROOF 57: Position-Value LP + Anomalous Step Classification
========================================================================

The j-double-zero subgraph is a DAG but no pair-count LP works (δ=0) and
no simple measure is monotone. Try:

1. Position-value LP: Φ(c) = Σ_j w(j,c[j]) on j-double-zero edges
   This captures position-dependent value preferences.
2. Position-pair-value LP: Φ(c) = Σ_j w(c[j],c[j+1]) * h(j)
   Position-weighted pair potential with VARIABLE h(j).
3. Classify anomalous step types in CUP-2 tables
4. Decompose each excursion edge into anomalous step + cascade
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
    return sum(1 for j in range(2, n-2) if c[j] == 2 and c[(j+1) % n] == 1)

def int_j_20(c, n):
    return sum(j for j in range(2, n-2) if c[j] == 2 and c[(j+1) % n] == 0)


def main():
    # ═══════════════════════════════════════════════════════════
    # STEP 1: Classify anomalous entries in CUP-2 tables
    # ═══════════════════════════════════════════════════════════
    print("=" * 70)
    print("STEP 1: Anomalous entries in CUP-2 tables")
    print("=" * 70)
    print()
    print("Anomalous = output ≠ L AND output ≠ R")

    n_val = 9
    ms, fs = build_system(n_val)

    table_names = {0: 'T_bot', 1: 'T_low', 2: 'T_mid(fix)',
                   **{j: 'T_mid' for j in range(3, n_val-2)},
                   n_val-2: 'T_high', n_val-1: 'T_top'}

    anom_entries_by_table = defaultdict(list)
    for pos in range(n_val):
        m_L = ms[(pos-1) % n_val]
        m_S = ms[pos]
        m_R = ms[(pos+1) % n_val]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    out = fs[pos](L, S, R)
                    if out != S and out != L and out != R:
                        anom_entries_by_table[table_names[pos]].append((pos, L, S, R, out))

    for tname in ['T_bot', 'T_low', 'T_mid(fix)', 'T_mid', 'T_high', 'T_top']:
        entries = anom_entries_by_table[tname]
        print(f"\n  {tname}: {len(entries)} anomalous entries")
        for pos, L, S, R, out in entries[:10]:
            # Effect on (2,1) and (2,0) pairs
            print(f"    pos={pos}: ({L},{S},{R})→{out}  "
                  f"Δ(L,p):{L},{S}→{L},{out}  Δ(p,R):{S},{R}→{out},{R}")

    # ═══════════════════════════════════════════════════════════
    # STEP 2: Position-value LP on j-double-zero edges
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 2: Position-value LP on j-double-zero edges")
    print("=" * 70)
    print()
    print("Φ(c) = Σ_j w(j, c[j]) where w depends on position AND value")
    print("For each n: n_pos * n_val variables")

    for n_val in [8, 9, 10]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        jdz_edges = []
        for u, v in exc_edges:
            if int_21(v, n) - int_21(u, n) != 0:
                continue
            if int_j_20(v, n) - int_j_20(u, n) != 0:
                continue
            jdz_edges.append((u, v))

        # Variables: w(j, v) for j=0..n-1, v=0..m_j-1
        # For position j, values 0..m_j-1
        var_idx = {}
        n_vars = 0
        for j in range(n):
            for v in range(ms[j]):
                var_idx[(j, v)] = n_vars
                n_vars += 1

        # Feature vector for edge (u, v): Δw = Σ_j [w(j, v[j]) - w(j, u[j])]
        # For each edge, only positions where u[j] ≠ v[j] contribute
        E = len(jdz_edges)
        A_feat = np.zeros((E, n_vars))
        for ei, (u, v) in enumerate(jdz_edges):
            for j in range(n):
                if u[j] != v[j]:
                    A_feat[ei, var_idx[(j, v[j])]] += 1
                    A_feat[ei, var_idx[(j, u[j])]] -= 1

        # LP: max δ s.t. A_feat @ w + δ ≤ 0
        # Variables: [w..., δ]
        total_vars = n_vars + 1
        c_obj = np.zeros(total_vars)
        c_obj[-1] = -1  # maximize δ

        A_ub = np.zeros((E, total_vars))
        b_ub = np.zeros(E)
        A_ub[:, :n_vars] = A_feat
        A_ub[:, -1] = 1.0

        bounds = [(-100, 100)] * n_vars + [(0, None)]

        res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')
        dt = time.time() - t0

        if res.success:
            delta = res.x[-1]
            w = res.x[:n_vars]
            print(f"\n  n={n_val}: {E} jdz edges, {n_vars} vars → δ = {delta:.6f} ({dt:.1f}s)")
            if delta > 1e-8:
                print(f"    STRICT DECREASE on all j-double-zero edges!")
                print(f"    Position-value weights:")
                for j in range(n):
                    vals = []
                    for v in range(ms[j]):
                        vals.append(f"w({j},{v})={w[var_idx[(j,v)]]:.3f}")
                    print(f"      pos {j}: {', '.join(vals)}")
        else:
            print(f"\n  n={n_val}: LP INFEASIBLE ({dt:.1f}s)")

    # ═══════════════════════════════════════════════════════════
    # STEP 3: Parametric position-value LP (shared across n)
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 3: Parametric position-value LP")
    print("=" * 70)
    print()
    print("w(j,v) = α(v)*j + β(v) for interior positions (6 params)")
    print("+ boundary weights (free)")

    # Collect constraints across n=5..11
    # Interior positions: w(j,v) = α(v)*j + β(v) for v ∈ {0,1,2}
    # Boundary: w(0,v), w(1,v), w(n-2,v), w(n-1,v) are free per-n
    # But for n-independence: boundary weights = γ(pos_type, v)
    # pos_type: {bot, low, mid, high, top}
    # Since bot/top are binary (v ∈ {0,1}), low/high are ternary

    # Parameters:
    # α(0), α(1), α(2): 3 (slope)
    # β(0), β(1), β(2): 3 (intercept)
    # γ_bot(0), γ_bot(1): 2
    # γ_low(0), γ_low(1), γ_low(2): 3
    # γ_high(0), γ_high(1), γ_high(2): 3
    # γ_top(0), γ_top(1): 2
    # Total: 16 parameters

    param_names = ['α0', 'α1', 'α2', 'β0', 'β1', 'β2',
                   'γbot0', 'γbot1', 'γlow0', 'γlow1', 'γlow2',
                   'γhigh0', 'γhigh1', 'γhigh2', 'γtop0', 'γtop1']
    n_params = len(param_names)

    all_constraints = []
    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        for u, v in exc_edges:
            if int_21(v, n) - int_21(u, n) != 0:
                continue
            if int_j_20(v, n) - int_j_20(u, n) != 0:
                continue

            # Build constraint: Σ_j [w(j,v[j]) - w(j,u[j])] + δ ≤ 0
            feat = np.zeros(n_params)
            for j in range(n):
                if u[j] == v[j]:
                    continue

                if j == 0:  # bot (binary)
                    feat[6 + v[j]] += 1  # γbot(v[j])
                    feat[6 + u[j]] -= 1  # γbot(u[j])
                elif j == 1:  # low (ternary)
                    feat[8 + v[j]] += 1
                    feat[8 + u[j]] -= 1
                elif j == n-2:  # high (ternary)
                    feat[11 + v[j]] += 1
                    feat[11 + u[j]] -= 1
                elif j == n-1:  # top (binary)
                    feat[14 + v[j]] += 1
                    feat[14 + u[j]] -= 1
                else:  # interior: w(j,v) = α(v)*j + β(v)
                    # w(j,v[j]) - w(j,u[j]) = α(v[j])*j + β(v[j]) - α(u[j])*j - β(u[j])
                    feat[v[j]] += j     # α(v[j]) * j
                    feat[u[j]] -= j     # -α(u[j]) * j
                    feat[3 + v[j]] += 1  # β(v[j])
                    feat[3 + u[j]] -= 1  # -β(u[j])

            all_constraints.append(feat)

        print(f"  n={n_val}: cumulative {len(all_constraints)} jdz edges ({time.time()-t0:.1f}s)")

    A = np.array(all_constraints)
    E = A.shape[0]
    print(f"\n  Total: {E} constraints, {n_params} parameters")

    # LP: max δ s.t. A @ p + δ ≤ 0
    total_vars = n_params + 1
    c_obj = np.zeros(total_vars)
    c_obj[-1] = -1

    A_ub = np.zeros((E, total_vars))
    b_ub = np.zeros(E)
    A_ub[:, :n_params] = A
    A_ub[:, -1] = 1.0

    bounds = [(-100, 100)] * n_params + [(0, None)]
    res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')

    if res.success:
        delta = res.x[-1]
        p = res.x[:n_params]
        print(f"\n  Parametric LP: δ = {delta:.6f}")
        if delta > 1e-8:
            print(f"  STRICT DECREASE! Parameters:")
            for i, name in enumerate(param_names):
                if abs(p[i]) > 1e-10:
                    print(f"    {name} = {p[i]:.6f}")
    else:
        print(f"\n  Parametric LP: INFEASIBLE")

    # ═══════════════════════════════════════════════════════════
    # STEP 4: More general parametric: w(j,v) = α(v)*j² + β(v)*j + γ(v)
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 4: Quadratic position weight")
    print("=" * 70)
    print("w(j,v) = α(v)*j² + β(v)*j + γ(v) for interior (9 params + boundary)")

    param_names2 = ['α0', 'α1', 'α2', 'β0', 'β1', 'β2', 'γ0', 'γ1', 'γ2',
                    'b_bot0', 'b_bot1', 'b_low0', 'b_low1', 'b_low2',
                    'b_high0', 'b_high1', 'b_high2', 'b_top0', 'b_top1']
    n_params2 = len(param_names2)

    all_constraints2 = []
    for n_val in range(5, 12):
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        for u, v in exc_edges:
            if int_21(v, n) - int_21(u, n) != 0:
                continue
            if int_j_20(v, n) - int_j_20(u, n) != 0:
                continue

            feat = np.zeros(n_params2)
            for j in range(n):
                if u[j] == v[j]:
                    continue

                if j == 0:
                    feat[9 + v[j]] += 1; feat[9 + u[j]] -= 1
                elif j == 1:
                    feat[11 + v[j]] += 1; feat[11 + u[j]] -= 1
                elif j == n-2:
                    feat[14 + v[j]] += 1; feat[14 + u[j]] -= 1
                elif j == n-1:
                    feat[17 + v[j]] += 1; feat[17 + u[j]] -= 1
                else:
                    feat[v[j]] += j*j; feat[u[j]] -= j*j
                    feat[3+v[j]] += j; feat[3+u[j]] -= j
                    feat[6+v[j]] += 1; feat[6+u[j]] -= 1

            all_constraints2.append(feat)

    A2 = np.array(all_constraints2)
    E2 = A2.shape[0]

    total_vars2 = n_params2 + 1
    c_obj2 = np.zeros(total_vars2)
    c_obj2[-1] = -1

    A_ub2 = np.zeros((E2, total_vars2))
    b_ub2 = np.zeros(E2)
    A_ub2[:, :n_params2] = A2
    A_ub2[:, -1] = 1.0

    bounds2 = [(-100, 100)] * n_params2 + [(0, None)]
    res2 = linprog(c_obj2, A_ub=A_ub2, b_ub=b_ub2, bounds=bounds2, method='highs')

    if res2.success:
        delta2 = res2.x[-1]
        p2 = res2.x[:n_params2]
        print(f"\n  Quadratic LP: δ = {delta2:.6f}")
        if delta2 > 1e-8:
            print(f"  STRICT DECREASE! Parameters:")
            for i, name in enumerate(param_names2):
                if abs(p2[i]) > 1e-10:
                    print(f"    {name} = {p2[i]:.6f}")
    else:
        print(f"\n  Quadratic LP: INFEASIBLE")

    # ═══════════════════════════════════════════════════════════
    # STEP 5: Position-value LP per-n (can it work per-n?)
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 5: Per-n position-value LP")
    print("=" * 70)

    for n_val in [8, 9, 10]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        # Also collect ALL zero edges (not just jdz)
        zero_edges = []
        jdz_edges = []
        for u, v in exc_edges:
            if int_21(v, n) - int_21(u, n) != 0:
                continue
            zero_edges.append((u, v))
            if int_j_20(v, n) - int_j_20(u, n) != 0:
                continue
            jdz_edges.append((u, v))

        # Variables: w(j, v) for j=0..n-1, v=0..m_j-1
        var_idx = {}
        n_vars = 0
        for j in range(n):
            for v in range(ms[j]):
                var_idx[(j, v)] = n_vars
                n_vars += 1

        for edge_type, edges in [('zero', zero_edges), ('jdz', jdz_edges)]:
            E = len(edges)
            A_feat = np.zeros((E, n_vars))
            for ei, (u, v) in enumerate(edges):
                for j in range(n):
                    if u[j] != v[j]:
                        A_feat[ei, var_idx[(j, v[j])]] += 1
                        A_feat[ei, var_idx[(j, u[j])]] -= 1

            total_vars = n_vars + 1
            c_obj = np.zeros(total_vars)
            c_obj[-1] = -1

            A_ub = np.zeros((E, total_vars))
            b_ub = np.zeros(E)
            A_ub[:, :n_vars] = A_feat
            A_ub[:, -1] = 1.0

            bounds = [(-100, 100)] * n_vars + [(0, None)]
            res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')

            dt = time.time() - t0
            if res.success:
                print(f"  n={n_val} {edge_type}: δ = {res.x[-1]:.6f} "
                      f"({E} edges, {n_vars} vars, {dt:.1f}s)")
            else:
                print(f"  n={n_val} {edge_type}: INFEASIBLE ({dt:.1f}s)")

    # ═══════════════════════════════════════════════════════════
    # STEP 6: Position-value-PAIR LP per-n on jdz edges
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 6: Position-value-pair LP per-n on jdz edges")
    print("=" * 70)
    print("Φ(c) = Σ_j w(j, c[j], c[j+1]) where w depends on position+pair")

    for n_val in [8, 9]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        jdz_edges = []
        for u, v in exc_edges:
            if int_21(v, n) - int_21(u, n) != 0:
                continue
            if int_j_20(v, n) - int_j_20(u, n) != 0:
                continue
            jdz_edges.append((u, v))

        # Variables: w(j, a, b) for each position j and pair (a,b)
        var_idx = {}
        n_vars = 0
        for j in range(n):
            m_j = ms[j]
            m_j1 = ms[(j+1) % n]
            for a in range(m_j):
                for b in range(m_j1):
                    var_idx[(j, a, b)] = n_vars
                    n_vars += 1

        E = len(jdz_edges)
        A_feat = np.zeros((E, n_vars))
        for ei, (u, v) in enumerate(jdz_edges):
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

        dt = time.time() - t0
        if res.success:
            delta = res.x[-1]
            print(f"\n  n={n_val}: δ = {delta:.6f} ({E} edges, {n_vars} vars, {dt:.1f}s)")
            if delta > 1e-8:
                print(f"  STRICT DECREASE on all jdz edges!")
        else:
            print(f"\n  n={n_val}: INFEASIBLE ({dt:.1f}s)")

    # ═══════════════════════════════════════════════════════════
    # STEP 7: Summary
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print()
    print("Potential types tested on j-double-zero edges:")
    print("  - Position-value Φ(c) = Σ w(j,c[j]): per-n and parametric")
    print("  - Quadratic position weight: α(v)j² + β(v)j + γ(v)")
    print("  - Position-value-pair Φ(c) = Σ w(j,c[j],c[j+1]): per-n")
    print()
    print("Results above determine which (if any) can prove jdz-DAG.")


if __name__ == '__main__':
    main()
