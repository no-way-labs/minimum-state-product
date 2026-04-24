#!/usr/bin/env python3
"""Wave 3 combined probe — P0/P1/P2/P3/P5/P6/P7.

Run order:
  P0  Fix CLB generalization (build_clb_witness_v2 with full edge_costs sweep).
  P1  Stratified corpus expansion: sub classes 1/2 expanded; classes 3,4,5 are
      structurally empty at strict sub-threshold for small n (documented).
      At-threshold: CLB ternary-strip at n=5..10 (6 records) + existing n=9.
  P2  Per-record balance-identity test: for each feasible sub record, compute
      per-vertex T(v) and c_right balance; report `||T+c_right||/||T||`,
      plus residual attributable to c_self+c_left.
  P3  c_right asymmetry: reverse cycle, re-run C1, compare support type ratios.
  P5  Scalar-feature logistic regression. Features: (n, L, prod_m, n_binary,
      n_ternary, n_geq4).
  P6  Coverage correlation with bootstrap CI.
  P7  Perturbation variants: v2a drain-to-good, v2b include VC-inconsistent,
      v2c Hamming>=2 targets. Re-run C1 on 5 sub records + expanded at.

Outputs phaseW3_results.json alongside this file.
"""
from __future__ import annotations

import json
import os
import sys
import time
from collections import Counter, defaultdict
from itertools import product as iproduct

import numpy as np
from scipy.optimize import linprog

HERE = os.path.dirname(os.path.abspath(__file__))
CLAUDE_DIR = os.path.abspath(os.path.join(HERE, "..", "..", "..", "..", "claude"))
sys.path.insert(0, CLAUDE_DIR)
from verifier import verify_system  # type: ignore

# ======================================================================
# P0 — CLB generalization v2 (restore full edge_costs sweep)
# ======================================================================

def build_clb_witness_v2(n: int):
    """Generalize clb_witness_8748.build_system to n>=5 with the full
    O(non_good × free_entry) edge_costs sweep preserved. Returns
    (ms, fs, comp, cycle, movers)."""
    ms = (2,) + (3,) * (n - 2) + (2,)
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * 5
    movers = []
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        movers.append(mover)
        if nc == cycle[0]:
            break
        if nc in visited:
            raise RuntimeError(f"Bounce cycle didn't close at n={n}")
        visited.add(nc)
        cycle.append(nc)
    L = len(cycle)
    movers = movers[:L]

    good_set = set(cycle)
    all_configs = list(iproduct(*(range(m) for m in ms)))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    det = {}
    for idx in range(L):
        c = cycle[idx]; c_next = cycle[(idx + 1) % L]; mv = movers[idx]
        for p in range(n):
            Lv = c[(p-1)%n]; Sv = c[p]; Rv = c[(p+1)%n]
            key = (p, Lv, Sv, Rv)
            if p == mv:
                det[key] = c_next[p]
            else:
                det[key] = Sv

    free_entries = []
    for p in range(n):
        mL = ms[(p-1)%n]; mS = ms[p]; mR = ms[(p+1)%n]
        for Lv in range(mL):
            for Sv in range(mS):
                for Rv in range(mR):
                    key = (p, Lv, Sv, Rv)
                    if key not in det:
                        free_entries.append(key)

    # Edge costs (full sweep — the load-bearing piece missed in v1)
    edge_costs = {}
    for key in free_entries:
        p, Lv, Sv, Rv = key
        for out in range(ms[p]):
            if out == Sv:
                edge_costs[(key, out)] = 0
            else:
                edges = sum(
                    1 for c in non_good
                    if c[(p-1)%n] == Lv and c[p] == Sv and c[(p+1)%n] == Rv
                    and tuple(c[j] if j != p else out for j in range(n)) in non_good_set
                )
                edge_costs[(key, out)] = edges

    # good-targeting completion
    comp = dict(det)
    for key in free_entries:
        p, Lv, Sv, Rv = key
        best_out = Sv; best_good = 0; best_ng = float('inf')
        for out in range(ms[p]):
            ng = edge_costs.get((key, out), 0)
            good_count = 0
            if out != Sv:
                good_count = sum(
                    1 for c in non_good
                    if c[(p-1)%n] == Lv and c[p] == Sv and c[(p+1)%n] == Rv
                    and tuple(c[j] if j != p else out for j in range(n)) in good_set
                )
            if good_count > best_good or (good_count == best_good and ng < best_ng):
                best_out = out; best_good = good_count; best_ng = ng
        comp[key] = best_out

    # liveness fix (using edge_costs as tie-breaker — this is the bug fix)
    for c in all_configs:
        has_priv = any(
            comp.get((p, c[(p-1)%n], c[p], c[(p+1)%n]), c[p]) != c[p]
            for p in range(n)
        )
        if not has_priv:
            best_key = None; best_cost = float('inf'); best_out_val = None
            for p in range(n):
                L2 = c[(p-1)%n]; S2 = c[p]; R2 = c[(p+1)%n]
                key = (p, L2, S2, R2)
                if key not in det:
                    for out in range(ms[p]):
                        if out != S2:
                            cost = edge_costs.get((key, out), 0)
                            if cost < best_cost:
                                best_cost = cost
                                best_key = key
                                best_out_val = out
            if best_key:
                comp[best_key] = best_out_val

    def make_f(p_idx):
        def f(L, S, R):
            return comp.get((p_idx, L, S, R), S)
        return f
    fs = [make_f(p) for p in range(n)]
    return list(ms), fs, comp, cycle, movers


# ======================================================================
# Sub-threshold cycle enumerator (from wave2)
# ======================================================================

def m_n(n):
    return 32 * 3 ** (n - 4) if 5 <= n <= 8 else 4 * 3 ** (n - 2)


def enumerate_multisets(n, max_product):
    out = []
    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product:
                out.append(tuple(prefix))
            return
        for m in range(2, max_product + 1):
            new_prod = prod * m
            min_remaining = 2 ** (n - i - 1)
            if new_prod * min_remaining >= max_product:
                break
            prefix.append(m)
            rec(i + 1, prefix, new_prod)
            prefix.pop()
    rec(0, [], 1)
    return out


def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen_cycles = set()
    t0 = time.time()
    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max: return
        for p in range(n):
            Lp = config[(p-1)%n]; Sp = config[p]; Rp = config[(p+1)%n]
            km = (p, Lp, Sp, Rp)
            forced_out = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced_out is not None and forced_out != new_val: continue
                new_det = dict(det); new_det[km] = new_val
                ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si:
                        ok = False; break
                    new_det[ki] = Si
                if not ok: continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path): continue
                dfs(start, nc, new_det, path + [nc], movers + [p])
    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget: break
        dfs(start, start, {}, [start], [])
    return found


def classify_composition(ms):
    n = len(ms)
    n_bin = sum(1 for m in ms if m == 2)
    if n_bin == n: return 1
    if n >= 3 and ms[0] == 2 and ms[-1] == 2 and all(m == 3 for m in ms[1:-1]):
        return 3
    if n_bin == 3 and any(m == 4 for m in ms) and sum(1 for m in ms if m == 3) == n - 4:
        return 4
    if n_bin >= 3: return 2
    return 5


def value_set_tube(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for q in range(n): V[q].add(c[q])
    return [sorted(s) for s in V]


# ======================================================================
# Lifted graph (v2 baseline; v2a/v2b/v2c variants handled in build_lifted_graph2)
# ======================================================================

def build_lifted_graph(rec, variant='v2'):
    """variants:
      v2  baseline: V_tube = values attained in cycle, only non-cycle tube configs
      v2a as v2 but also emit edges to lifts in G(C) (reclassified as exit)
      v2b as v2 but V_tube = full Fin(m_q) (value-inconsistent included)
      v2c as v2 but emit edges to configs Hamming>=2 from all cycle steps
           (no lift target; we approximate by creating virtual sink vertices)
    """
    ms = rec['ms']; n = len(ms)
    cycle = [tuple(c) for c in rec['cycle']]
    movers = rec['movers']
    L = len(cycle)
    det = rec['det']
    cycle_set = set(cycle)
    V_tube = value_set_tube(cycle, n)
    if variant == 'v2b':
        V_tube = [list(range(ms[q])) for q in range(n)]
    move_entries = {k: v for k, v in det.items() if v != k[2]}

    V_lift = []; idx_of = {}; tube_configs = {}
    for k in range(L):
        c_k = cycle[k]
        for q in range(n):
            for a in V_tube[q]:
                if a == c_k[q]: continue
                nc = list(c_k); nc[q] = a; nc = tuple(nc)
                if nc in cycle_set: continue
                key = (k, q, a)
                idx_of[key] = len(V_lift)
                V_lift.append(key)
                tube_configs[key] = nc

    # virtual drain vertex for v2a / v2c
    drain_idx = None
    if variant in ('v2a', 'v2c'):
        drain_idx = len(V_lift)

    E_lift = []
    for src_v in V_lift:
        k, q, a = src_v
        c = tube_configs[src_v]
        mov_k = movers[k] if k < len(movers) else None
        adj_q = {(q-1)%n, q, (q+1)%n}
        for p_fire in range(n):
            ctx = (p_fire, c[(p_fire-1)%n], c[p_fire], c[(p_fire+1)%n])
            v_new = move_entries.get(ctx)
            if v_new is None or v_new == c[p_fire]: continue
            c_succ = list(c); c_succ[p_fire] = v_new; c_succ = tuple(c_succ)
            if p_fire == mov_k and p_fire not in adj_q:
                edge_type = 'transport'
            elif p_fire == q:
                edge_type = 'c_self'
            elif p_fire == (q-1)%n:
                edge_type = 'c_left'
            elif p_fire == (q+1)%n:
                edge_type = 'c_right'
            else:
                edge_type = 'other'
            tgt_v = None
            if edge_type == 'transport':
                cand = ((k+1)%L, q, a)
                if cand in idx_of: tgt_v = cand
            if tgt_v is None:
                if c_succ in cycle_set:
                    if variant == 'v2a':
                        # emit to drain
                        E_lift.append((idx_of[src_v], drain_idx, 'drain_good'))
                    continue
                # search for Hamming-1 lift
                found = False
                for kk in range(L):
                    c_kk = cycle[kk]
                    diff = [(i, c_succ[i]) for i in range(n) if c_succ[i] != c_kk[i]]
                    if len(diff) == 1:
                        qq, aa = diff[0]
                        cand = (kk, qq, aa)
                        if cand in idx_of:
                            tgt_v = cand; found = True; break
                if not found:
                    if variant == 'v2c':
                        E_lift.append((idx_of[src_v], drain_idx, 'hamming_ge2'))
                    continue
            E_lift.append((idx_of[src_v], idx_of[tgt_v], edge_type))
    # in v2a/v2c, add drain vertex with zero-boundary to keep LP well-posed
    total_V = len(V_lift) + (1 if drain_idx is not None else 0)
    return V_lift, E_lift, tube_configs, total_V


def solve_circulation_lp(n_vertices, E_lift):
    nE = len(E_lift)
    if nE == 0:
        return {'feasible': False, 'supp_size': 0, 'support': [], 'phi': []}
    Aeq = np.zeros((n_vertices, nE))
    for e_idx, (s, t, _) in enumerate(E_lift):
        Aeq[s, e_idx] -= 1; Aeq[t, e_idx] += 1
    beq = np.zeros(n_vertices)
    c = -np.ones(nE)
    bounds = [(0.0, 1.0)] * nE
    res = linprog(c, A_eq=Aeq, b_eq=beq, bounds=bounds, method='highs')
    if not res.success:
        return {'feasible': False, 'supp_size': 0, 'support': [], 'phi': []}
    x = res.x
    obj = float(res.fun)
    supp = [i for i in range(nE) if x[i] > 1e-6]
    return {
        'feasible': obj < -1e-9,
        'supp_size': len(supp), 'support': supp,
        'phi': x.tolist(), 'objective': obj,
    }


def cyclic_time_shift_stabilizer(V_lift, E_lift, support, L):
    if not support: return L
    supp_set = set()
    for e_idx in support:
        s, t, _ = E_lift[e_idx]
        vs = V_lift[s] if s < len(V_lift) else ('drain',)
        vt = V_lift[t] if t < len(V_lift) else ('drain',)
        supp_set.add(('src', vs)); supp_set.add(('dst', vt))
    stab = 0
    for s in range(L):
        shifted = set()
        for (tag, v) in supp_set:
            if len(v) == 3:
                k, q, a = v
                shifted.add((tag, ((k+s) % L, q, a)))
            else:
                shifted.add((tag, v))
        if shifted == supp_set:
            stab += 1
    return stab


# ======================================================================
# Analyze a record under a variant
# ======================================================================

def analyze_record(rec, variant='v2'):
    V_lift, E_lift, _, n_vert = build_lifted_graph(rec, variant)
    etype_count = Counter(etype for _, _, etype in E_lift)
    lp = solve_circulation_lp(n_vert, E_lift)
    support = lp.get('support', [])
    supp_etypes = Counter(E_lift[i][2] for i in support) if support else Counter()
    stab = cyclic_time_shift_stabilizer(V_lift, E_lift, support, rec['L'])
    ms = rec['ms']; n = len(ms); L = rec['L']; product = int(np.prod(ms))
    return {
        'class': rec['class'], 'n': n, 'ms': list(ms), 'L': L,
        'product': product,
        'composition_class': classify_composition(ms),
        'coverage': L / (n * product),
        'nV_lift': len(V_lift), 'nE_lift': len(E_lift),
        'edge_type_hist': dict(etype_count),
        'feasible': lp.get('feasible', False),
        'supp_size': lp.get('supp_size', 0),
        'supp_edge_type_hist': dict(supp_etypes),
        'phi': lp.get('phi', []),
        'stab_time_shift': stab,
        'stab_ratio': stab / max(L, 1),
        'variant': variant,
        # include lifted graph for balance-identity reuse
        '_V_lift': V_lift, '_E_lift': E_lift, '_n_vert': n_vert,
    }


# ======================================================================
# P2 balance-identity test
# ======================================================================

def balance_identity_test(records):
    """For each feasible record, compute per-vertex imbalance by edge type.
    Returns dict of aggregate statistics across records."""
    out = []
    for r in records:
        if not r.get('feasible') or '_V_lift' not in r: continue
        V_lift = r['_V_lift']; E_lift = r['_E_lift']; phi = r['phi']
        nV = len(V_lift) + (0 if r['_n_vert'] == len(V_lift) else 1)
        # per-vertex per-type imbalance
        by_type = {'transport': np.zeros(r['_n_vert']),
                   'c_self': np.zeros(r['_n_vert']),
                   'c_left': np.zeros(r['_n_vert']),
                   'c_right': np.zeros(r['_n_vert']),
                   'other': np.zeros(r['_n_vert']),
                   'drain_good': np.zeros(r['_n_vert']),
                   'hamming_ge2': np.zeros(r['_n_vert'])}
        for e_idx, (s, t, etype) in enumerate(E_lift):
            w = phi[e_idx]
            if etype in by_type:
                by_type[etype][s] -= w
                by_type[etype][t] += w
        T = by_type['transport']
        W_right = by_type['c_right']
        W_self = by_type['c_self']
        W_left = by_type['c_left']
        W_total = T + W_right + W_self + W_left + by_type['other']
        # Report residuals
        max_total = float(np.max(np.abs(W_total)))
        # Leading-order: T + c_right should ≈ 0
        leading = T + W_right
        max_leading = float(np.max(np.abs(leading)))
        norm_T = float(np.sum(np.abs(T)))
        sub = float(np.sum(np.abs(W_self) + np.abs(W_left)))
        out.append({
            'class': r['class'], 'n': r['n'], 'ms': r['ms'], 'L': r['L'],
            'max_per_vertex_total': max_total,   # should be ~0 (LP constraint)
            'max_per_vertex_leading_residual': max_leading,  # T+c_right
            'sum_abs_T': norm_T,
            'sum_abs_sub': sub,                  # |c_self|+|c_left| mass
            'leading_over_T_ratio': (max_leading / norm_T) if norm_T > 0 else 0.0,
            'sub_over_T_ratio': (sub / norm_T) if norm_T > 0 else 0.0,
        })
    return out


# ======================================================================
# P3 c_right asymmetry — reverse-cycle test
# ======================================================================

def reverse_cycle_record(rec):
    """Reverse the good cycle direction. New cycle[k] = old cycle[L-1-k].
    detOf must be recomputed from the reversed sequence."""
    old_cycle = [tuple(c) for c in rec['cycle']]
    old_movers = rec['movers']
    L = len(old_cycle)
    # reversed cycle: start from old_cycle[0], go backwards
    new_cycle = [old_cycle[(L - k) % L] for k in range(L)]
    new_movers = [old_movers[(L - 1 - k) % L] for k in range(L)]
    # recompute det on reversed
    n = len(rec['ms'])
    ms = rec['ms']
    det = {}
    for idx in range(L):
        c = new_cycle[idx]; c_next = new_cycle[(idx + 1) % L]; mv = new_movers[idx]
        for p in range(n):
            Lv = c[(p-1)%n]; Sv = c[p]; Rv = c[(p+1)%n]
            key = (p, Lv, Sv, Rv)
            if p == mv:
                det[key] = c_next[p]
            else:
                if key in det and det[key] != Sv:
                    # conflict: reversed cycle has inconsistent dynamics
                    # return None to flag
                    return None
                det[key] = Sv
    return {
        'class': rec['class'], 'n': n, 'ms': ms,
        'cycle': [list(c) for c in new_cycle],
        'movers': new_movers, 'det': det, 'L': L,
        'reversed_of_orig': True,
    }


# ======================================================================
# P5 scalar-feature regression
# ======================================================================

def scenario_b_regression(records):
    """Logistic regression on (n, L, log(prod), n_binary, n_ternary, n_geq4)
    predicting feasibility."""
    rs = [r for r in records if 'feasible' in r]
    if len(rs) < 6: return {'skipped': f'only {len(rs)} records'}
    X = []
    y = []
    for r in rs:
        ms = r['ms']
        X.append([r['n'], r['L'], np.log(r['product']),
                  sum(1 for m in ms if m == 2),
                  sum(1 for m in ms if m == 3),
                  sum(1 for m in ms if m >= 4)])
        y.append(1.0 if r['feasible'] else 0.0)
    X = np.array(X); y = np.array(y)
    # simple logistic via normal-equations approximation (no sklearn dep)
    # add bias
    X1 = np.hstack([np.ones((len(X), 1)), X])
    # linear regression as a crude proxy
    try:
        beta, *_ = np.linalg.lstsq(X1, y, rcond=None)
        yhat = X1 @ beta
        # pseudo-R² via 1 - SSE/SST
        sse = float(np.sum((y - yhat) ** 2))
        sst = float(np.sum((y - y.mean()) ** 2))
        r_sq = 1 - sse / sst if sst > 0 else 0.0
    except Exception:
        r_sq = None; beta = None
    # also: accuracy of thresholding yhat at 0.5
    if beta is not None:
        pred = (yhat >= 0.5).astype(int)
        acc = float(np.mean(pred == y))
    else:
        acc = None
    return {
        'n_records': len(rs), 'r_squared_linear': r_sq,
        'threshold_accuracy': acc,
        'beta': beta.tolist() if beta is not None else None,
        'features': ['bias', 'n', 'L', 'log(prod)', 'n_bin', 'n_ter', 'n_geq4'],
    }


# ======================================================================
# P6 coverage-correlation bootstrap CI
# ======================================================================

def coverage_ci(records, n_boot=1000):
    rs = [r for r in records if 'feasible' in r and 'coverage' in r]
    cov = np.array([r['coverage'] for r in rs])
    feas = np.array([1.0 if r['feasible'] else 0.0 for r in rs])
    if np.std(feas) == 0 or np.std(cov) == 0:
        return {'cor': 0.0, 'ci_lo': 0.0, 'ci_hi': 0.0, 'n': len(rs)}
    base_cor = float(np.corrcoef(cov, feas)[0, 1])
    rng = np.random.default_rng(42)
    boot_cors = []
    for _ in range(n_boot):
        idx = rng.integers(0, len(rs), len(rs))
        cov_b = cov[idx]; feas_b = feas[idx]
        if np.std(feas_b) == 0 or np.std(cov_b) == 0: continue
        boot_cors.append(float(np.corrcoef(cov_b, feas_b)[0, 1]))
    if not boot_cors:
        return {'cor': base_cor, 'ci_lo': base_cor, 'ci_hi': base_cor,
                'n': len(rs)}
    lo = float(np.percentile(boot_cors, 2.5))
    hi = float(np.percentile(boot_cors, 97.5))
    return {'cor': base_cor, 'ci_lo': lo, 'ci_hi': hi, 'n': len(rs),
            'n_boot': len(boot_cors)}


# ======================================================================
# Corpus construction
# ======================================================================

def build_at_corpus():
    print("=== P0/P1 at-threshold corpus: CLB ternary-strip v2 ===")
    out = []
    for n in range(5, 11):
        print(f"  building CLB witness at n={n}...", end=" ", flush=True)
        t0 = time.time()
        try:
            ms, fs, comp, cycle, movers = build_clb_witness_v2(n)
        except Exception as e:
            print(f"ERROR {e}"); continue
        v = verify_system(ms, fs, verbose=False)
        dt = time.time() - t0
        valid = v['valid']
        print(f"valid={valid} prod={int(np.prod(ms))} L={len(cycle)} ({dt:.1f}s)")
        if valid:
            out.append({
                'class': 'at', 'n': n, 'ms': list(ms),
                'cycle': [list(c) for c in cycle],
                'movers': movers, 'det': dict(comp),
                'L': len(cycle),
                'verify_valid': True,
                'product': int(np.prod(ms)),
            })
    return out


def build_sub_corpus(per_n=8):
    print("=== P1 sub-threshold corpus (classes 1/2 — 3/4/5 are empty at strict sub) ===")
    L_max_by_n = {5: 40, 6: 24, 7: 18}
    out = []
    for n in (5, 6, 7):
        Mn = m_n(n)
        multisets = enumerate_multisets(n, Mn)
        print(f"  n={n} M_n={Mn} total multisets={len(multisets)}")
        # Take evenly-strided sample
        stride = max(1, len(multisets) // (per_n + 1))
        sample = multisets[::stride][:per_n]
        for ms in sample:
            cycles = enumerate_all_cycles(ms, n, L_max_by_n[n], 2.0, 1)
            for cycle, movers, det in cycles:
                out.append({
                    'class': 'sub', 'n': n, 'ms': list(ms),
                    'cycle': cycle, 'movers': movers, 'det': dict(det),
                    'L': len(cycle), 'product': int(np.prod(ms)),
                })
    return out


# ======================================================================
# Main
# ======================================================================

def main():
    print("=" * 72)
    print("Wave 3 combined probe")
    print("=" * 72)

    t_g0 = time.time()
    at_corpus = build_at_corpus()
    sub_corpus = build_sub_corpus(per_n=8)
    print(f"\nCorpus: {len(at_corpus)} at-threshold, {len(sub_corpus)} sub-threshold")

    # Analyze all under v2 baseline
    print("\n--- Running C1 baseline (v2) ---")
    v2_results = []
    all_records = at_corpus + sub_corpus
    for i, r in enumerate(all_records):
        print(f"[{i+1}/{len(all_records)}] {r['class']} n={r['n']} "
              f"ms={r['ms']} L={r['L']}", flush=True)
        o = analyze_record(r, variant='v2')
        v2_results.append(o)
        print(f"  class={o['composition_class']} feas={o['feasible']} "
              f"supp={o['supp_size']} types={o['supp_edge_type_hist']} "
              f"stab={o['stab_time_shift']}/{r['L']}")

    # --- P1 outcomes ---
    sub_v2 = [r for r in v2_results if r['class'] == 'sub']
    at_v2 = [r for r in v2_results if r['class'] == 'at']
    print("\n=== P1 outcomes ===")
    print(f"sub feasible: {sum(1 for r in sub_v2 if r['feasible'])}/{len(sub_v2)}")
    print(f" at feasible: {sum(1 for r in at_v2 if r['feasible'])}/{len(at_v2)}")
    class_counts = Counter(r['composition_class'] for r in sub_v2)
    print(f"sub composition classes: {dict(class_counts)}")
    # per-class feasibility
    for cc in (1, 2):
        cc_rec = [r for r in sub_v2 if r['composition_class'] == cc]
        if cc_rec:
            feas = sum(1 for r in cc_rec if r['feasible'])
            print(f"  class {cc}: {feas}/{len(cc_rec)} feasible")

    # --- P2 balance identity ---
    print("\n=== P2 balance identity ===")
    bal = balance_identity_test(v2_results)
    for b in bal[:10]:  # show first 10
        print(f"  {b['class']} n={b['n']} ms={b['ms']} L={b['L']}: "
              f"max_total={b['max_per_vertex_total']:.2e} "
              f"lead_resid/T={b['leading_over_T_ratio']:.3f} "
              f"sub/T={b['sub_over_T_ratio']:.3f}")
    if bal:
        mean_lead = np.mean([b['leading_over_T_ratio'] for b in bal])
        mean_sub = np.mean([b['sub_over_T_ratio'] for b in bal])
        print(f"\n  mean leading_residual/T = {mean_lead:.3f}")
        print(f"  mean subleading/T = {mean_sub:.3f}")

    # --- P3 reverse-cycle ---
    print("\n=== P3 c_right asymmetry (reverse-cycle test) ===")
    rev_results = []
    rev_targets = [r for r in sub_corpus if r['n'] == 6][:3]
    for r in rev_targets:
        r_rev = reverse_cycle_record(r)
        if r_rev is None:
            print(f"  {r['ms']}: reverse detOf conflict — skipped")
            continue
        o_fwd = next(o for o in v2_results
                     if o['class']=='sub' and o['ms']==r['ms'] and o['L']==r['L'])
        o_rev = analyze_record(r_rev, variant='v2')
        rev_results.append({'ms': r['ms'], 'L': r['L'],
                            'fwd_types': o_fwd['supp_edge_type_hist'],
                            'rev_types': o_rev['supp_edge_type_hist'],
                            'rev_feasible': o_rev['feasible']})
        print(f"  ms={r['ms']}")
        print(f"    fwd supp types: {o_fwd['supp_edge_type_hist']}")
        print(f"    rev supp types: {o_rev['supp_edge_type_hist']}")

    # --- P5 regression ---
    print("\n=== P5 scalar-feature regression ===")
    reg = scenario_b_regression(v2_results)
    print(f"  n_records={reg.get('n_records')} "
          f"R²_lin={reg.get('r_squared_linear')} "
          f"acc={reg.get('threshold_accuracy')}")

    # --- P6 coverage CI ---
    print("\n=== P6 coverage correlation ===")
    cov = coverage_ci(v2_results)
    print(f"  cor={cov['cor']:.3f}  95% CI=[{cov['ci_lo']:.3f}, {cov['ci_hi']:.3f}] "
          f"n={cov['n']} boot={cov.get('n_boot')}")

    # --- P7 perturbation ---
    print("\n=== P7 perturbation variants ===")
    pert_sample = sub_corpus[:5] + at_corpus
    pert_results = []
    for variant in ('v2a', 'v2b', 'v2c'):
        print(f"  variant {variant}:")
        for r in pert_sample:
            try:
                o = analyze_record(r, variant=variant)
                pert_results.append({'variant': variant, 'class': r['class'],
                                     'ms': r['ms'], 'L': r['L'],
                                     'feasible': o['feasible'],
                                     'supp_size': o['supp_size']})
                print(f"    {r['class']} ms={r['ms']}: feas={o['feasible']} "
                      f"supp={o['supp_size']}")
            except Exception as e:
                pert_results.append({'variant': variant, 'class': r['class'],
                                     'ms': r['ms'], 'error': str(e)})
                print(f"    {r['class']} ms={r['ms']}: ERROR {e}")

    # compare v2 vs variants
    print("\n  stability:")
    for variant in ('v2a', 'v2b', 'v2c'):
        flips = 0
        total = 0
        for pr in [p for p in pert_results if p.get('variant') == variant]:
            if 'feasible' not in pr: continue
            v2_match = next((o for o in v2_results
                             if o['class']==pr['class'] and o['ms']==pr['ms']
                             and o['L']==pr['L']), None)
            if v2_match is None: continue
            total += 1
            if v2_match['feasible'] != pr['feasible']: flips += 1
        print(f"    {variant}: {flips}/{total} flipped from v2")

    # Write outputs (strip in-memory heavy fields)
    slim_v2 = [{k: v for k, v in o.items() if not k.startswith('_') and k != 'phi'}
               for o in v2_results]
    out_payload = {
        'at_corpus_size': len(at_corpus),
        'sub_corpus_size': len(sub_corpus),
        'v2_results': slim_v2,
        'balance_identity': bal,
        'reverse_cycle': rev_results,
        'regression': reg,
        'coverage': cov,
        'perturbation': pert_results,
        'runtime_s': round(time.time() - t_g0, 1),
    }
    out_path = os.path.join(HERE, "phaseW3_results.json")
    try:
        with open(out_path, "w") as f:
            json.dump(out_payload, f, indent=2, default=str)
        print(f"\nWrote {out_path}  (runtime {time.time()-t_g0:.1f}s)")
    except Exception as e:
        print(f"\nWrite failed: {e}")


if __name__ == "__main__":
    main()
