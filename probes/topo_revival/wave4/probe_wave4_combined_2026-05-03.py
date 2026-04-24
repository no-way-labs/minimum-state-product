#!/usr/bin/env python3
"""Wave 4 combined probe — P0 dispositive + P0.5 audit + P1/P2/P3 conditional.

P0 is dispositive and runs first. If P0 Case B fires (any small-n witness
feasible in C1), the probe stops — route is RED, no point in P1-P4.

P0.5 runs in parallel to P0 — classifies every edge under a logging
classifier, enumerates `other_*` patterns, reports them as bugs vs new-type.

P1 (direction-covariant decomposition): merge c_right + c_left, test
  |T(v) + W_sided(v)| / |T(v)| < 0.01 on feasible sub records.

P2+P3 (richer arithmetic regression): re-run regression on corpus
  (19 sub + 6 CLB at + 4 small-n witnesses = 29 records) with 6 basic
  + 5 richer features. Check whether `n_bin >= 3` still achieves 100%
  accuracy (tautology) or whether richer features are required.
"""
from __future__ import annotations

import json
import os
import sys
import time
from collections import Counter, defaultdict
from itertools import product as iproduct
from math import gcd

import numpy as np
from scipy.optimize import linprog

HERE = os.path.dirname(os.path.abspath(__file__))
CLAUDE_DIR = os.path.abspath(os.path.join(HERE, "..", "..", "..", "..", "claude"))
DOCS_DIR = os.path.abspath(os.path.join(HERE, "..", "..", "..", "..", "docs"))
sys.path.insert(0, CLAUDE_DIR)
sys.path.insert(0, DOCS_DIR)

from verifier import verify_system  # type: ignore
import verify_witnesses as vw  # type: ignore


# ======================================================================
# Witness loading
# ======================================================================

def build_record_from_witness(name, state_counts, rules):
    """Turn a verify_witnesses-style (ms, rules) into a full record with
    good cycle + movers + detOf. Verifies the system first."""
    ms = list(state_counts)
    n = len(ms)

    def make_f(p_idx, rule_p):
        def f(L, S, R):
            return rule_p[(L, S, R)]
        return f

    fs = [make_f(p, rules[p]) for p in range(n)]
    v = verify_system(ms, fs, verbose=False)
    if not v['valid']:
        return None

    # Extract good cycle via the same logic as verify_witnesses
    configs = list(iproduct(*(range(m) for m in ms)))
    def privileged(cfg):
        priv = []
        for i in range(n):
            L = cfg[(i - 1) % n]
            S = cfg[i]
            R = cfg[(i + 1) % n]
            if fs[i](L, S, R) != S:
                priv.append(i)
        return priv
    def move(cfg, proc):
        L = cfg[(proc - 1) % n]; S = cfg[proc]; R = cfg[(proc + 1) % n]
        new_S = fs[proc](L, S, R)
        lst = list(cfg); lst[proc] = new_S
        return tuple(lst)

    single_priv = {}
    for cfg in configs:
        p = privileged(cfg)
        if len(p) == 1:
            single_priv[cfg] = (move(cfg, p[0]), p[0])

    good_cycle = None; good_movers = None
    for start in single_priv:
        path = []; movers = []; visited = set(); cur = start
        while cur in single_priv and cur not in visited:
            visited.add(cur); path.append(cur)
            nxt, mover = single_priv[cur]
            movers.append(mover); cur = nxt
        if cur == start and path:
            good_cycle = path; good_movers = movers; break

    if good_cycle is None:
        return None

    # Build detOf: all (p, L, S, R) triples seen at any cycle config
    det = {}
    for idx in range(len(good_cycle)):
        c = good_cycle[idx]
        mv = good_movers[idx]
        c_next = good_cycle[(idx + 1) % len(good_cycle)]
        for p in range(n):
            Lv = c[(p - 1) % n]; Sv = c[p]; Rv = c[(p + 1) % n]
            key = (p, Lv, Sv, Rv)
            if p == mv:
                det[key] = c_next[p]
            else:
                det[key] = Sv

    # Also extend det with witness rules at every triple encountered on
    # all configs (full detOf from rules).
    for cfg in configs:
        for p in range(n):
            Lv = cfg[(p - 1) % n]; Sv = cfg[p]; Rv = cfg[(p + 1) % n]
            key = (p, Lv, Sv, Rv)
            if key not in det:
                det[key] = fs[p](Lv, Sv, Rv)

    return {
        'class': 'at_smallN', 'name': name,
        'n': n, 'ms': ms,
        'cycle': [list(c) for c in good_cycle],
        'movers': good_movers,
        'det': det,
        'L': len(good_cycle),
        'product': int(np.prod(ms)),
    }


def load_smalln_witnesses():
    recs = []
    for attr, label in [('witness_n5', 'w5'), ('witness_n6', 'w6'),
                        ('witness_n7', 'w7'), ('witness_n8', 'w8')]:
        fn = getattr(vw, attr, None)
        if fn is None:
            print(f"  {attr}: not found"); continue
        ms, rules = fn()
        r = build_record_from_witness(label, ms, rules)
        if r is None:
            print(f"  {label}: verify_system FAILED or no good cycle"); continue
        print(f"  {label}: ms={r['ms']} prod={r['product']} L={r['L']}")
        recs.append(r)
    return recs


# ======================================================================
# Lifted graph + LP — copied from wave3 baseline with instrumentation
# ======================================================================

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


def build_lifted_graph(rec, log_other=True):
    ms = rec['ms']; n = len(ms)
    cycle = [tuple(c) for c in rec['cycle']]
    movers = rec['movers']
    L = len(cycle)
    det = rec['det']
    cycle_set = set(cycle)
    V_tube = value_set_tube(cycle, n)
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

    E_lift = []
    other_patterns = defaultdict(int)
    for src_v in V_lift:
        k, q, a = src_v
        c = tube_configs[src_v]
        mov_k = movers[k] if k < len(movers) else None
        adj_q = {(q - 1) % n, q, (q + 1) % n}
        for p_fire in range(n):
            ctx = (p_fire, c[(p_fire - 1) % n], c[p_fire], c[(p_fire + 1) % n])
            v_new = move_entries.get(ctx)
            if v_new is None or v_new == c[p_fire]: continue
            c_succ = list(c); c_succ[p_fire] = v_new; c_succ = tuple(c_succ)
            # classify (with instrumentation)
            if p_fire == mov_k and p_fire not in adj_q:
                edge_type = 'transport'
            elif p_fire == q:
                edge_type = 'c_self'
            elif p_fire == (q - 1) % n:
                edge_type = 'c_left'
            elif p_fire == (q + 1) % n:
                edge_type = 'c_right'
            else:
                # "other" bucket: track pattern
                rel_mov = (mov_k - q) % n if mov_k is not None else None
                rel_fire = (p_fire - q) % n
                pat = (rel_mov, rel_fire)
                if log_other:
                    other_patterns[pat] += 1
                edge_type = f'other[rel_mov={rel_mov},rel_fire={rel_fire}]'
            tgt_v = None
            if edge_type == 'transport':
                cand = ((k + 1) % L, q, a)
                if cand in idx_of: tgt_v = cand
            if tgt_v is None:
                if c_succ in cycle_set:
                    continue
                for kk in range(L):
                    c_kk = cycle[kk]
                    diff = [(i, c_succ[i]) for i in range(n)
                            if c_succ[i] != c_kk[i]]
                    if len(diff) == 1:
                        qq, aa = diff[0]
                        cand = (kk, qq, aa)
                        if cand in idx_of:
                            tgt_v = cand; break
                if tgt_v is None:
                    continue
            E_lift.append((idx_of[src_v], idx_of[tgt_v], edge_type))

    return V_lift, E_lift, other_patterns


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
    return {'feasible': obj < -1e-9, 'supp_size': len(supp),
            'support': supp, 'phi': x.tolist(), 'objective': obj}


def analyze_record(rec):
    V_lift, E_lift, other_patterns = build_lifted_graph(rec)
    lp = solve_circulation_lp(len(V_lift), E_lift)
    support = lp.get('support', [])
    etype_total = Counter(e[2].split('[')[0] for e in E_lift)
    supp_types = Counter(E_lift[i][2].split('[')[0] for i in support) if support else Counter()
    return {
        'class': rec['class'], 'n': rec['n'], 'ms': rec['ms'], 'L': rec['L'],
        'product': rec['product'],
        'composition_class': classify_composition(rec['ms']),
        'coverage': rec['L'] / (rec['n'] * rec['product']),
        'nV_lift': len(V_lift), 'nE_lift': len(E_lift),
        'edge_type_hist': dict(etype_total),
        'feasible': lp.get('feasible', False),
        'supp_size': lp.get('supp_size', 0),
        'supp_edge_type_hist': dict(supp_types),
        'other_patterns': dict(other_patterns),
        'phi': lp.get('phi', []),
        '_V_lift': V_lift, '_E_lift': E_lift, 'name': rec.get('name'),
    }


# ======================================================================
# Wave 3 corpus rebuild (needed for P1, P2)
# ======================================================================

def m_n(n):
    return 32 * 3 ** (n - 4) if 5 <= n <= 8 else 4 * 3 ** (n - 2)


def enumerate_multisets(n, max_product):
    out = []
    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product: out.append(tuple(prefix))
            return
        for m in range(2, max_product + 1):
            new_prod = prod * m
            min_rem = 2 ** (n - i - 1)
            if new_prod * min_rem >= max_product: break
            prefix.append(m); rec(i + 1, prefix, new_prod); prefix.pop()
    rec(0, [], 1)
    return out


def enumerate_cycles(ms, n, L_max, time_budget, max_cycles=1):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []; seen = set(); t0 = time.time()
    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen:
                seen.add(norm); found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max: return
        for p in range(n):
            Lp = config[(p-1)%n]; Sp = config[p]; Rp = config[(p+1)%n]
            km = (p, Lp, Sp, Rp); forced_out = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced_out is not None and forced_out != new_val: continue
                new_det = dict(det); new_det[km] = new_val; ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si: ok = False; break
                    new_det[ki] = Si
                if not ok: continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path): continue
                dfs(start, nc, new_det, path + [nc], movers + [p])
    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget: break
        dfs(start, start, {}, [start], [])
    return found


def build_sub_corpus(per_n=8):
    L_max = {5: 40, 6: 24, 7: 18}; out = []
    for n in (5, 6, 7):
        ms_list = enumerate_multisets(n, m_n(n))
        stride = max(1, len(ms_list) // (per_n + 1))
        for ms in ms_list[::stride][:per_n]:
            cycles = enumerate_cycles(ms, n, L_max[n], 2.0, 1)
            for cycle, movers, det in cycles:
                out.append({'class': 'sub', 'n': n, 'ms': list(ms),
                            'cycle': cycle, 'movers': movers, 'det': dict(det),
                            'L': len(cycle), 'product': int(np.prod(ms))})
    return out


def build_clb_witness_v2(n: int):
    ms = (2,) + (3,) * (n - 2) + (2,)
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n; cycle = [tuple(config)]; visited = {tuple(config)}
    full = up_down * 5; movers = []
    for step, mover in enumerate(full):
        config = list(cycle[-1]); config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config); movers.append(mover)
        if nc == cycle[0]: break
        if nc in visited: raise RuntimeError("bounce cycle didn't close")
        visited.add(nc); cycle.append(nc)
    L = len(cycle); movers = movers[:L]
    good_set = set(cycle)
    all_configs = list(iproduct(*(range(m) for m in ms)))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)
    det = {}
    for idx in range(L):
        c = cycle[idx]; c_next = cycle[(idx+1)%L]; mv = movers[idx]
        for p in range(n):
            Lv=c[(p-1)%n];Sv=c[p];Rv=c[(p+1)%n]; key=(p,Lv,Sv,Rv)
            det[key] = c_next[p] if p == mv else Sv
    free_entries = []
    for p in range(n):
        for Lv in range(ms[(p-1)%n]):
            for Sv in range(ms[p]):
                for Rv in range(ms[(p+1)%n]):
                    key = (p,Lv,Sv,Rv)
                    if key not in det: free_entries.append(key)
    edge_costs = {}
    for key in free_entries:
        p,Lv,Sv,Rv = key
        for out in range(ms[p]):
            if out == Sv: edge_costs[(key,out)] = 0
            else:
                edges = sum(1 for c in non_good
                            if c[(p-1)%n]==Lv and c[p]==Sv and c[(p+1)%n]==Rv
                            and tuple(c[j] if j!=p else out for j in range(n)) in non_good_set)
                edge_costs[(key,out)] = edges
    comp = dict(det)
    for key in free_entries:
        p,Lv,Sv,Rv = key; best_out=Sv; best_good=0; best_ng=float('inf')
        for out in range(ms[p]):
            ng = edge_costs.get((key,out),0); good_count = 0
            if out != Sv:
                good_count = sum(1 for c in non_good
                                 if c[(p-1)%n]==Lv and c[p]==Sv and c[(p+1)%n]==Rv
                                 and tuple(c[j] if j!=p else out for j in range(n)) in good_set)
            if good_count > best_good or (good_count==best_good and ng < best_ng):
                best_out=out; best_good=good_count; best_ng=ng
        comp[key] = best_out
    for c in all_configs:
        has_priv = any(comp.get((p, c[(p-1)%n], c[p], c[(p+1)%n]), c[p]) != c[p]
                       for p in range(n))
        if not has_priv:
            best_key=None; best_cost=float('inf'); best_out_val=None
            for p in range(n):
                L2=c[(p-1)%n]; S2=c[p]; R2=c[(p+1)%n]; key=(p,L2,S2,R2)
                if key not in det:
                    for out in range(ms[p]):
                        if out != S2:
                            cost = edge_costs.get((key,out),0)
                            if cost < best_cost:
                                best_cost=cost; best_key=key; best_out_val=out
            if best_key: comp[best_key] = best_out_val
    def make_f(p_idx):
        def f(L,S,R): return comp.get((p_idx,L,S,R),S)
        return f
    return list(ms), [make_f(p) for p in range(n)], comp, cycle, movers


def build_at_corpus():
    out = []
    for n in range(5, 11):
        try:
            ms, fs, comp, cycle, movers = build_clb_witness_v2(n)
        except Exception as e:
            continue
        v = verify_system(ms, fs, verbose=False)
        if v['valid']:
            out.append({'class': 'at_clb', 'n': n, 'ms': list(ms),
                        'cycle': [list(c) for c in cycle], 'movers': movers,
                        'det': dict(comp), 'L': len(cycle),
                        'product': int(np.prod(ms))})
    return out


# ======================================================================
# P1 — direction-covariant (c_sided = c_left+c_right) decomposition
# ======================================================================

def direction_covariant_balance(r):
    if not r.get('feasible') or '_E_lift' not in r: return None
    E_lift = r['_E_lift']; phi = r['phi']
    nV = max((max(s, t) for s, t, _ in E_lift), default=-1) + 1
    T = np.zeros(nV); W_sided = np.zeros(nV); W_self = np.zeros(nV); W_other = np.zeros(nV)
    for e_idx, (s, t, etype) in enumerate(E_lift):
        w = phi[e_idx]; base = etype.split('[')[0]
        if base == 'transport': arr = T
        elif base in ('c_left', 'c_right'): arr = W_sided
        elif base == 'c_self': arr = W_self
        else: arr = W_other
        arr[s] -= w; arr[t] += w
    norm_T = float(np.sum(np.abs(T)))
    if norm_T == 0: return None
    leading = T + W_sided
    max_lead = float(np.max(np.abs(leading)))
    max_T_wsided_wself = float(np.max(np.abs(T + W_sided + W_self)))
    return {
        'sum_abs_T': norm_T,
        'max_T_plus_Wsided_norm_T': max_lead / norm_T if norm_T > 0 else 0,
        'sum_abs_W_sided': float(np.sum(np.abs(W_sided))),
        'sum_abs_W_self': float(np.sum(np.abs(W_self))),
        'sum_abs_W_other': float(np.sum(np.abs(W_other))),
        'W_self_over_T_plus_Wsided': float(np.sum(np.abs(W_self))) / max(max_lead, 1e-9),
    }


# ======================================================================
# P2+P3 — regression with expanded features
# ======================================================================

def feature_vector(rec):
    ms = rec['ms']; n = rec['n']; L = rec['L']; prod = rec['product']
    n_bin = sum(1 for m in ms if m == 2)
    n_ter = sum(1 for m in ms if m == 3)
    n_geq4 = sum(1 for m in ms if m >= 4)
    # longest run of consecutive binaries (on ring)
    longest_bin = 0
    if n_bin > 0:
        cur = 0
        for m in ms + ms[:n-1]:
            if m == 2: cur += 1; longest_bin = max(longest_bin, cur)
            else: cur = 0
        longest_bin = min(longest_bin, n_bin)
    # LCM of non-binary segments between binary blocks
    non_bin_segments = []
    ms_ext = list(ms)
    in_seg = False; seg = []
    for m in ms_ext + [ms_ext[0]]:
        if m != 2:
            seg.append(m); in_seg = True
        else:
            if in_seg and seg:
                non_bin_segments.append(seg); seg = []
            in_seg = False
    lcm_non_bin = 1
    for seg in non_bin_segments:
        s_lcm = 1
        for m in seg:
            s_lcm = s_lcm * m // gcd(s_lcm, m)
        lcm_non_bin = lcm_non_bin * s_lcm // gcd(lcm_non_bin, s_lcm)
    # mover variance
    movers = rec.get('movers', [])
    mover_var = float(np.var(movers)) if movers else 0.0
    # longest mover run
    longest_mov_run = 0
    if movers:
        cur = 1
        for i in range(1, len(movers)):
            if movers[i] == movers[i-1]: cur += 1
            else:
                longest_mov_run = max(longest_mov_run, cur); cur = 1
        longest_mov_run = max(longest_mov_run, cur)
    return {
        'n': n, 'L': L, 'log_prod': float(np.log(prod)),
        'n_bin': n_bin, 'n_ter': n_ter, 'n_geq4': n_geq4,
        'longest_bin_run': longest_bin,
        'lcm_non_bin_seg': lcm_non_bin,
        'mover_var': mover_var,
        'longest_mov_run': longest_mov_run,
    }


def tautology_check(records):
    """Does n_bin >= 3 perfectly separate feasibility?"""
    err_nbin3 = 0; err_nbin_ge4 = 0
    for r in records:
        feas = r['feasible']
        ms = r['ms']; n_bin = sum(1 for m in ms if m == 2)
        pred_nbin3 = (n_bin >= 3)
        if pred_nbin3 != feas: err_nbin3 += 1
    return {'n_bin_ge3_errors': err_nbin3,
            'n_records': len(records),
            'acc_n_bin_ge3': 1.0 - err_nbin3 / max(1, len(records))}


def richer_regression(records):
    rs = [r for r in records if 'feasible' in r]
    if len(rs) < 6: return {'skipped': 'too few'}
    X = []; y = []; feat_names = None
    for r in rs:
        fv = feature_vector(r); feat_names = list(fv.keys())
        X.append([fv[k] for k in feat_names])
        y.append(1.0 if r['feasible'] else 0.0)
    X = np.array(X); y = np.array(y)
    X1 = np.hstack([np.ones((len(X), 1)), X])
    beta, *_ = np.linalg.lstsq(X1, y, rcond=None)
    yhat = X1 @ beta
    sse = float(np.sum((y - yhat) ** 2)); sst = float(np.sum((y - y.mean()) ** 2))
    r_sq = 1 - sse / sst if sst > 0 else 0.0
    acc = float(np.mean((yhat >= 0.5).astype(int) == y))
    # leave-one-out acc
    loo_correct = 0
    for i in range(len(rs)):
        mask = np.arange(len(rs)) != i
        try:
            b, *_ = np.linalg.lstsq(X1[mask], y[mask], rcond=None)
            ph = X1[i] @ b
            if (ph >= 0.5) == (y[i] >= 0.5): loo_correct += 1
        except Exception:
            pass
    return {
        'n_records': len(rs), 'r_squared': r_sq,
        'threshold_accuracy': acc,
        'loo_accuracy': loo_correct / len(rs),
        'features': ['bias'] + feat_names,
        'beta': beta.tolist(),
    }


# ======================================================================
# Main
# ======================================================================

def main():
    print("=" * 72)
    print("Wave 4 combined probe — dispositive P0 + P1/P2/P3/P0.5")
    print("=" * 72)
    t0 = time.time()

    # --- P0: small-n witnesses ---
    print("\n=== P0 small-n witness loading ===")
    smalln = load_smalln_witnesses()

    print(f"\n--- P0 C1 on small-n witnesses ({len(smalln)} records) ---")
    p0_results = []
    for r in smalln:
        o = analyze_record(r)
        p0_results.append(o)
        print(f"  {o['name']} ms={o['ms']} L={o['L']}: "
              f"feas={o['feasible']} supp={o['supp_size']} "
              f"types={o['supp_edge_type_hist']} other={o['other_patterns']}")

    feas_at_smallN = sum(1 for o in p0_results if o['feasible'])
    if feas_at_smallN > 0:
        print(f"\n*** P0 Case B: {feas_at_smallN}/{len(p0_results)} small-n witnesses "
              f"feasible. ROUTE RED. Stopping. ***")
        payload = {'p0_case': 'B_route_red', 'p0_results':
                   [{k: v for k, v in o.items() if not k.startswith('_')}
                    for o in p0_results]}
        out_path = os.path.join(HERE, "phaseW4_results.json")
        try:
            with open(out_path, "w") as f:
                json.dump(payload, f, indent=2, default=str)
            print(f"Wrote {out_path}")
        except Exception as e:
            print(f"Write failed: {e}")
        return

    print(f"\n*** P0 Case A: {len(p0_results)}/{len(p0_results)} small-n witnesses "
          f"infeasible. Circulation discrimination survives at 3-binary. "
          f"Proceeding to P1–P4. ***")

    # --- Build full corpus (P1+P2 need it) ---
    print("\n--- Corpus expansion (sub + CLB at + small-n) ---")
    sub_corpus = build_sub_corpus(per_n=8)
    at_clb_corpus = build_at_corpus()
    print(f"  sub={len(sub_corpus)}, CLB at={len(at_clb_corpus)}, "
          f"small-n={len(smalln)}")

    print("\n--- Re-analyzing full corpus (slow step) ---")
    all_results = list(p0_results)  # already analyzed small-n
    for r in sub_corpus + at_clb_corpus:
        o = analyze_record(r)
        all_results.append(o)

    # --- P0.5 classify_type audit: any 'other' edges in forward direction? ---
    print("\n=== P0.5 classify_type audit ===")
    all_other = Counter()
    for o in all_results:
        for pat, cnt in o['other_patterns'].items():
            all_other[pat] += cnt
    total_edges = sum(sum(o['edge_type_hist'].values()) for o in all_results)
    total_other = sum(all_other.values())
    print(f"  forward-direction 'other' edges: {total_other} / {total_edges} "
          f"({100*total_other/max(1,total_edges):.3f}%)")
    if all_other:
        print("  'other' pattern breakdown (rel_mov, rel_fire -> count):")
        for pat, cnt in sorted(all_other.items(), key=lambda x: -x[1])[:20]:
            print(f"    {pat}: {cnt}")

    # --- P1 direction-covariant balance ---
    print("\n=== P1 direction-covariant decomposition ===")
    sub_feasible = [o for o in all_results if o['class'] == 'sub' and o['feasible']]
    p1_stats = []
    for o in sub_feasible:
        b = direction_covariant_balance(o)
        if b:
            p1_stats.append({'ms': o['ms'], 'L': o['L'], **b})
            print(f"  ms={o['ms']} L={o['L']}: "
                  f"|T+Wsided|/|T|={b['max_T_plus_Wsided_norm_T']:.3f} "
                  f"|W_self|/|T+Wsided|={b['W_self_over_T_plus_Wsided']:.3f}")
    if p1_stats:
        mean_lead = np.mean([s['max_T_plus_Wsided_norm_T'] for s in p1_stats])
        mean_sub = np.mean([s['W_self_over_T_plus_Wsided'] for s in p1_stats])
        print(f"\n  mean |T+Wsided|/|T| = {mean_lead:.4f}")
        print(f"  mean |W_self|/|T+Wsided| = {mean_sub:.4f}")
        print(f"  plan §3.3 threshold: <0.01  -> "
              f"{'PASS' if mean_lead < 0.01 else 'FAIL (RED)'}")

    # --- P2+P3 regression on expanded corpus ---
    print("\n=== P2+P3 regression on expanded corpus ===")
    taut = tautology_check(all_results)
    print(f"  n_bin>=3 classifier: acc={taut['acc_n_bin_ge3']:.3f} "
          f"({taut['n_bin_ge3_errors']} errors / {taut['n_records']})")
    if taut['acc_n_bin_ge3'] == 1.0:
        print("  *** TAUTOLOGY: n_bin>=3 perfectly separates feasibility. ***")
        print("  Scenario (b) confirmed on this corpus.")
    reg = richer_regression(all_results)
    print(f"  richer regression: R²={reg.get('r_squared'):.3f} "
          f"acc={reg.get('threshold_accuracy'):.3f} "
          f"loo_acc={reg.get('loo_accuracy'):.3f}")
    if reg.get('beta'):
        print("  top features by coefficient magnitude:")
        pairs = sorted(zip(reg['features'], reg['beta']),
                       key=lambda x: -abs(x[1]))[:7]
        for name, b in pairs:
            print(f"    {name}: {b:+.3f}")

    # --- P4 ARG comparison (prose stub) ---
    print("\n=== P4 ARG comparison — see memo §6 ===")

    # --- Write results ---
    slim_results = [{k: v for k, v in o.items() if not k.startswith('_') and k != 'phi'}
                    for o in all_results]
    payload = {
        'p0_case': 'A_proceed',
        'p0_results': [{k: v for k, v in o.items() if not k.startswith('_') and k != 'phi'}
                       for o in p0_results],
        'corpus_all_results': slim_results,
        'p05_other_patterns': {str(k): v for k, v in all_other.items()},
        'p05_other_total': total_other,
        'p05_edges_total': total_edges,
        'p1_direction_covariant': p1_stats,
        'p2_tautology_check': taut,
        'p2_regression': reg,
        'runtime_s': round(time.time() - t0, 1),
    }
    out_path = os.path.join(HERE, "phaseW4_results.json")
    try:
        with open(out_path, "w") as f:
            json.dump(payload, f, indent=2, default=str)
        print(f"\nWrote {out_path} ({time.time()-t0:.1f}s)")
    except Exception as e:
        print(f"Write failed: {e}")


if __name__ == "__main__":
    main()
