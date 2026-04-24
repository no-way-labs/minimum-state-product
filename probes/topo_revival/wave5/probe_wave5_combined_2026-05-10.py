#!/usr/bin/env python3
"""Wave 5 terminal probe queue — P7, P1.5, sharpness, random, P5, tropical.

Queue-executed: any probe that produces a proof-shaped result triggers
integration into paper. Queue exhausted → paper as conjecture + evidence.

P8 Conley index not included here (highest implementation cost, run
separately if budget permits).
"""
from __future__ import annotations

import json
import os
import random
import sys
import time
from collections import Counter, defaultdict
from itertools import product as iproduct, combinations
from math import gcd

import numpy as np
from scipy.optimize import linprog

HERE = os.path.dirname(os.path.abspath(__file__))
CLAUDE_DIR = os.path.abspath(os.path.join(HERE, "..", "..", "..", "..", "claude"))
DOCS_DIR = os.path.abspath(os.path.join(HERE, "..", "..", "..", "..", "docs"))
sys.path.insert(0, CLAUDE_DIR); sys.path.insert(0, DOCS_DIR)
from verifier import verify_system  # type: ignore
import verify_witnesses as vw  # type: ignore


# ======================================================================
# Reused infrastructure from Wave 3/4 (abbreviated)
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
            if new_prod * (2 ** (n - i - 1)) >= max_product: break
            prefix.append(m); rec(i + 1, prefix, new_prod); prefix.pop()
    rec(0, [], 1)
    return out


def enumerate_cycles(ms, n, L_max, time_budget=2.0, max_cycles=1):
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
            Lp=config[(p-1)%n]; Sp=config[p]; Rp=config[(p+1)%n]
            km=(p,Lp,Sp,Rp); forced_out=det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced_out is not None and forced_out != new_val: continue
                new_det = dict(det); new_det[km] = new_val; ok = True
                for i in range(n):
                    if i == p: continue
                    Li=config[(i-1)%n]; Si=config[i]; Ri=config[(i+1)%n]
                    ki=(i,Li,Si,Ri)
                    if ki in new_det and new_det[ki] != Si: ok=False; break
                    new_det[ki] = Si
                if not ok: continue
                nc=list(config); nc[p]=new_val; nc=tuple(nc)
                if nc != start and nc in set(path): continue
                dfs(start, nc, new_det, path+[nc], movers+[p])
    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget: break
        dfs(start, start, {}, [start], [])
    return found


def value_set_tube(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for q in range(n): V[q].add(c[q])
    return [sorted(s) for s in V]


def build_lifted_graph(rec):
    ms = rec['ms']; n = len(ms)
    cycle = [tuple(c) for c in rec['cycle']]
    movers = rec['movers']
    L = len(cycle); det = rec['det']
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
                idx_of[key] = len(V_lift); V_lift.append(key)
                tube_configs[key] = nc
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
            if p_fire == mov_k and p_fire not in adj_q: edge_type = 'transport'
            elif p_fire == q: edge_type = 'c_self'
            elif p_fire == (q-1)%n: edge_type = 'c_left'
            elif p_fire == (q+1)%n: edge_type = 'c_right'
            else: edge_type = 'other'
            tgt_v = None
            if edge_type == 'transport':
                cand = ((k+1)%L, q, a)
                if cand in idx_of: tgt_v = cand
            if tgt_v is None:
                if c_succ in cycle_set: continue
                for kk in range(L):
                    c_kk = cycle[kk]
                    diff = [(i, c_succ[i]) for i in range(n) if c_succ[i] != c_kk[i]]
                    if len(diff) == 1:
                        qq, aa = diff[0]
                        cand = (kk, qq, aa)
                        if cand in idx_of: tgt_v = cand; break
                if tgt_v is None: continue
            E_lift.append((idx_of[src_v], idx_of[tgt_v], edge_type))
    return V_lift, E_lift


def solve_lp(n_vert, E_lift):
    nE = len(E_lift)
    if nE == 0: return {'feasible': False, 'supp_size': 0, 'phi': []}
    Aeq = np.zeros((n_vert, nE))
    for e_idx, (s, t, _) in enumerate(E_lift):
        Aeq[s, e_idx] -= 1; Aeq[t, e_idx] += 1
    beq = np.zeros(n_vert); c = -np.ones(nE); bounds = [(0.0, 1.0)] * nE
    res = linprog(c, A_eq=Aeq, b_eq=beq, bounds=bounds, method='highs')
    if not res.success: return {'feasible': False, 'supp_size': 0, 'phi': []}
    x = res.x; obj = float(res.fun)
    return {'feasible': obj < -1e-9,
            'supp_size': sum(1 for xi in x if xi > 1e-6),
            'phi': x.tolist()}


def c1_detector(rec):
    V, E = build_lifted_graph(rec)
    lp = solve_lp(len(V), E)
    return lp['feasible'], lp['supp_size'], V, E, lp['phi']


# Witness builders (abbreviated)

def build_clb_witness_v2(n):
    ms = (2,) + (3,) * (n - 2) + (2,)
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n; cycle = [tuple(config)]; visited = {tuple(config)}
    movers = []
    for step, mover in enumerate(up_down * 5):
        config = list(cycle[-1]); config[mover] = (config[mover]+1) % ms[mover]
        nc = tuple(config); movers.append(mover)
        if nc == cycle[0]: break
        if nc in visited: raise RuntimeError
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
            key=(p, c[(p-1)%n], c[p], c[(p+1)%n])
            det[key] = c_next[p] if p == mv else c[p]
    free_entries = [(p,L_,S_,R_) for p in range(n)
                    for L_ in range(ms[(p-1)%n]) for S_ in range(ms[p])
                    for R_ in range(ms[(p+1)%n])
                    if (p,L_,S_,R_) not in det]
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
            ng = edge_costs.get((key,out),0); good_count=0
            if out != Sv:
                good_count = sum(1 for c in non_good
                                 if c[(p-1)%n]==Lv and c[p]==Sv and c[(p+1)%n]==Rv
                                 and tuple(c[j] if j!=p else out for j in range(n)) in good_set)
            if good_count > best_good or (good_count==best_good and ng < best_ng):
                best_out=out; best_good=good_count; best_ng=ng
        comp[key] = best_out
    for c in all_configs:
        has_priv = any(comp.get((p,c[(p-1)%n],c[p],c[(p+1)%n]),c[p])!=c[p] for p in range(n))
        if not has_priv:
            best_key=None; best_cost=float('inf'); best_out_val=None
            for p in range(n):
                key=(p, c[(p-1)%n], c[p], c[(p+1)%n])
                if key not in det:
                    for out in range(ms[p]):
                        if out != c[p]:
                            cost = edge_costs.get((key,out),0)
                            if cost < best_cost:
                                best_cost=cost; best_key=key; best_out_val=out
            if best_key: comp[best_key] = best_out_val
    def make_f(p_idx):
        def f(L,S,R): return comp.get((p_idx,L,S,R),S)
        return f
    return list(ms), [make_f(p) for p in range(n)], comp, cycle, movers


def build_smalln_record(name, ms, rules):
    n = len(ms)
    def make_f(p, rp):
        def f(L,S,R): return rp[(L,S,R)]
        return f
    fs = [make_f(p, rules[p]) for p in range(n)]
    if not verify_system(ms, fs, verbose=False)['valid']: return None
    configs = list(iproduct(*(range(m) for m in ms)))
    single_priv = {}
    for cfg in configs:
        priv = [i for i in range(n)
                if fs[i](cfg[(i-1)%n], cfg[i], cfg[(i+1)%n]) != cfg[i]]
        if len(priv) == 1:
            mv = priv[0]
            nxt = list(cfg); nxt[mv] = fs[mv](cfg[(mv-1)%n], cfg[mv], cfg[(mv+1)%n])
            single_priv[cfg] = (tuple(nxt), mv)
    for start in single_priv:
        path=[]; movers=[]; visited=set(); cur=start
        while cur in single_priv and cur not in visited:
            visited.add(cur); path.append(cur)
            nxt, mv = single_priv[cur]; movers.append(mv); cur=nxt
        if cur == start and path:
            det = {}
            for idx in range(len(path)):
                c = path[idx]; c_next = path[(idx+1)%len(path)]; mv = movers[idx]
                for p in range(n):
                    key = (p, c[(p-1)%n], c[p], c[(p+1)%n])
                    det[key] = c_next[p] if p == mv else c[p]
            for cfg in configs:
                for p in range(n):
                    key = (p, cfg[(p-1)%n], cfg[p], cfg[(p+1)%n])
                    if key not in det:
                        det[key] = fs[p](cfg[(p-1)%n], cfg[p], cfg[(p+1)%n])
            return {'class': 'at_smallN', 'name': name, 'n': n, 'ms': list(ms),
                    'cycle': [list(c) for c in path], 'movers': movers,
                    'det': det, 'L': len(path), 'product': int(np.prod(ms))}
    return None


# ======================================================================
# P7 — sheaf extension-obstruction probe
# ======================================================================

def probe_p7_extension(rec):
    """Simplified H¹ proxy: count forced triples vs undetermined, and
    check whether an arbitrary "stay" completion produces a valid or
    invalid verify_system. If sub-threshold records systematically fail
    with a reason other than global convergence, that's H¹ signal."""
    ms = rec['ms']; n = len(ms); det = rec['det']
    # Enumerate all possible triples in rule domain
    total_triples = sum(ms[(p-1)%n] * ms[p] * ms[(p+1)%n] for p in range(n))
    forced = len(det)
    free = total_triples - forced
    # Try arbitrary "stay" completion: undefined triple (p,L,S,R) → S
    comp = dict(det)
    for p in range(n):
        for Lv in range(ms[(p-1)%n]):
            for Sv in range(ms[p]):
                for Rv in range(ms[(p+1)%n]):
                    key = (p, Lv, Sv, Rv)
                    if key not in comp:
                        comp[key] = Sv  # stay
    def make_f(p_idx):
        def f(L,S,R): return comp.get((p_idx,L,S,R), S)
        return f
    fs = [make_f(p) for p in range(n)]
    v = verify_system(ms, fs, verbose=False)
    # More informative: which property fails?
    failed = [k for k, (ok, _) in v['properties'].items() if not ok]
    return {
        'total_triples': total_triples,
        'forced_triples': forced,
        'free_triples': free,
        'forced_ratio': forced / total_triples,
        'stay_completion_valid': v['valid'],
        'failed_props': failed,
    }


# ======================================================================
# P1.5 — zero-residual subclass characterization
# ======================================================================

def direction_covariant_residual(r_analyzed):
    """Compute |T + W_sided|/|T| for a feasibility-analyzed record."""
    E = r_analyzed['_E_lift']; phi = r_analyzed['phi']
    n_vert = max((max(s, t) for s, t, _ in E), default=-1) + 1
    T = np.zeros(n_vert); W_sided = np.zeros(n_vert)
    for e_idx, (s, t, etype) in enumerate(E):
        w = phi[e_idx]; base = etype.split('[')[0]
        if base == 'transport': T[s] -= w; T[t] += w
        elif base in ('c_left', 'c_right'): W_sided[s] -= w; W_sided[t] += w
    norm_T = float(np.sum(np.abs(T)))
    max_lead = float(np.max(np.abs(T + W_sided)))
    return max_lead / norm_T if norm_T > 0 else 0.0


def subclass_features(rec):
    ms = rec['ms']; n = len(ms)
    n_bin = sum(1 for m in ms if m == 2)
    n_ter = sum(1 for m in ms if m == 3)
    n_geq4 = sum(1 for m in ms if m >= 4)
    # consecutive ternary runs (ring-adjacent)
    longest_ter = 0; cur = 0
    for m in ms + ms[:n-1]:
        if m == 3: cur += 1; longest_ter = max(longest_ter, cur)
        else: cur = 0
    longest_ter = min(longest_ter, n_ter)
    # consecutive binary runs
    longest_bin = 0; cur = 0
    for m in ms + ms[:n-1]:
        if m == 2: cur += 1; longest_bin = max(longest_bin, cur)
        else: cur = 0
    longest_bin = min(longest_bin, n_bin)
    # has adjacent (3,3)?
    has_33 = any(ms[i] == 3 and ms[(i+1) % n] == 3 for i in range(n))
    # has any m >= 4?
    has_geq4 = any(m >= 4 for m in ms)
    return {
        'n_bin': n_bin, 'n_ter': n_ter, 'n_geq4': n_geq4,
        'longest_bin_run': longest_bin, 'longest_ter_run': longest_ter,
        'has_consec_ternary': has_33, 'has_geq4': has_geq4,
        'ms_signature': tuple(sorted(ms)),
    }


# ======================================================================
# Sharpness probe
# ======================================================================

def sharpness_test(n, L_max):
    """For this n: find (a) largest ∏m < M_n with a good cycle, run C1.
    (b) ∏m = M_n via CLB or small-n witness, run C1."""
    Mn = m_n(n)
    # Sub-threshold just below M_n
    ms_list = enumerate_multisets(n, Mn)
    # pick ms with largest product
    ms_list_with_prod = [(int(np.prod(ms)), ms) for ms in ms_list]
    ms_list_with_prod.sort(reverse=True)
    result = {'n': n, 'M_n': Mn, 'sub_tests': [], 'at_test': None}
    for prod, ms in ms_list_with_prod[:3]:  # try top 3 sub-threshold
        cycles = enumerate_cycles(ms, n, L_max, 2.0, 1)
        if cycles:
            cyc, mov, det = cycles[0]
            r = {'class': 'sub', 'n': n, 'ms': list(ms),
                 'cycle': cyc, 'movers': mov, 'det': dict(det),
                 'L': len(cyc), 'product': prod}
            feas, supp, _, _, _ = c1_detector(r)
            result['sub_tests'].append({'ms': list(ms), 'product': prod,
                                        'L': len(cyc), 'feas': feas, 'supp': supp})
    # At-threshold: CLB for n≥5
    if n >= 5 and n <= 10:
        try:
            ms_at, fs, comp, cycle, movers = build_clb_witness_v2(n)
            if verify_system(ms_at, fs, verbose=False)['valid']:
                r = {'class': 'at_clb', 'n': n, 'ms': list(ms_at),
                     'cycle': [list(c) for c in cycle], 'movers': movers,
                     'det': dict(comp), 'L': len(cycle),
                     'product': int(np.prod(ms_at))}
                feas, supp, _, _, _ = c1_detector(r)
                result['at_test'] = {'ms': list(ms_at),
                                     'product': int(np.prod(ms_at)),
                                     'L': len(cycle), 'feas': feas, 'supp': supp}
        except Exception as e:
            result['at_test'] = {'error': str(e)}
    return result


# ======================================================================
# Random-multiset probe
# ======================================================================

def random_multiset_test(n, n_samples, rng):
    Mn = m_n(n); results = []; attempted = 0; cycle_ok = 0
    ms_list = enumerate_multisets(n, Mn)
    if not ms_list: return {'n': n, 'attempts': 0, 'skipped': 'empty'}
    rng.shuffle(ms_list)
    for ms in ms_list[:n_samples]:
        attempted += 1
        cycles = enumerate_cycles(ms, n, {5:40,6:24,7:18,8:14,9:14,10:14}.get(n, 14), 1.5, 1)
        if not cycles: continue
        cycle_ok += 1
        cyc, mov, det = cycles[0]
        r = {'class':'sub','n':n,'ms':list(ms),'cycle':cyc,'movers':mov,
             'det':dict(det),'L':len(cyc),'product':int(np.prod(ms))}
        feas, supp, _, _, _ = c1_detector(r)
        results.append({'ms': list(ms), 'L': len(cyc), 'feas': feas, 'supp': supp,
                        'product': int(np.prod(ms))})
    return {'n': n, 'n_attempted': attempted, 'n_cycle_ok': cycle_ok,
            'results': results,
            'feas_rate': sum(1 for r in results if r['feas']) / max(1, len(results))}


# ======================================================================
# P5 — Forman-Ricci + Gauss-Bonnet (simplified on NG 1-skeleton)
# ======================================================================

def forman_ricci_1d(rec):
    """Simplified: compute Forman-Ricci of 1-cells (edges) in NG Hamming-1
    graph. For an edge e = (u, v), Ric_F(e) = (degree u + degree v) -
    (# 2-cells containing e). Sum should be ≈ -2*χ(1-skel)."""
    ms = rec['ms']; n = len(ms)
    cycle = [tuple(c) for c in rec['cycle']]
    cycle_set = set(cycle)
    V = [c for c in iproduct(*[range(m) for m in ms]) if c not in cycle_set]
    idx = {c: i for i, c in enumerate(V)}
    # Hamming-1 edges among non-good configs
    adj = defaultdict(list)
    E = []
    for c in V:
        i = idx[c]
        for p in range(n):
            for v in range(ms[p]):
                if v == c[p]: continue
                nc = list(c); nc[p] = v; nc = tuple(nc)
                if nc in idx and idx[nc] > i:
                    adj[i].append(idx[nc]); adj[idx[nc]].append(i)
                    E.append((i, idx[nc], p))
    # Forman-Ricci: for an edge e in coord p_e, Ric_F(e) = 2 - (#squares through e)
    # - (#triangles). We approximate with: Ric_F(e) = deg(u) + deg(v) - 2*(common_neighbors)
    # Scale: sum(Ric_F) relates to χ.
    ric = []
    for u, v, p_e in E:
        du = len(adj[u]); dv = len(adj[v])
        # common neighbors count ≈ # 2-cells through e in 1-sk
        common = len(set(adj[u]) & set(adj[v]))
        r = (du + dv) - 2 * common
        ric.append(r)
    return {
        'n_V': len(V), 'n_E': len(E),
        'ric_mean': float(np.mean(ric)) if ric else 0.0,
        'ric_min': int(np.min(ric)) if ric else 0,
        'ric_max': int(np.max(ric)) if ric else 0,
        'ric_sum': int(np.sum(ric)) if ric else 0,
    }


# ======================================================================
# Tropical LP
# ======================================================================

def tropical_min_cycle_mean(rec):
    """Tropical eigenvalue of weighted directed graph (forced-NG): min
    cycle mean. Use Karp's algorithm O(|V|*|E|)."""
    V, E = build_lifted_graph(rec)
    nV = len(V)
    if nV == 0 or not E: return {'tropical_eval': None}
    # adjacency with weight = 1 (uniform edge weight)
    succ = defaultdict(list)
    for s, t, _ in E:
        succ[s].append((t, 1))
    # Karp's algorithm: d_k(v) = min cost of path of length k from some source to v.
    # Pick an arbitrary source s0. If not all v reachable, max over sources.
    # For efficiency: pick source = 0
    best_mean = float('inf')
    for source in range(min(3, nV)):  # test a few sources
        d = [[float('inf')] * nV for _ in range(nV + 1)]
        d[0][source] = 0
        for k in range(nV):
            for u in range(nV):
                if d[k][u] == float('inf'): continue
                for v, w in succ[u]:
                    if d[k+1][v] > d[k][u] + w:
                        d[k+1][v] = d[k][u] + w
        for v in range(nV):
            if d[nV][v] == float('inf'): continue
            mx = max((d[nV][v] - d[k][v]) / (nV - k) for k in range(nV)
                     if d[k][v] != float('inf'))
            if mx < best_mean: best_mean = mx
    if best_mean == float('inf'): best_mean = None
    return {'tropical_eval': best_mean, 'nV': nV, 'nE': len(E)}


# ======================================================================
# Main
# ======================================================================

def main():
    print("=" * 72)
    print("Wave 5 terminal probe queue")
    print("=" * 72)
    t0 = time.time()

    # Build corpus (sub 19 + CLB at 6 + small-n at 4)
    print("\n--- Corpus ---")
    sub_corpus = []
    L_max = {5:40, 6:24, 7:18}
    for nn in (5, 6, 7):
        Mn = m_n(nn)
        ms_list = enumerate_multisets(nn, Mn)
        stride = max(1, len(ms_list) // 9)
        for ms in ms_list[::stride][:8]:
            cyc = enumerate_cycles(ms, nn, L_max[nn], 2.0, 1)
            for c, mov, det in cyc:
                sub_corpus.append({'class':'sub','n':nn,'ms':list(ms),
                    'cycle':c,'movers':mov,'det':dict(det),
                    'L':len(c),'product':int(np.prod(ms))})
    print(f"  sub corpus: {len(sub_corpus)} records")

    at_corpus = []
    for n in range(5, 11):
        try:
            ms,fs,comp,cyc,mov = build_clb_witness_v2(n)
            if verify_system(ms, fs, verbose=False)['valid']:
                at_corpus.append({'class':'at_clb','n':n,'ms':list(ms),
                    'cycle':[list(c) for c in cyc],'movers':mov,
                    'det':dict(comp),'L':len(cyc),'product':int(np.prod(ms))})
        except Exception: pass
    for name in ('witness_n5', 'witness_n6', 'witness_n7', 'witness_n8'):
        fn = getattr(vw, name, None)
        if fn is None: continue
        ms, rules = fn()
        r = build_smalln_record(name[-2:], ms, rules)
        if r: at_corpus.append(r)
    print(f"  at corpus: {len(at_corpus)} records "
          f"({sum(1 for r in at_corpus if r['class']=='at_clb')} CLB + "
          f"{sum(1 for r in at_corpus if r['class']=='at_smallN')} small-n)")

    all_records = sub_corpus + at_corpus

    # ---- P7 sheaf extension probe ----
    print("\n=== P7 sheaf H¹ (simplified extension probe) ===")
    p7_records = []
    for r in all_records:
        res = probe_p7_extension(r)
        p7_records.append({'class': r['class'], 'n': r['n'], 'ms': r['ms'],
                           'L': r['L'], **res})
    # Check: do sub-threshold records fail stay-completion for
    # non-convergence reasons (→ H¹ signal) or just for convergence
    # (→ tautological)?
    sub_failures = [r for r in p7_records if r['class']=='sub' and not r['stay_completion_valid']]
    sub_fail_props = Counter()
    for r in sub_failures:
        for p in r['failed_props']: sub_fail_props[p] += 1
    at_failures = [r for r in p7_records if r['class'].startswith('at') and not r['stay_completion_valid']]
    print(f"  sub stay-completion: {len(p7_records)-len(sub_failures)}/"
          f"{sum(1 for r in p7_records if r['class']=='sub')} valid")
    print(f"  at stay-completion:  {sum(1 for r in p7_records if r['class'].startswith('at') and r['stay_completion_valid'])}/"
          f"{sum(1 for r in p7_records if r['class'].startswith('at'))} valid")
    print(f"  sub failed-properties histogram: {dict(sub_fail_props)}")
    # at failures:
    at_fail_props = Counter()
    for r in at_failures:
        for p in r['failed_props']: at_fail_props[p] += 1
    print(f"  at failed-properties histogram: {dict(at_fail_props)}")

    # ---- P1.5 subclass characterization ----
    print("\n=== P1.5 zero-residual subclass ===")
    # Analyze sub records, compute direction-covariant residual
    sub_analyzed = []
    for r in sub_corpus:
        V, E = build_lifted_graph(r)
        lp = solve_lp(len(V), E)
        a = {'class':'sub','n':r['n'],'ms':r['ms'],'L':r['L'],
             'feasible':lp['feasible'],'phi':lp['phi'],
             '_E_lift':E}
        if lp['feasible']:
            resid = direction_covariant_residual(a)
            a['dc_residual'] = resid
        sub_analyzed.append(a)
    feas_sub = [a for a in sub_analyzed if a.get('feasible')]
    zero_resid = [a for a in feas_sub if a.get('dc_residual', 0) < 1e-6]
    nonzero_resid = [a for a in feas_sub if a.get('dc_residual', 0) >= 1e-6]
    print(f"  feasible sub: {len(feas_sub)}, zero-residual: {len(zero_resid)}, "
          f"nonzero-residual: {len(nonzero_resid)}")
    # Characterize: features of zero vs nonzero
    print("  zero-residual ms:")
    for a in zero_resid:
        f = subclass_features({'ms':a['ms'],'n':a['n']})
        print(f"    ms={a['ms']} has_33={f['has_consec_ternary']} "
              f"longest_ter_run={f['longest_ter_run']} n_ter={f['n_ter']}")
    print("  nonzero-residual ms:")
    for a in nonzero_resid:
        f = subclass_features({'ms':a['ms'],'n':a['n']})
        print(f"    ms={a['ms']} has_33={f['has_consec_ternary']} "
              f"longest_ter_run={f['longest_ter_run']} n_ter={f['n_ter']} "
              f"resid={a['dc_residual']:.3f}")
    # Test separator: has_consec_ternary predicts nonzero?
    err1 = 0
    for a in feas_sub:
        f = subclass_features({'ms':a['ms'],'n':a['n']})
        pred_nonzero = f['has_consec_ternary']
        actual_nonzero = a.get('dc_residual', 0) >= 1e-6
        if pred_nonzero != actual_nonzero: err1 += 1
    print(f"  has_consec_ternary predicts nonzero: {len(feas_sub)-err1}/{len(feas_sub)} acc")
    # Alternative: longest_ter_run >= 2
    err2 = 0
    for a in feas_sub:
        f = subclass_features({'ms':a['ms'],'n':a['n']})
        pred_nonzero = f['longest_ter_run'] >= 2
        actual_nonzero = a.get('dc_residual', 0) >= 1e-6
        if pred_nonzero != actual_nonzero: err2 += 1
    print(f"  longest_ter_run >= 2 predicts nonzero: {len(feas_sub)-err2}/{len(feas_sub)} acc")

    # ---- Sharpness probe ----
    print("\n=== Sharpness probe ===")
    sharp = []
    for n in (5, 6, 7):
        r = sharpness_test(n, L_max.get(n, 14))
        sharp.append(r)
        sub_str = ', '.join(f"p={s['product']} feas={s['feas']}" for s in r['sub_tests'])
        at_str = (f"p={r['at_test']['product']} feas={r['at_test']['feas']}"
                  if r['at_test'] and 'feas' in r['at_test'] else 'none')
        print(f"  n={n}: M_n={r['M_n']} | sub[{sub_str}] | at[{at_str}]")

    # ---- Random multiset probe ----
    print("\n=== Random multiset probe ===")
    rng = random.Random(42)
    rand_tests = []
    for n in (5, 6, 7):
        rt = random_multiset_test(n, 5, rng)
        rand_tests.append(rt)
        if 'feas_rate' in rt:
            print(f"  n={n}: attempted={rt['n_attempted']} cycle_ok={rt['n_cycle_ok']} "
                  f"feas_rate={rt['feas_rate']:.2f}")

    # ---- P5 Forman-Ricci ----
    print("\n=== P5 Forman-Ricci ===")
    fr_stats = {'sub': [], 'at': []}
    for r in sub_corpus[:8]:  # sample to save time
        try:
            fr = forman_ricci_1d(r)
            fr_stats['sub'].append({'ms':r['ms'],'L':r['L'],**fr})
        except Exception as e:
            pass
    for r in at_corpus[:5]:
        try:
            fr = forman_ricci_1d(r)
            fr_stats['at'].append({'ms':r['ms'],'L':r['L'],**fr})
        except Exception as e:
            pass
    sub_ric = [s['ric_mean'] for s in fr_stats['sub']]
    at_ric = [s['ric_mean'] for s in fr_stats['at']]
    print(f"  sub Ric_F mean: {np.mean(sub_ric) if sub_ric else None}")
    print(f"   at Ric_F mean: {np.mean(at_ric) if at_ric else None}")

    # ---- Tropical ----
    print("\n=== Tropical LP (min cycle mean on forced-NG lifted graph) ===")
    trop_stats = {'sub': [], 'at': []}
    for r in (sub_corpus + at_corpus):
        try:
            t = tropical_min_cycle_mean(r)
            trop_stats[r['class'][:3] if r['class'].startswith('at') else r['class']].append(t)
        except Exception:
            pass
    sub_eval = [t['tropical_eval'] for t in trop_stats.get('sub', []) if t['tropical_eval'] is not None]
    at_eval = [t['tropical_eval'] for t in trop_stats.get('at', []) if t['tropical_eval'] is not None]
    print(f"  sub tropical eval (min cycle mean): {sub_eval}")
    print(f"   at tropical eval (min cycle mean): {at_eval}")

    # ---- Write results ----
    payload = {
        'p7_extension': p7_records,
        'p15_subclass': {
            'zero_resid_ms': [list(a['ms']) for a in zero_resid],
            'nonzero_resid': [{'ms':list(a['ms']), 'resid':a.get('dc_residual')}
                              for a in nonzero_resid],
            'acc_has_consec_ternary': 1.0 - err1/max(1,len(feas_sub)),
            'acc_longest_ter_run_ge2': 1.0 - err2/max(1,len(feas_sub)),
        },
        'sharpness': sharp,
        'random_multiset': rand_tests,
        'forman_ricci': fr_stats,
        'tropical': {
            'sub_eval': [float(x) for x in sub_eval],
            'at_eval': [float(x) for x in at_eval],
        },
        'runtime_s': round(time.time() - t0, 1),
    }
    out_path = os.path.join(HERE, "phaseW5_results.json")
    try:
        with open(out_path, "w") as f:
            json.dump(payload, f, indent=2, default=str)
        print(f"\nWrote {out_path} ({time.time()-t0:.1f}s)")
    except Exception as e:
        print(f"Write failed: {e}")


if __name__ == "__main__":
    main()
