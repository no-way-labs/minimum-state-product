#!/usr/bin/env python3
"""Wave 2 C1 — lifted-defect circulation LP probe.

Builds verified at-threshold corpus (Priority 0.5) + sub-threshold corpus,
then for each record:
  1. Build V_lift = {(k, q, a) : k in Fin L, q in Fin n, a in Fin m_q,
     a != c_k(q), c_k[q:=a] in T_N1}
  2. Build E_lift = forced edges lifted per Wave 2 §2.2 (transport +
     twist + other).
  3. Solve LP:  min 0  s.t.  B^T Φ = 0, Φ >= 0, 1^T Φ >= 1.
  4. Report feasibility, |supp Φ|, support edge-type histogram,
     composition class, cyclic-time-shift stabilizer.

Pre-commit kill criteria (Wave 2 §2.4 + addendum §2.3 + §3.3):
  - RED if sub-threshold infeasible anywhere
  - RED if at-threshold feasible anywhere (verified corpus)
  - RED if high-entropy support (>O(n) edge types)
  - RED if feasibility confined to pure-binary only
  - RED if supp Φ invariant under cycle-time shift on >80% of records

Corpus sources:
  S1  (skipped — no stored sharp small-n witnesses)
  S2  CLB-generalized ternary-strip witnesses for n in {5..10},
      ms=(2,3,...,3,2). Verified via verify_system.
  S3  (Sol3v1-shape, used if CLB misses a needed n).
  SUB enumerate_all_cycles on sub-threshold multisets, as Phase A.

Outputs
  phaseC1_results.json next to this file.
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
# CLB-generalized witness construction (generalizes clb_witness_8748 to n>=5)
# ======================================================================

def build_clb_witness(n: int):
    """Generalize clb_witness_8748.build_system() to arbitrary n>=5.
    Returns (ms, fs, comp, good_cycle, movers)."""
    ms = (2,) + (3,) * (n - 2) + (2,)
    # Bounce: up 0..n-1 then down n-2..1, repeat until closed
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
        c = cycle[idx]
        c_next = cycle[(idx + 1) % L]
        mv = movers[idx]
        for p in range(n):
            Lv = c[(p - 1) % n]; Sv = c[p]; Rv = c[(p + 1) % n]
            key = (p, Lv, Sv, Rv)
            if p == mv:
                det[key] = c_next[p]
            else:
                det[key] = Sv

    free_entries = []
    for p in range(n):
        mL = ms[(p - 1) % n]; mS = ms[p]; mR = ms[(p + 1) % n]
        for Lv in range(mL):
            for Sv in range(mS):
                for Rv in range(mR):
                    key = (p, Lv, Sv, Rv)
                    if key not in det:
                        free_entries.append(key)

    # good-targeting completion
    comp = dict(det)
    for key in free_entries:
        p, Lv, Sv, Rv = key
        best_out = Sv; best_good = 0; best_ng = float('inf')
        for out in range(ms[p]):
            ng = 0; good_count = 0
            if out != Sv:
                for c in non_good:
                    if c[(p-1)%n]==Lv and c[p]==Sv and c[(p+1)%n]==Rv:
                        nc = tuple(c[j] if j != p else out for j in range(n))
                        if nc in good_set: good_count += 1
                        elif nc in non_good_set: ng += 1
            if good_count > best_good or (good_count == best_good and ng < best_ng):
                best_out = out; best_good = good_count; best_ng = ng
        comp[key] = best_out

    # liveness fix
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
                            cost = 0  # skip deep cost for speed
                            if cost < best_cost:
                                best_cost = cost; best_key = key; best_out_val = out
            if best_key:
                comp[best_key] = best_out_val

    def make_f(p_idx):
        def f(L, S, R):
            return comp.get((p_idx, L, S, R), S)
        return f
    fs = [make_f(p) for p in range(n)]
    return list(ms), fs, comp, cycle, movers


def verify_at_threshold_record(n):
    """Build + verify an at-threshold witness at dimension n. For n=9
    use the known-good imported `clb_witness_8748.build_system`; for
    other n use the in-file generalization (which may fail verification
    due to liveness-fix edge-cost shortcut)."""
    if n == 9:
        try:
            from clb_witness_8748 import build_system as clb_build
        except Exception as e:
            return {'n': n, 'error': f'import clb_witness_8748 failed: {e}'}
        ms, fs, comp = clb_build()
        # reconstruct cycle+movers by re-running bounce closure
        up_down = list(range(n)) + list(range(n - 2, 0, -1))
        config = [0] * n
        cycle = [tuple(config)]
        movers = []
        for step, mover in enumerate(up_down * 5):
            config = list(cycle[-1]); config[mover] = (config[mover] + 1) % ms[mover]
            nc = tuple(config); movers.append(mover)
            if nc == cycle[0]:
                break
            cycle.append(nc)
        movers = movers[:len(cycle)]
        v = verify_system(ms, fs, verbose=False)
        return {
            'class': 'at', 'n': n, 'ms': list(ms),
            'cycle': [list(c) for c in cycle],
            'movers': movers, 'det': dict(comp),
            'L': len(cycle),
            'verify_valid': v['valid'],
            'verify_props': {k: ok for k, (ok, _) in v['properties'].items()},
            'product': int(np.prod(ms)),
        }
    try:
        ms, fs, comp, cycle, movers = build_clb_witness(n)
    except Exception as e:
        return {'n': n, 'error': str(e)}
    v = verify_system(ms, fs, verbose=False)
    return {
        'class': 'at', 'n': n, 'ms': list(ms),
        'cycle': [list(c) for c in cycle],
        'movers': movers, 'det': dict(comp),
        'L': len(cycle),
        'verify_valid': v['valid'],
        'verify_props': {k: ok for k, (ok, _) in v['properties'].items()},
        'product': int(np.prod(ms)),
    }


# ======================================================================
# Sub-threshold corpus (from Phase A shared plumbing)
# ======================================================================

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


def m_n(n):
    return 32 * 3 ** (n - 4) if 5 <= n <= 8 else 4 * 3 ** (n - 2)


def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen_cycles = set()
    t0 = time.time()
    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)):
                return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max:
            return
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


def get_sub_threshold_records(n_list=(5, 6, 7), per_n=6, L_max_by_n=None,
                              time_budget=3.0):
    if L_max_by_n is None:
        L_max_by_n = {5: 40, 6: 24, 7: 18}
    records = []
    for n in n_list:
        Mn = m_n(n)
        multisets = enumerate_multisets(n, Mn)
        stride = max(1, len(multisets) // (per_n + 1))
        sample = multisets[::stride][:per_n]
        for ms in sample:
            cycles = enumerate_all_cycles(ms, n, L_max_by_n[n], time_budget, 1)
            for cycle, movers, det in cycles:
                records.append({
                    'class': 'sub', 'n': n, 'ms': list(ms),
                    'cycle': cycle, 'movers': movers, 'det': dict(det),
                    'L': len(cycle),
                    'product': int(np.prod(ms)),
                })
    return records


# ======================================================================
# Lifted graph + LP
# ======================================================================

def classify_composition(ms):
    """Per addendum §2.2. Returns class 1..5."""
    n = len(ms)
    n_bin = sum(1 for m in ms if m == 2)
    if n_bin == n:
        return 1  # pure binary
    if (n >= 3 and ms[0] == 2 and ms[-1] == 2
        and all(m == 3 for m in ms[1:-1])):
        return 3  # endpoint-binary ternary-strip
    if n_bin == 3 and any(m == 4 for m in ms) and sum(1 for m in ms if m == 3) == n - 4:
        return 4  # {2^3, 4, 3^(n-4)}
    if n_bin >= 3:
        return 2  # binary-dominated
    return 5  # other


def value_set_tube(cycle, n):
    """V_q = set of values c_k(q) attained in the cycle."""
    V = [set() for _ in range(n)]
    for c in cycle:
        for q in range(n):
            V[q].add(c[q])
    return [sorted(s) for s in V]


def build_lifted_graph(rec):
    """Build (V_lift, E_lift, type_of_edge, cycle_configs).
    E_lift entries are (src_idx, dst_idx, edge_type).
    edge_type in {'transport', 'c_self', 'c_left', 'c_right', 'other'}.
    """
    ms = rec['ms']
    n = len(ms)
    cycle = [tuple(c) for c in rec['cycle']]
    movers = rec['movers']
    L = len(cycle)
    det = rec['det']
    cycle_set = set(cycle)
    V_tube = value_set_tube(cycle, n)

    move_entries = {k: v for k, v in det.items() if v != k[2]}

    # V_lift vertices
    V_lift = []
    idx_of = {}
    tube_configs = {}  # (k,q,a) -> config c_k[q:=a]
    for k in range(L):
        c_k = cycle[k]
        for q in range(n):
            for a in V_tube[q]:
                if a == c_k[q]:
                    continue
                nc = list(c_k); nc[q] = a; nc = tuple(nc)
                if nc in cycle_set:
                    continue
                # value-consistent within V_tube (automatic by construction)
                # non-good: check by detOf? Here NG = not in cycle.
                key = (k, q, a)
                idx_of[key] = len(V_lift)
                V_lift.append(key)
                tube_configs[key] = nc

    # E_lift edges: emit ALL forced-move edges at c = c_k[q:=a] (one per
    # firing position where the triple has val != S)
    E_lift = []
    for src_v in V_lift:
        k, q, a = src_v
        c = tube_configs[src_v]
        mov_k = movers[k] if k < len(movers) else None
        adj_q = {(q-1) % n, q, (q+1) % n}
        for p_fire in range(n):
            ctx = (p_fire, c[(p_fire-1)%n], c[p_fire], c[(p_fire+1)%n])
            v_new = move_entries.get(ctx)
            if v_new is None or v_new == c[p_fire]:
                continue
            c_succ = list(c); c_succ[p_fire] = v_new; c_succ = tuple(c_succ)
            # Classify edge type
            if p_fire == mov_k and p_fire not in adj_q:
                edge_type = 'transport'
            elif p_fire == q:
                edge_type = 'c_self'
            elif p_fire == (q - 1) % n:
                edge_type = 'c_left'
            elif p_fire == (q + 1) % n:
                edge_type = 'c_right'
            else:
                edge_type = 'other'
            # Find a lift of c_succ
            tgt_v = None
            if edge_type == 'transport':
                cand = ((k+1) % L, q, a)
                if cand in idx_of:
                    tgt_v = cand
            if tgt_v is None:
                if c_succ in cycle_set:
                    continue  # exits tube into cycle
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

    return V_lift, E_lift, tube_configs


def solve_circulation_lp(V_lift, E_lift):
    """Solve:  max sum(Φ)  s.t.  B^T Φ = 0,  Φ >= 0,  1^T Φ >= 1.
    Equivalent formulation: min -1^T Φ with equality B^T Φ = 0 and Φ in [0,1].
    If optimum < 0 (slightly negative or at -∞), feasible. If optimum = 0,
    infeasible (no nonzero circulation)."""
    nV = len(V_lift); nE = len(E_lift)
    if nE == 0:
        return {'feasible': False, 'supp_size': 0, 'support': []}
    # Build incidence: row v, col e, entry = +1 if edge starts at v, -1 if ends.
    # We want B^T Φ = 0 means for each vertex, in - out = 0.
    # Equivalent: for each vertex v, sum_{e out of v} Φ_e - sum_{e into v} Φ_e = 0
    Aeq = np.zeros((nV, nE))
    for e_idx, (s, t, _) in enumerate(E_lift):
        Aeq[s, e_idx] -= 1  # out
        Aeq[t, e_idx] += 1  # in
    beq = np.zeros(nV)
    # objective: maximize sum Φ, bounded by box [0, 1]
    c = -np.ones(nE)
    bounds = [(0.0, 1.0)] * nE
    res = linprog(c, A_eq=Aeq, b_eq=beq, bounds=bounds, method='highs',
                  options={'disp': False})
    if not res.success:
        return {'feasible': False, 'supp_size': 0, 'support': [],
                'lp_status': res.status, 'lp_message': res.message}
    x = res.x
    # "feasible" for our probe means a nonzero circulation exists
    # objective = -sum Φ. If objective < -1e-9 we have Φ supporting a cycle.
    obj = float(res.fun)
    supp_mask = x > 1e-6
    supp_idx = [i for i in range(nE) if supp_mask[i]]
    return {
        'feasible': obj < -1e-9,
        'supp_size': len(supp_idx),
        'support': supp_idx,
        'objective': obj,
        'max_phi': float(np.max(x)) if nE > 0 else 0.0,
    }


def cyclic_time_shift_stabilizer(V_lift, E_lift, support, L):
    """Compute order of stabilizer of support under cycle-time shift
    (k,q,a) -> (k+s, q, a). Returns int in 1..L."""
    if not support:
        return L
    supp_set = set()
    for e_idx in support:
        s, t, _ = E_lift[e_idx]
        vs = V_lift[s]; vt = V_lift[t]
        supp_set.add(('src', vs)); supp_set.add(('dst', vt))
    stab = 0
    for s in range(L):
        shifted = set()
        for (tag, (k, q, a)) in supp_set:
            shifted.add((tag, ((k + s) % L, q, a)))
        if shifted == supp_set:
            stab += 1
    return stab


# ======================================================================
# Driver
# ======================================================================

def analyze_record(rec):
    t0 = time.time()
    V_lift, E_lift, _ = build_lifted_graph(rec)
    build_t = time.time() - t0
    etype_count = Counter(etype for _, _, etype in E_lift)
    t1 = time.time()
    lp = solve_circulation_lp(V_lift, E_lift)
    lp_t = time.time() - t1
    support = lp.get('support', [])
    supp_etypes = Counter(E_lift[i][2] for i in support) if support else Counter()
    stab = cyclic_time_shift_stabilizer(V_lift, E_lift, support, rec['L'])
    ms = rec['ms']; n = len(ms); L = rec['L']; product = int(np.prod(ms))
    coverage = L / (n * product)
    return {
        'class': rec['class'], 'n': n, 'ms': list(ms), 'L': L,
        'product': product,
        'composition_class': classify_composition(ms),
        'coverage': coverage,
        'nV_lift': len(V_lift), 'nE_lift': len(E_lift),
        'edge_type_hist': dict(etype_count),
        'feasible': lp.get('feasible', False),
        'supp_size': lp.get('supp_size', 0),
        'supp_edge_type_hist': dict(supp_etypes),
        'objective': lp.get('objective'),
        'stab_time_shift': stab,
        'stab_ratio': stab / max(L, 1),
        'build_t_s': round(build_t, 2), 'lp_t_s': round(lp_t, 2),
    }


def main():
    print("=" * 72)
    print("Wave 2 C1: lifted-defect circulation LP probe")
    print("=" * 72)

    # --------- Corpus: at-threshold verified ---------
    print("\n--- Priority 0.5: at-threshold CLB witness verification ---")
    at_records = []
    at_verify_report = []
    for n in (5, 6, 7, 8, 9):
        print(f"  building CLB witness at n={n}...", end=" ", flush=True)
        t0 = time.time()
        r = verify_at_threshold_record(n)
        dt = time.time() - t0
        if 'error' in r:
            print(f"ERROR {r['error']} ({dt:.1f}s)")
            at_verify_report.append({'n': n, 'status': 'error', 'msg': r['error']})
            continue
        print(f"valid={r['verify_valid']} product={r['product']} L={r['L']} ({dt:.1f}s)")
        at_verify_report.append({
            'n': n, 'status': 'valid' if r['verify_valid'] else 'invalid',
            'props': r['verify_props'], 'product': r['product'], 'L': r['L'],
        })
        if r['verify_valid']:
            at_records.append(r)

    print(f"  -> {len(at_records)} verified at-threshold records")

    # --------- Corpus: sub-threshold ---------
    print("\n--- Sub-threshold corpus (enumerated) ---")
    sub_records = get_sub_threshold_records(n_list=(5, 6, 7), per_n=6,
                                            time_budget=2.0)
    print(f"  -> {len(sub_records)} sub-threshold records")

    all_records = at_records + sub_records

    # --------- Run C1 on each ---------
    print(f"\n--- Running C1 on {len(all_records)} records ---")
    out_recs = []
    t_global = time.time()
    for i, r in enumerate(all_records):
        print(f"\n[{i+1}/{len(all_records)}] {r['class']} n={r['n']} "
              f"ms={r['ms']} L={r['L']} prod={r['product']}", flush=True)
        try:
            o = analyze_record(r)
            out_recs.append(o)
            print(f"  comp_class={o['composition_class']} "
                  f"V={o['nV_lift']} E={o['nE_lift']} "
                  f"types={o['edge_type_hist']}")
            print(f"  LP feasible={o['feasible']} "
                  f"supp={o['supp_size']} supp_types={o['supp_edge_type_hist']} "
                  f"stab={o['stab_time_shift']}/{r['L']} "
                  f"cov={o['coverage']:.4f}")
        except Exception as e:
            import traceback; traceback.print_exc()
            out_recs.append({'class': r['class'], 'n': r['n'],
                             'ms': r['ms'], 'error': str(e)})

    # --------- Breakouts and verdicts ---------
    print("\n" + "=" * 72)
    print("VERDICTS")
    print("=" * 72)

    sub = [r for r in out_recs if r.get('class') == 'sub' and 'feasible' in r]
    at = [r for r in out_recs if r.get('class') == 'at' and 'feasible' in r]

    sub_feas = sum(1 for r in sub if r['feasible'])
    at_feas = sum(1 for r in at if r['feasible'])
    print(f"\nOverall feasibility:")
    print(f"  sub:  {sub_feas}/{len(sub)} feasible")
    print(f"   at: {at_feas}/{len(at)} feasible")

    # 5-class breakout
    print("\nComposition-class breakout (feasible / total):")
    print(f"  {'class':<6}{'sub feas':<14}{'at feas':<14}")
    for cc in (1, 2, 3, 4, 5):
        sub_cc = [r for r in sub if r['composition_class'] == cc]
        at_cc = [r for r in at if r['composition_class'] == cc]
        sf = sum(1 for r in sub_cc if r['feasible'])
        af = sum(1 for r in at_cc if r['feasible'])
        name = {1: 'pure-bin', 2: 'bin-dom', 3: 'ternstrip', 4: 'abs{234}', 5: 'other'}[cc]
        print(f"  {cc} {name:<6}  {sf}/{len(sub_cc):<10}  {af}/{len(at_cc)}")

    # coverage correlation
    if sub and at:
        all_r = sub + at
        cov = np.array([r['coverage'] for r in all_r])
        feas = np.array([1.0 if r['feasible'] else 0.0 for r in all_r])
        if np.std(feas) > 0 and np.std(cov) > 0:
            cor = float(np.corrcoef(cov, feas)[0, 1])
        else:
            cor = 0.0
        print(f"\nCoverage correlation cor(coverage, feasible) = {cor:.3f}")
    else:
        cor = None

    # cyclic-time-shift stabilizer
    sub_stab = [r['stab_ratio'] for r in sub]
    at_stab = [r['stab_ratio'] for r in at]
    print(f"\nCycle-time-shift stabilizer ratio (1.0 = full invariance):")
    if sub_stab:
        print(f"  sub mean={np.mean(sub_stab):.3f} max={max(sub_stab):.3f}")
    else:
        print("  sub: no data")
    if at_stab:
        print(f"   at mean={np.mean(at_stab):.3f} max={max(at_stab):.3f}")
    else:
        print("   at: no data")
    # Invariance only meaningful for feasible records (infeasible → empty supp → trivial L)
    sub_feas_rec = [r for r in sub if r['feasible']]
    sub_feas_stab = [r['stab_ratio'] for r in sub_feas_rec]
    if sub_feas_stab:
        print(f"  sub (feasible only): mean={np.mean(sub_feas_stab):.3f} "
              f"min={min(sub_feas_stab):.3f} max={max(sub_feas_stab):.3f}")

    # Verdict logic (Wave 2 §2.4 + addendum §2.3 + §3.3)
    verdicts = []
    if any(not r['feasible'] for r in sub):
        verdicts.append(("RED", "sub-threshold infeasible somewhere: "
                        f"{sum(1 for r in sub if not r['feasible'])}/"
                        f"{len(sub)} infeasible"))
    if any(r['feasible'] for r in at):
        verdicts.append(("RED", f"at-threshold feasible somewhere: "
                        f"{sum(1 for r in at if r['feasible'])}/"
                        f"{len(at)} feasible on verified corpus"))
    # composition-class confound
    pure_bin_sub_feas = sum(1 for r in sub
                             if r['composition_class'] == 1 and r['feasible'])
    nonpure_sub_feas = sum(1 for r in sub
                            if r['composition_class'] != 1 and r['feasible'])
    nonpure_sub_total = sum(1 for r in sub if r['composition_class'] != 1)
    if pure_bin_sub_feas > 0 and nonpure_sub_total > 0 and nonpure_sub_feas == 0:
        verdicts.append(("RED", "feasibility confined to pure-binary subclass — "
                        "composition confound (addendum §2.3)"))
    # coverage
    if cor is not None and abs(cor) > 0.3:
        verdicts.append(("YELLOW-caveat", f"feasibility correlates with coverage "
                        f"(|cor|={abs(cor):.2f} > 0.3) — residualize"))
    # cyclic-time-shift
    inv_records_sub = sum(1 for r in sub if r['stab_ratio'] > 0.99)
    if sub and inv_records_sub / len(sub) > 0.8:
        verdicts.append(("RED", f"supp Φ invariant under cycle-time shift on "
                        f"{inv_records_sub}/{len(sub)} sub records "
                        f"— P2-style circulant collapse one level up (addendum §3.3)"))
    if not verdicts:
        if sub_feas == len(sub) and at_feas == 0:
            verdicts.append(("YELLOW", "feasibility rates pass pre-commit; no confound detected on this corpus"))
        else:
            verdicts.append(("AMBIGUOUS", "no kill tripwire fired but SURVIVES condition not met"))

    print("\n--- Pre-commit verdict(s) ---")
    for v, msg in verdicts:
        print(f"  {v}: {msg}")

    # Write outputs
    out_payload = {
        'at_verify_report': at_verify_report,
        'records': out_recs,
        'verdicts': verdicts,
        'correlation_coverage_feas': cor,
        'runtime_s': round(time.time() - t_global, 1),
    }
    out_path = os.path.join(HERE, "phaseC1_results.json")
    try:
        with open(out_path, "w") as f:
            json.dump(out_payload, f, indent=2, default=str)
        print(f"\nWrote {out_path}")
    except Exception as e:
        print(f"\nFailed to write {out_path}: {e}")
        print("--- JSON payload ---")
        print(json.dumps(out_payload, indent=2, default=str)[:5000])


if __name__ == "__main__":
    main()
