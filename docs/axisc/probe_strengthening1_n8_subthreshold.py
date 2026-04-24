#!/usr/bin/env python3
"""Strengthening task #1 — extend sub-threshold enumeration to n=8 (and n=9 Table 7).

Purpose: test whether the C1 circulation LP detector still separates on a
corpus that covers n=8 sub-threshold (product < B_8 = 2592) and ideally the
n=9 Table 7 multisets (product = 7776, sub-threshold for M_9 = 8748).

Pipeline mirrors Wave 3/4:
  1. enumerate unordered multisets with each m_i >= 2, prod < threshold,
  2. for each, try representative cyclic orderings until a candidate good
     cycle is found (up to a per-record time budget),
  3. feed each (ms, cycle, movers, det) into the lifted circulation LP,
  4. record feasibility + sufficient fields for downstream audit.

Outputs (in same directory as this script):
  - phase1_n8_sub_corpus.json   (raw per-record results)
  - phase1_n8_summary.md        (human-readable summary)

Expected (if detector holds): every n=8 sub-threshold record with a cycle
is LP-feasible; every at-threshold witness (w5-w8, CLB n=5..10) is
LP-infeasible. A single LP-infeasible n=8 sub-threshold record would be
the "first counterexample" called out in the strengthening doc.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from collections import Counter, defaultdict
from itertools import product as iproduct

import numpy as np
from scipy.optimize import linprog

HERE = os.path.dirname(os.path.abspath(__file__))
CLAUDE_DIR = os.path.abspath(os.path.join(HERE, "..", "..", "..", "claude"))
DOCS_DIR = os.path.abspath(os.path.join(HERE, "..", "..", "..", "docs"))
sys.path.insert(0, CLAUDE_DIR)
sys.path.insert(0, DOCS_DIR)

from verifier import verify_system  # type: ignore
import verify_witnesses as vw  # type: ignore


# ----------------------------------------------------------------------
# Composition / cycle enumeration  (ported from wave4 combined)
# ----------------------------------------------------------------------

def m_n(n: int) -> int:
    return 32 * 3 ** (n - 4) if 5 <= n <= 8 else 4 * 3 ** (n - 2)


def enumerate_compositions(n: int, max_product: int):
    """All ordered (m_0, ..., m_{n-1}) with each m_i >= 2 and prod < max_product."""
    out = []

    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product:
                out.append(tuple(prefix))
            return
        for m in range(2, max_product + 1):
            new_prod = prod * m
            min_rem = 2 ** (n - i - 1)
            if new_prod * min_rem >= max_product:
                break
            prefix.append(m)
            rec(i + 1, prefix, new_prod)
            prefix.pop()

    rec(0, [], 1)
    return out


def unordered_multisets(compositions):
    seen = set()
    out = []
    for ms in compositions:
        key = tuple(sorted(ms))
        if key not in seen:
            seen.add(key)
            out.append(key)
    return out


def canonical_orderings(sorted_ms):
    """Return one composition per (rotation, reflection) orbit."""
    from itertools import permutations
    n = len(sorted_ms)
    seen = set()
    reps = []
    for perm in set(permutations(sorted_ms)):
        # canonical = lex-min over rotations and reflections
        rots = [perm[i:] + perm[:i] for i in range(n)]
        refls = [tuple(reversed(r)) for r in rots]
        canon = min(rots + refls)
        if canon not in seen:
            seen.add(canon)
            reps.append(canon)
    return reps


def enumerate_cycles(ms, n, L_max, time_budget, max_cycles=1):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen = set()
    t0 = time.time()

    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)):
                return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen:
                seen.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max:
            return
        for p in range(n):
            Lp = config[(p - 1) % n]
            Sp = config[p]
            Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp)
            forced_out = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp:
                    continue
                if forced_out is not None and forced_out != new_val:
                    continue
                new_det = dict(det)
                new_det[km] = new_val
                ok = True
                for i in range(n):
                    if i == p:
                        continue
                    Li = config[(i - 1) % n]
                    Si = config[i]
                    Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si:
                        ok = False
                        break
                    new_det[ki] = Si
                if not ok:
                    continue
                nc = list(config)
                nc[p] = new_val
                nc = tuple(nc)
                if nc != start and nc in set(path):
                    continue
                dfs(start, nc, new_det, path + [nc], movers + [p])

    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            break
        dfs(start, start, {}, [start], [])
    return found


# ----------------------------------------------------------------------
# Lifted graph + circulation LP  (ported from wave4 combined)
# ----------------------------------------------------------------------

def classify_composition(ms):
    n = len(ms)
    n_bin = sum(1 for m in ms if m == 2)
    if n_bin == n:
        return 1
    if n >= 3 and ms[0] == 2 and ms[-1] == 2 and all(m == 3 for m in ms[1:-1]):
        return 3
    if n_bin == 3 and any(m == 4 for m in ms) and sum(1 for m in ms if m == 3) == n - 4:
        return 4
    if n_bin >= 3:
        return 2
    return 5


def value_set_tube(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for q in range(n):
            V[q].add(c[q])
    return [sorted(s) for s in V]


def build_lifted_graph(rec):
    ms = rec['ms']
    n = len(ms)
    cycle = [tuple(c) for c in rec['cycle']]
    movers = rec['movers']
    L = len(cycle)
    det = rec['det']
    cycle_set = set(cycle)
    V_tube = value_set_tube(cycle, n)
    move_entries = {k: v for k, v in det.items() if v != k[2]}

    V_lift = []
    idx_of = {}
    tube_configs = {}
    for k in range(L):
        c_k = cycle[k]
        for q in range(n):
            for a in V_tube[q]:
                if a == c_k[q]:
                    continue
                nc = list(c_k)
                nc[q] = a
                nc = tuple(nc)
                if nc in cycle_set:
                    continue
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
            if v_new is None or v_new == c[p_fire]:
                continue
            c_succ = list(c)
            c_succ[p_fire] = v_new
            c_succ = tuple(c_succ)
            if p_fire == mov_k and p_fire not in adj_q:
                edge_type = 'transport'
            elif p_fire == q:
                edge_type = 'c_self'
            elif p_fire == (q - 1) % n:
                edge_type = 'c_left'
            elif p_fire == (q + 1) % n:
                edge_type = 'c_right'
            else:
                rel_mov = (mov_k - q) % n if mov_k is not None else None
                rel_fire = (p_fire - q) % n
                other_patterns[(rel_mov, rel_fire)] += 1
                edge_type = f'other[rel_mov={rel_mov},rel_fire={rel_fire}]'
            tgt_v = None
            if edge_type == 'transport':
                cand = ((k + 1) % L, q, a)
                if cand in idx_of:
                    tgt_v = cand
            if tgt_v is None:
                if c_succ in cycle_set:
                    continue
                for kk in range(L):
                    c_kk = cycle[kk]
                    diff = [(i, c_succ[i]) for i in range(n) if c_succ[i] != c_kk[i]]
                    if len(diff) == 1:
                        qq, aa = diff[0]
                        cand = (kk, qq, aa)
                        if cand in idx_of:
                            tgt_v = cand
                            break
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
        Aeq[s, e_idx] -= 1
        Aeq[t, e_idx] += 1
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
        'supp_size': len(supp),
        'support': supp,
        'phi': x.tolist(),
        'objective': obj,
    }


def analyze_record(rec):
    V_lift, E_lift, other_patterns = build_lifted_graph(rec)
    lp = solve_circulation_lp(len(V_lift), E_lift)
    support = lp.get('support', [])
    etype_total = Counter(e[2].split('[')[0] for e in E_lift)
    supp_types = (
        Counter(E_lift[i][2].split('[')[0] for i in support)
        if support else Counter()
    )
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
        'other_patterns': {f'{k}': v for k, v in other_patterns.items()},
    }


# ----------------------------------------------------------------------
# Corpus builders
# ----------------------------------------------------------------------

def find_cycle_for_multiset(sorted_ms, n, L_max, per_ordering_budget, max_orderings):
    """Try canonical orderings until we find at least one fair good cycle."""
    reps = canonical_orderings(sorted_ms)
    tried = 0
    for ordering in reps[:max_orderings]:
        tried += 1
        cycles = enumerate_cycles(
            list(ordering), n, L_max, per_ordering_budget, max_cycles=1
        )
        if cycles:
            return ordering, cycles[0], tried, len(reps)
    return None, None, tried, len(reps)


def build_sub_corpus_n8(per_ordering_budget=4.0, max_orderings=20):
    """Full n=8 unordered-multiset sweep with representative orderings."""
    threshold = m_n(8)  # 2592
    all_comps = enumerate_compositions(8, threshold)
    ums = unordered_multisets(all_comps)
    print(f"  n=8: {len(ums)} unordered multisets (from {len(all_comps)} compositions), "
          f"threshold = {threshold}")
    out = []
    missed = []
    for i, sorted_ms in enumerate(sorted(ums)):
        t0 = time.time()
        ordering, cycle_data, tried, total_reps = find_cycle_for_multiset(
            sorted_ms, 8, L_max=48,
            per_ordering_budget=per_ordering_budget,
            max_orderings=max_orderings,
        )
        dt = time.time() - t0
        if ordering is None:
            missed.append({'sorted_ms': sorted_ms, 'tried': tried,
                           'total_reps': total_reps, 'dt': dt})
            print(f"  [{i+1}/{len(ums)}] sorted={sorted_ms} prod={int(np.prod(sorted_ms))} "
                  f"NO CYCLE found after {tried}/{total_reps} orderings, dt={dt:.1f}s")
            continue
        cycle, movers, det = cycle_data
        rec = {
            'class': 'sub',
            'n': 8,
            'ms': list(ordering),
            'sorted_ms': list(sorted_ms),
            'cycle': cycle,
            'movers': movers,
            'det': dict(det),
            'L': len(cycle),
            'product': int(np.prod(ordering)),
            'orderings_tried': tried,
            'orderings_total': total_reps,
        }
        out.append(rec)
        print(f"  [{i+1}/{len(ums)}] sorted={sorted_ms} ord={ordering} "
              f"prod={rec['product']} L={rec['L']} "
              f"(tried {tried}/{total_reps}, {dt:.1f}s)")
    return out, missed


def build_n9_table7_corpus(per_ordering_budget=10.0, max_orderings=80):
    """The three Table 7 multisets at n=9 with product 7776."""
    targets = [
        (2, 2, 2, 3, 3, 3, 3, 3, 4),  # {2^3, 3^5, 4}
        (2, 2, 2, 2, 3, 3, 3, 3, 6),  # {2^4, 3^4, 6}
        (2, 2, 2, 2, 2, 3, 3, 3, 9),  # {2^5, 3^3, 9}
    ]
    out = []
    missed = []
    for sorted_ms in targets:
        prod = int(np.prod(sorted_ms))
        reps = canonical_orderings(sorted_ms)
        print(f"  n=9 Table7 sorted={sorted_ms} prod={prod} "
              f"orbit reps={len(reps)} (testing up to {max_orderings})")
        found_any = False
        for j, ordering in enumerate(reps[:max_orderings]):
            t0 = time.time()
            cycles = enumerate_cycles(list(ordering), 9, 54,
                                      per_ordering_budget, max_cycles=1)
            dt = time.time() - t0
            if not cycles:
                continue
            cycle, movers, det = cycles[0]
            rec = {
                'class': 'sub_n9table7',
                'n': 9,
                'ms': list(ordering),
                'sorted_ms': list(sorted_ms),
                'cycle': cycle,
                'movers': movers,
                'det': dict(det),
                'L': len(cycle),
                'product': prod,
                'ordering_index': j,
                'orderings_total': len(reps),
            }
            out.append(rec)
            found_any = True
            print(f"    [ord {j+1}/{len(reps)}] ordering={ordering} "
                  f"L={rec['L']} dt={dt:.1f}s CYCLE-FOUND")
        if not found_any:
            missed.append({'sorted_ms': sorted_ms})
    return out, missed


# ----------------------------------------------------------------------
# At-threshold reference corpus (for separation audit)
# ----------------------------------------------------------------------

def build_record_from_witness(name, state_counts, rules):
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
        L = cfg[(proc - 1) % n]
        S = cfg[proc]
        R = cfg[(proc + 1) % n]
        new_S = fs[proc](L, S, R)
        lst = list(cfg)
        lst[proc] = new_S
        return tuple(lst)

    single_priv = {}
    for cfg in configs:
        p = privileged(cfg)
        if len(p) == 1:
            single_priv[cfg] = (move(cfg, p[0]), p[0])

    good_cycle = None
    good_movers = None
    for start in single_priv:
        path = []
        movers = []
        visited = set()
        cur = start
        while cur in single_priv and cur not in visited:
            visited.add(cur)
            path.append(cur)
            nxt, mover = single_priv[cur]
            movers.append(mover)
            cur = nxt
        if cur == start and path:
            good_cycle = path
            good_movers = movers
            break

    if good_cycle is None:
        return None

    det = {}
    for idx in range(len(good_cycle)):
        c = good_cycle[idx]
        mv = good_movers[idx]
        c_next = good_cycle[(idx + 1) % len(good_cycle)]
        for p in range(n):
            Lv = c[(p - 1) % n]
            Sv = c[p]
            Rv = c[(p + 1) % n]
            key = (p, Lv, Sv, Rv)
            det[key] = c_next[p] if p == mv else Sv
    for cfg in configs:
        for p in range(n):
            Lv = cfg[(p - 1) % n]
            Sv = cfg[p]
            Rv = cfg[(p + 1) % n]
            key = (p, Lv, Sv, Rv)
            if key not in det:
                det[key] = fs[p](Lv, Sv, Rv)

    return {
        'class': 'at_smallN',
        'name': name,
        'n': n,
        'ms': ms,
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
            continue
        ms, rules = fn()
        r = build_record_from_witness(label, ms, rules)
        if r is None:
            continue
        recs.append(r)
    return recs


# ----------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--skip-n8", action="store_true")
    parser.add_argument("--skip-n9", action="store_true")
    parser.add_argument("--n8-budget", type=float, default=4.0,
                        help="per-ordering cycle-search budget (s) at n=8")
    parser.add_argument("--n8-max-orderings", type=int, default=20)
    parser.add_argument("--n9-budget", type=float, default=10.0)
    parser.add_argument("--n9-max-orderings", type=int, default=120)
    parser.add_argument("--output", default=os.path.join(HERE, "phase1_n8_sub_corpus.json"))
    args = parser.parse_args()

    print("=" * 72)
    print("Strengthening #1 — n=8 sub-threshold corpus extension")
    print("=" * 72)
    t0 = time.time()

    # At-threshold reference witnesses (w5..w8) for separation audit
    print("\n--- at-threshold reference (small-n witnesses) ---")
    small_at = load_smalln_witnesses()
    for r in small_at:
        print(f"  {r['name']} ms={r['ms']} prod={r['product']} L={r['L']}")

    n8_sub, n8_missed = [], []
    if not args.skip_n8:
        print("\n--- n=8 sub-threshold sweep ---")
        n8_sub, n8_missed = build_sub_corpus_n8(
            per_ordering_budget=args.n8_budget,
            max_orderings=args.n8_max_orderings,
        )

    n9_table7, n9_missed = [], []
    if not args.skip_n9:
        print("\n--- n=9 Table 7 sub-threshold sweep ---")
        n9_table7, n9_missed = build_n9_table7_corpus(
            per_ordering_budget=args.n9_budget,
            max_orderings=args.n9_max_orderings,
        )

    print(f"\n--- analyzing {len(small_at)} at + {len(n8_sub)} n=8 sub "
          f"+ {len(n9_table7)} n=9 Table 7 records ---")
    at_results = [analyze_record(r) | {'name': r.get('name', '')} for r in small_at]
    n8_results = [analyze_record(r) for r in n8_sub]
    n9_results = [analyze_record(r) for r in n9_table7]

    # --- separation verdict ---
    at_feas = sum(1 for r in at_results if r['feasible'])
    sub_feas = sum(1 for r in n8_results if r['feasible'])
    n9_feas = sum(1 for r in n9_results if r['feasible'])
    print("\n" + "=" * 72)
    print("SEPARATION AUDIT")
    print("=" * 72)
    print(f"  at-threshold w5..w8    : feasible {at_feas}/{len(at_results)}  (expected 0)")
    print(f"  n=8 sub-threshold      : feasible {sub_feas}/{len(n8_results)}  (expected all)")
    print(f"  n=9 Table7 sub         : feasible {n9_feas}/{len(n9_results)}  (expected all)")
    violators = []
    for r in at_results:
        if r['feasible']:
            violators.append(('at_feasible_should_be_infeasible', r))
    for r in n8_results:
        if not r['feasible']:
            violators.append(('n8_sub_infeasible_counterexample', r))
    for r in n9_results:
        if not r['feasible']:
            violators.append(('n9_sub_infeasible_counterexample', r))
    if violators:
        print(f"\n*** {len(violators)} SEPARATION VIOLATIONS ***")
        for tag, r in violators[:10]:
            print(f"    {tag}: ms={r['ms']} L={r['L']} prod={r['product']}")
    else:
        print("\n*** DETECTOR SEPARATES on this extended corpus ***")

    # --- write JSON ---
    payload = {
        'timestamp': time.strftime("%Y-%m-%d %H:%M:%S"),
        'parameters': vars(args),
        'n8_sub': {
            'n_multisets_with_cycle': len(n8_results),
            'n_multisets_missed': len(n8_missed),
            'missed': [{'sorted_ms': list(m['sorted_ms']),
                        'tried': m['tried'], 'total': m['total_reps']}
                       for m in n8_missed],
            'records': [_strip(r) for r in n8_results],
        },
        'n9_table7_sub': {
            'n_ordering_records': len(n9_results),
            'n_multisets_missed': len(n9_missed),
            'records': [_strip(r) for r in n9_results],
        },
        'at_reference': {
            'records': [_strip(r) for r in at_results],
        },
        'separation_audit': {
            'at_feasible': at_feas,
            'at_total': len(at_results),
            'n8_sub_feasible': sub_feas,
            'n8_sub_total': len(n8_results),
            'n9_table7_feasible': n9_feas,
            'n9_table7_total': len(n9_results),
            'violations': [{'tag': t, 'ms': v['ms'], 'L': v['L'],
                            'product': v['product'], 'class': v['class']}
                           for t, v in violators],
        },
        'runtime_s': round(time.time() - t0, 1),
    }
    try:
        with open(args.output, "w") as f:
            json.dump(payload, f, indent=2, default=str)
        print(f"\nWrote {args.output} ({payload['runtime_s']}s)")
    except Exception as e:
        print(f"Write failed: {e}")


def _strip(rec):
    return {k: v for k, v in rec.items() if k != 'phi'}


if __name__ == "__main__":
    main()
