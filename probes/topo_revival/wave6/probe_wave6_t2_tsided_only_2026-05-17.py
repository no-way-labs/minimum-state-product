#!/usr/bin/env python3
"""Wave 6 T2 empirical — T+sided-only circulation existence.

Claim (Wave 6 plan §2.1, from addendum consolidation §2.2 dir 3 + §2.5 lead 2):
  On the forced-NG lifted graph of a sub-threshold subclass record,
  the subgraph induced by transport ∪ c_left ∪ c_right edges (i.e.
  c_self deleted) already carries a nonzero nonnegative circulation.

If so, the restricted theorem reduces to proving existence of that
restricted cycle — no reasoning about c_self is needed.

Pre-commit per §2.3:
  GREEN  — 100% of subclass records feasible with c_self removed.
  RED    — any subclass record infeasible. c_self is structurally necessary.
  PARTIAL — some feasible, some not; investigate correlation.

Uses Wave 5 baseline subclass (longest_ter_run <= 1) since T1 RED.
Run on all 19 sub-threshold records for diagnostic breadth, tag
subclass membership in the output.
"""
from __future__ import annotations

import importlib.util
import json
import os
import sys
import time

import numpy as np
from scipy.optimize import linprog

HERE = os.path.dirname(os.path.abspath(__file__))
WAVE5_PY = os.path.abspath(os.path.join(
    HERE, "..", "wave5", "probe_wave5_combined_2026-05-10.py"))

spec = importlib.util.spec_from_file_location("w5", WAVE5_PY)
w5 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(w5)


def build_sub_corpus():
    sub_corpus = []
    L_max = {5: 40, 6: 24, 7: 18}
    for nn in (5, 6, 7):
        Mn = w5.m_n(nn)
        ms_list = w5.enumerate_multisets(nn, Mn)
        stride = max(1, len(ms_list) // 9)
        for ms in ms_list[::stride][:8]:
            cyc = w5.enumerate_cycles(ms, nn, L_max[nn], 2.0, 1)
            for c, mov, det in cyc:
                sub_corpus.append({
                    'class': 'sub', 'n': nn, 'ms': list(ms),
                    'cycle': c, 'movers': mov, 'det': dict(det),
                    'L': len(c), 'product': int(np.prod(ms)),
                })
    return sub_corpus


def solve_lp_filtered(n_vert, E_lift, allowed_types):
    """Flow LP restricted to edges whose type is in allowed_types."""
    E_filt = [(s, t, et) for (s, t, et) in E_lift if et in allowed_types]
    nE = len(E_filt)
    if nE == 0:
        return {'feasible': False, 'nE': 0, 'supp_size': 0, 'phi': []}
    Aeq = np.zeros((n_vert, nE))
    for e_idx, (s, t, _) in enumerate(E_filt):
        Aeq[s, e_idx] -= 1
        Aeq[t, e_idx] += 1
    beq = np.zeros(n_vert)
    c = -np.ones(nE)
    bounds = [(0.0, 1.0)] * nE
    res = linprog(c, A_eq=Aeq, b_eq=beq, bounds=bounds, method='highs')
    if not res.success:
        return {'feasible': False, 'nE': nE, 'supp_size': 0, 'phi': []}
    x = res.x
    obj = float(res.fun)
    supp = sum(1 for xi in x if xi > 1e-6)
    return {
        'feasible': obj < -1e-9,
        'nE': nE,
        'supp_size': supp,
        'phi': x.tolist(),
        'obj': -obj,
    }


def edge_type_histogram(E_lift):
    from collections import Counter
    return dict(Counter(et for _, _, et in E_lift))


def longest_ter_run(ms):
    n = len(ms); cur = 0; best = 0
    for m in list(ms) + list(ms)[:n - 1]:
        if m == 3: cur += 1; best = max(best, cur)
        else: cur = 0
    return min(best, sum(1 for m in ms if m == 3))


def main():
    t0 = time.time()
    print("=" * 72)
    print("Wave 6 T2 empirical — T+sided-only circulation on lifted forced-NG")
    print("=" * 72)

    sub_corpus = build_sub_corpus()
    print(f"\nSub corpus rebuilt: {len(sub_corpus)} records")

    rows = []
    for r in sub_corpus:
        V, E = w5.build_lifted_graph(r)
        n_vert = len(V)

        # Baseline LP: all edge types (sanity)
        lp_all = solve_lp_filtered(
            n_vert, E, {'transport', 'c_self', 'c_left', 'c_right', 'other'})
        # Restricted LP: c_self deleted
        lp_no_cself = solve_lp_filtered(
            n_vert, E, {'transport', 'c_left', 'c_right', 'other'})

        lt_run = longest_ter_run(r['ms'])
        subclass = (lt_run <= 1)

        row = {
            'ms': r['ms'], 'n': r['n'], 'L': r['L'],
            'product': r['product'],
            'n_vert': n_vert, 'n_edge': len(E),
            'edge_hist': edge_type_histogram(E),
            'longest_ter_run': lt_run,
            'subclass_W5': subclass,
            'feas_all': lp_all['feasible'],
            'feas_no_cself': lp_no_cself['feasible'],
            'supp_all': lp_all['supp_size'],
            'supp_no_cself': lp_no_cself['supp_size'],
            'obj_all': lp_all.get('obj', 0.0),
            'obj_no_cself': lp_no_cself.get('obj', 0.0),
            'nE_no_cself': lp_no_cself['nE'],
        }
        rows.append(row)

    # Report
    print(f"\n{'ms':<28} {'n':>2} {'L':>3} {'lt_run':>6} {'sub':>4} "
          f"{'feas_all':>8} {'feas_no_cs':>10} {'supp_all':>8} {'supp_nocs':>9} "
          f"{'c_self%':>8}")
    for r in rows:
        eh = r['edge_hist']
        total_e = max(1, r['n_edge'])
        cs_pct = eh.get('c_self', 0) / total_e * 100
        print(f"{str(tuple(r['ms'])):<28} {r['n']:>2} {r['L']:>3} "
              f"{r['longest_ter_run']:>6} {str(r['subclass_W5']):>4} "
              f"{str(r['feas_all']):>8} {str(r['feas_no_cself']):>10} "
              f"{r['supp_all']:>8} {r['supp_no_cself']:>9} "
              f"{cs_pct:>7.1f}%")

    subclass_rows = [r for r in rows if r['subclass_W5']]
    nonsubclass_rows = [r for r in rows if not r['subclass_W5']]
    print(f"\nSubclass rows (longest_ter_run <= 1): {len(subclass_rows)}")
    sub_feas_all = sum(1 for r in subclass_rows if r['feas_all'])
    sub_feas_nocs = sum(1 for r in subclass_rows if r['feas_no_cself'])
    print(f"  feasible with all edges:    {sub_feas_all}/{len(subclass_rows)}")
    print(f"  feasible without c_self:    {sub_feas_nocs}/{len(subclass_rows)}")

    nonsub_feas_all = sum(1 for r in nonsubclass_rows if r['feas_all'])
    nonsub_feas_nocs = sum(1 for r in nonsubclass_rows if r['feas_no_cself'])
    print(f"\nNonsubclass rows (longest_ter_run >= 2): {len(nonsubclass_rows)}")
    print(f"  feasible with all edges:    {nonsub_feas_all}/{len(nonsubclass_rows)}")
    print(f"  feasible without c_self:    {nonsub_feas_nocs}/{len(nonsubclass_rows)}")

    infeas_subclass = [r for r in subclass_rows if not r['feas_no_cself']]
    print(f"\n=== Subclass records infeasible without c_self: {len(infeas_subclass)} ===")
    for r in infeas_subclass:
        eh = r['edge_hist']
        print(f"  ms={tuple(r['ms'])}  L={r['L']}  n_edge={r['n_edge']}  "
              f"edge_hist={eh}  nE_no_cself={r['nE_no_cself']}")

    # Verdict
    print(f"\n=== T2 empirical verdict ===")
    if sub_feas_nocs == len(subclass_rows) and len(subclass_rows) > 0:
        verdict = 'GREEN'
        msg = ("100% of subclass records feasible without c_self; restricted "
               "theorem path opens. Attempt analytical proof.")
    elif sub_feas_nocs == 0:
        verdict = 'RED (complete)'
        msg = "No subclass record is feasible without c_self; c_self structurally necessary."
    elif sub_feas_nocs < len(subclass_rows):
        verdict = 'PARTIAL'
        msg = (f"{sub_feas_nocs}/{len(subclass_rows)} subclass records feasible "
               f"without c_self; investigate correlation.")
    else:
        verdict = 'RED (no subclass)'
        msg = "Subclass empty after W5 predicate; nothing to test."

    print(f"  verdict: {verdict}")
    print(f"  {msg}")

    runtime = time.time() - t0
    print(f"\n  Runtime: {runtime:.1f}s")

    out = {
        'verdict': verdict,
        'message': msg,
        'subclass_feas_no_cself': sub_feas_nocs,
        'subclass_total': len(subclass_rows),
        'nonsubclass_feas_no_cself': nonsub_feas_nocs,
        'nonsubclass_total': len(nonsubclass_rows),
        'rows': rows,
        'runtime_s': runtime,
    }
    with open(os.path.join(HERE, 'phaseW6_t2_results.json'), 'w') as f:
        json.dump(out, f, indent=2)
    print(f"  Wrote phaseW6_t2_results.json")


if __name__ == '__main__':
    main()
