#!/usr/bin/env python3
"""Wave 6 T1 — V_tube refinement of the P1.5 subclass predicate.

Claim (Wave 5 addendum consolidation §2.5 lead 1):
  The predicate  max_q |V_tube[q]| <= 2  is iff with  dc_residual == 0
  on all 19 sub-threshold feasibility records.

Pre-commit per Wave 6 plan §1.3:
  GREEN  — iff on 19/19 (15 zero-residual satisfy, 4 nonzero-residual fail).
  RED false-positive — some nonzero record has max_q |V_tube[q]| <= 2.
  RED false-negative — some zero record has max_q |V_tube[q]| >= 3.
  PARTIAL — better than longest_ter_run<=1 (18/19) but not iff.

Rebuilds the Wave 5 sub corpus identically (same stride, same L_max,
same enumerate_cycles seed / ordering), computes V_tube and
dc_residual per record, emits the confusion matrix.
"""
from __future__ import annotations

import importlib.util
import json
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
WAVE5_PY = os.path.abspath(os.path.join(
    HERE, "..", "wave5", "probe_wave5_combined_2026-05-10.py"))

spec = importlib.util.spec_from_file_location("w5", WAVE5_PY)
w5 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(w5)


def build_sub_corpus():
    """Identical reconstruction of Wave 5 sub corpus."""
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


def analyze(rec):
    V, E = w5.build_lifted_graph(rec)
    lp = w5.solve_lp(len(V), E)
    a = {
        'class': 'sub', 'n': rec['n'], 'ms': rec['ms'], 'L': rec['L'],
        'feasible': lp['feasible'], 'phi': lp['phi'], '_E_lift': E,
    }
    if lp['feasible']:
        a['dc_residual'] = w5.direction_covariant_residual(a)
    return a


def v_tube_max(rec):
    cyc = [tuple(c) for c in rec['cycle']]
    n = rec['n']
    V = w5.value_set_tube(cyc, n)
    sizes = [len(s) for s in V]
    return max(sizes), sizes


def main():
    t0 = time.time()
    print("=" * 72)
    print("Wave 6 T1 — V_tube refinement of P1.5 subclass predicate")
    print("=" * 72)

    sub_corpus = build_sub_corpus()
    print(f"\nSub corpus rebuilt: {len(sub_corpus)} records")

    rows = []
    for r in sub_corpus:
        a = analyze(r)
        if not a.get('feasible'):
            continue
        vt_max, vt_sizes = v_tube_max(r)
        resid = a.get('dc_residual', 0.0)
        rows.append({
            'ms': r['ms'], 'n': r['n'], 'L': r['L'],
            'product': r['product'],
            'vt_sizes': vt_sizes, 'vt_max': vt_max,
            'dc_residual': resid,
            'zero_resid': resid < 1e-6,
            'pred_zero_T1': vt_max <= 2,
        })

    print(f"\nFeasible sub records: {len(rows)}")
    print(f"  zero-residual:    {sum(1 for r in rows if r['zero_resid'])}")
    print(f"  nonzero-residual: {sum(1 for r in rows if not r['zero_resid'])}")

    # Confusion matrix
    tp = sum(1 for r in rows if r['zero_resid'] and r['pred_zero_T1'])
    fp = sum(1 for r in rows if not r['zero_resid'] and r['pred_zero_T1'])
    fn = sum(1 for r in rows if r['zero_resid'] and not r['pred_zero_T1'])
    tn = sum(1 for r in rows if not r['zero_resid'] and not r['pred_zero_T1'])
    total = len(rows)
    correct = tp + tn

    print(f"\n=== T1 predicate: max_q |V_tube[q]| <= 2 ===")
    print(f"                  pred zero   pred nonzero")
    print(f"  actual zero       {tp:3d}          {fn:3d}")
    print(f"  actual nonzero    {fp:3d}          {tn:3d}")
    print(f"  accuracy: {correct}/{total} = {correct/total:.4f}")

    # Per-record detail
    print(f"\n=== Per-record detail ===")
    print(f"{'ms':<28} {'n':>2} {'L':>3} {'prod':>5} {'vt_max':>6} "
          f"{'vt_sizes':<22} {'resid':>7} {'T1_pred':>8} {'T1_ok':>6}")
    for r in rows:
        ms_s = str(tuple(r['ms']))
        t1_ok = (r['zero_resid'] == r['pred_zero_T1'])
        pred_s = 'zero' if r['pred_zero_T1'] else 'nonzero'
        flag = 'OK' if t1_ok else 'MISS'
        print(f"{ms_s:<28} {r['n']:>2} {r['L']:>3} {r['product']:>5} "
              f"{r['vt_max']:>6} {str(r['vt_sizes']):<22} "
              f"{r['dc_residual']:>7.4f} {pred_s:>8} {flag:>6}")

    # Misses in detail
    misses = [r for r in rows if r['zero_resid'] != r['pred_zero_T1']]
    print(f"\n=== Misses: {len(misses)} ===")
    for r in misses:
        typ = ('false-positive (predicted zero, actually nonzero)'
               if r['pred_zero_T1'] else
               'false-negative (predicted nonzero, actually zero)')
        print(f"  ms={tuple(r['ms'])}  vt_max={r['vt_max']}  "
              f"resid={r['dc_residual']:.4f}  [{typ}]")

    # Verdict
    print(f"\n=== Verdict ===")
    if fp == 0 and fn == 0:
        verdict = 'GREEN'
        msg = f"iff on {total}/{total}. Predicate refines Wave 5's 18/19."
    elif fp > 0 and fn == 0:
        verdict = 'RED (false-positive)'
        msg = f"{fp} nonzero-residual record(s) have max_q |V_tube[q]| <= 2; predicate fails to characterize subclass."
    elif fn > 0 and fp == 0:
        verdict = 'RED (false-negative)'
        msg = f"{fn} zero-residual record(s) have max_q |V_tube[q]| >= 3; predicate too strict."
    else:
        verdict = 'RED (mixed)'
        msg = f"{fp} false-pos and {fn} false-neg; predicate does not align with dc_residual."

    # Compare to Wave 5 longest_ter_run <= 1 baseline
    def longest_ter_run(ms):
        n = len(ms); cur = 0; best = 0
        for m in list(ms) + list(ms)[:n - 1]:
            if m == 3: cur += 1; best = max(best, cur)
            else: cur = 0
        return min(best, sum(1 for m in ms if m == 3))

    baseline_correct = sum(1 for r in rows
                           if (longest_ter_run(r['ms']) <= 1) == r['zero_resid'])
    print(f"  T1 verdict:         {verdict}")
    print(f"  T1 accuracy:        {correct}/{total}")
    print(f"  Baseline (W5):      {baseline_correct}/{total}  (longest_ter_run <= 1)")
    print(f"  {msg}")

    runtime = time.time() - t0
    print(f"\n  Runtime: {runtime:.1f}s")

    out = {
        'verdict': verdict,
        'message': msg,
        'confusion': {'tp': tp, 'fp': fp, 'fn': fn, 'tn': tn, 'total': total},
        'accuracy_T1': correct / total,
        'accuracy_baseline': baseline_correct / total,
        'rows': rows,
        'misses': [{'ms': r['ms'], 'vt_max': r['vt_max'],
                    'dc_residual': r['dc_residual']} for r in misses],
        'runtime_s': runtime,
    }
    with open(os.path.join(HERE, 'phaseW6_t1_results.json'), 'w') as f:
        json.dump(out, f, indent=2)
    print(f"  Wrote phaseW6_t1_results.json")


if __name__ == '__main__':
    main()
