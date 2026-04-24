#!/usr/bin/env python3
"""Wave 6 T2 structural diagnostic — what does the T+sided-only witness look like?

For each of the 19 sub records:
- Compute T+sided-only LP witness (c_self removed).
- Partition support by the q-tube (position) of each endpoint.
- Count: edges per q, edges crossing q-tubes, transport vs c_left vs c_right.

If witness decomposes cleanly into q-tube circulations (per-q balanced,
no q-crossing), the structural proof target is "each q-tube is itself a
T+sided-only cycle," which is a much simpler structural statement.
"""
from __future__ import annotations

import importlib.util
import json
import os
import time
from collections import Counter, defaultdict

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


def solve_tsided(n_vert, E_lift):
    E_filt = [(s, t, et) for (s, t, et) in E_lift
              if et in ('transport', 'c_left', 'c_right', 'other')]
    nE = len(E_filt)
    if nE == 0: return None, E_filt
    Aeq = np.zeros((n_vert, nE))
    for e_idx, (s, t, _) in enumerate(E_filt):
        Aeq[s, e_idx] -= 1; Aeq[t, e_idx] += 1
    res = linprog(-np.ones(nE), A_eq=Aeq, b_eq=np.zeros(n_vert),
                  bounds=[(0.0, 1.0)] * nE, method='highs')
    return (res.x if res.success else None), E_filt


def analyze_witness(rec):
    V, E = w5.build_lifted_graph(rec)
    n_vert = len(V)
    phi, E_filt = solve_tsided(n_vert, E)
    if phi is None: return None
    # q-tube accounting
    q_of = [v[1] for v in V]  # V[i] = (k, q, a); q_of[i] = q
    edges_by_type = defaultdict(float)
    edges_by_q = defaultdict(float)  # keyed by (q_src, q_tgt)
    active_edges = 0
    per_vertex_flow_in = defaultdict(float)
    per_vertex_flow_out = defaultdict(float)
    for e_idx, (s, t, et) in enumerate(E_filt):
        f = phi[e_idx]
        if f < 1e-8: continue
        active_edges += 1
        edges_by_type[et] += f
        qs = q_of[s]; qt = q_of[t]
        edges_by_q[(qs, qt)] += f
        per_vertex_flow_out[s] += f
        per_vertex_flow_in[t] += f

    # Is support per-q balanced? i.e., do q_src = q_tgt for all support edges?
    same_q = sum(f for (qs, qt), f in edges_by_q.items() if qs == qt)
    cross_q = sum(f for (qs, qt), f in edges_by_q.items() if qs != qt)
    total_flow = same_q + cross_q
    same_q_frac = same_q / total_flow if total_flow > 0 else 0.0
    per_q_supp = Counter()
    for (qs, qt), f in edges_by_q.items():
        if qs == qt and f > 1e-8: per_q_supp[qs] += 1
    return {
        'n_vert': n_vert, 'n_edges_filt': len(E_filt),
        'active_edges': active_edges,
        'total_flow': total_flow,
        'edges_by_type': {k: v for k, v in edges_by_type.items()},
        'same_q_flow': same_q, 'cross_q_flow': cross_q,
        'same_q_frac': same_q_frac,
        'per_q_supp': dict(per_q_supp),
        'n_q_used': len(per_q_supp),
    }


def main():
    t0 = time.time()
    print("=" * 72)
    print("Wave 6 T2 structural — witness decomposition by q-tube")
    print("=" * 72)
    sub_corpus = build_sub_corpus()

    rows = []
    for r in sub_corpus:
        w = analyze_witness(r)
        if w is None:
            print(f"  {tuple(r['ms'])}: LP infeasible")
            continue
        rows.append({
            'ms': r['ms'], 'n': r['n'], 'L': r['L'], **w,
        })

    print(f"\n{'ms':<28} {'n':>2} {'L':>3} {'supp':>5} {'flow':>6} "
          f"{'T':>6} {'cL':>6} {'cR':>6} {'oth':>6} {'same_q%':>8} {'q_used':>7}")
    for w in rows:
        eb = w['edges_by_type']
        ft = eb.get('transport', 0); fl = eb.get('c_left', 0)
        fr = eb.get('c_right', 0); fo = eb.get('other', 0)
        print(f"{str(tuple(w['ms'])):<28} {w['n']:>2} {w['L']:>3} "
              f"{w['active_edges']:>5} {w['total_flow']:>6.2f} "
              f"{ft:>6.2f} {fl:>6.2f} {fr:>6.2f} {fo:>6.2f} "
              f"{w['same_q_frac']*100:>7.1f}% {w['n_q_used']:>7}")

    all_same_q = all(abs(w['same_q_frac'] - 1.0) < 1e-6 for w in rows)
    print(f"\nAll witnesses purely single-q (same_q_frac = 100%): {all_same_q}")
    total_cross_q = sum(w['cross_q_flow'] for w in rows)
    print(f"Total cross-q flow across all records: {total_cross_q:.6f}")

    # Ratio edges_by_type
    total_T = sum(w['edges_by_type'].get('transport', 0) for w in rows)
    total_cL = sum(w['edges_by_type'].get('c_left', 0) for w in rows)
    total_cR = sum(w['edges_by_type'].get('c_right', 0) for w in rows)
    total_other = sum(w['edges_by_type'].get('other', 0) for w in rows)
    total_all = total_T + total_cL + total_cR + total_other
    print(f"\nEdge-type flow breakdown (all records):")
    print(f"  transport: {total_T:.2f} ({total_T/total_all*100:.1f}%)")
    print(f"  c_left:    {total_cL:.2f} ({total_cL/total_all*100:.1f}%)")
    print(f"  c_right:   {total_cR:.2f} ({total_cR/total_all*100:.1f}%)")
    print(f"  other:     {total_other:.2f} ({total_other/total_all*100:.1f}%)")

    # Per-q flow detail
    print(f"\nPer-q support uniform across q? (single-q witnesses only)")
    for w in rows:
        if w['n_q_used'] > 0:
            per_q = w['per_q_supp']
            print(f"  ms={tuple(w['ms'])} q-tubes used: {per_q}")

    with open(os.path.join(HERE, 'phaseW6_t2_structure.json'), 'w') as f:
        json.dump(rows, f, indent=2)

    print(f"\n  Runtime: {time.time()-t0:.1f}s")
    print(f"  Wrote phaseW6_t2_structure.json")


if __name__ == '__main__':
    main()
