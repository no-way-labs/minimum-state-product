#!/usr/bin/env python3
"""Wave 6 T4 — Non-standard sheaves with non-trivial restriction maps.

Per plan §4.2, three candidate constructions:

4.2.1 Single-priv-propagation sheaf.
  Stalks: rule-table entries at each 3-cell, same as standard.
  Restriction on shared (3-cell overlaps): instead of identity,
  require stalk values to be consistent with the cycle's mover at
  nearby steps — i.e., restrict along (k, k+1) cycle edges.

4.2.2 Path-sheaf.
  Indexing = paths in the forced-NG graph up to length L.
  Stalks = sequences of rule-table entries along the path.
  Restriction at shared prefixes enforces path-consistency.

4.2.3 Convergence-parameterized sheaf.
  Stalks = convergence depth d(c) = # forced-steps from c to good config.
  Restriction across Hamming-1 neighbors enforces d(c') ∈ {d(c) ± 1, d(c)}.
  H¹ obstructs globally-consistent depth assignment.

For each candidate, compute H¹ via simple cochain ranks over ℤ/2.

Pre-commit per §4.3: a candidate GREENs iff its H¹ > 0 at every sub-
threshold record AND = 0 at every at-threshold record. RED per candidate
if not. Route RED if all three candidates fail.
"""
from __future__ import annotations

import importlib.util
import json
import os
import sys
import time
from collections import defaultdict
from itertools import product as iproduct

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
WAVE5_PY = os.path.abspath(os.path.join(
    HERE, "..", "wave5", "probe_wave5_combined_2026-05-10.py"))
spec = importlib.util.spec_from_file_location("w5", WAVE5_PY)
w5 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(w5)


def rank_z2(M):
    if M.size == 0: return 0
    M = M.copy() % 2
    rows, cols = M.shape
    r = 0
    for c in range(cols):
        if r >= rows: break
        pivot = None
        for i in range(r, rows):
            if M[i, c] == 1: pivot = i; break
        if pivot is None: continue
        if pivot != r: M[[r, pivot]] = M[[pivot, r]]
        for i in range(rows):
            if i != r and M[i, c] == 1: M[i] ^= M[r]
        r += 1
    return r


# ================================================================
# Candidate 4.2.1 — single-priv-propagation sheaf
# ================================================================

def cech_h1_priv_propagation(rec):
    """Sheaf on lifted NG. Index set = cycle steps (0..L-1).
    Stalks F(k) = possible priv-next configs at step k (as subsets
    of Config). Restrictions r_{k,k+1}: F(k) → F(k+1) defined as
    apply-single-priv-forward.

    Cover U = {U_k}_{k=0..L-1} where U_k = {c : priv-forward-equivalent
    to cycle step k}.

    Because stalks encode configs, restriction maps may be non-trivial
    (a config in U_k ∩ U_{k+1} has different representations if cycle
    has multi-priv crossings).

    Čech δ^0: F(k) → F(k) × F(k+1), (f_k) → (f_{k+1} − r_{k,k+1} f_k).
    H^1 = ker δ^1 / im δ^0 on the nerve.

    For a period-L cycle alone (no auxiliary structure), the nerve is a
    single L-cycle; F(k) = detOf-consistent stalks; H^1 = 1 (one loop).

    Non-trivial discrimination via: sub stalks can be EMPTY at some k
    (no consistent extension of det to a single-priv transition at step
    k); at stalks nonempty.
    """
    ms = rec['ms']; n = len(ms)
    cycle = [tuple(c) for c in rec['cycle']]
    cycle_set = set(cycle)
    det = rec['det']; L = len(cycle)
    movers = rec['movers']

    # Stalk F(k) = set of det-consistent "potential moves" at step k:
    # at cycle[k], firing mov_k with context (mov_k, c[mov_k-1], c[mov_k],
    # c[mov_k+1]). If det has this entry, stalk = {forced_out}; else empty.
    # Trivially nonempty at all k for the cycle itself.
    # Refine: at (k, q) with q != mov_k, the stalk is the set of
    # rule-table entries det[(q, c[q-1], c[q], c[q+1])] — which is
    # c[q] because q is a non-mover.
    # This collapses to identity unless we enrich.
    # Enrichment: stalk F(k, q) = { alt_out : det[(q, c[q-1], alt_val,
    # c[q+1])] consistent with alt_val replacement at q on cycle[k]
    # maintaining det-consistency}. i.e., sides of the tube at step k.
    stalks = []
    for k in range(L):
        c = cycle[k]
        stalk_k = set()
        for q in range(n):
            for alt_v in range(ms[q]):
                if alt_v == c[q]: continue
                key = (q, c[(q-1)%n], alt_v, c[(q+1)%n])
                if key in det:
                    stalk_k.add((q, alt_v, det[key]))
        stalks.append(stalk_k)

    # Restrictions r_{k,k+1}: F(k) → F(k+1). For each element (q, alt, out)
    # ∈ F(k), check if cycle's step k→k+1 transition moves mov_k != q to
    # a new value, and the corresponding key in F(k+1) is (q, alt, out')
    # where out' = det[(q, cycle[k+1][q-1], alt, cycle[k+1][q+1])] if exists.
    # Restriction maps (q, alt, out) ↦ (q, alt, out') if consistent, else
    # marks as null.

    edges_used = 0; edges_null = 0
    for k in range(L):
        c_next = cycle[(k+1) % L]
        for (q, alt_v, out) in stalks[k]:
            key_next = (q, c_next[(q-1)%n], alt_v, c_next[(q+1)%n])
            if key_next in det:
                edges_used += 1
            else:
                edges_null += 1

    # H^1 computation as cochain complex over ℤ/2.
    # C^0 = direct sum of stalks F(k). Cochains c ∈ C^0 assign values
    # (over GF(2)) to elements of F(k).
    # δ^0 c (k, k+1)(x) = c(k+1)(r(x)) - c(k)(x) for x ∈ F(k) with r(x)
    # in F(k+1). We represent c(k) as a vector in GF(2)^{|F(k)|}.
    # δ^1 on C^1 = pairs (k, k+1): δ^1 vanishes since nerve is a 1-cycle.

    # Simplification: nerve is the L-cycle (pairwise overlaps at k,k+1).
    # C^0 dim = sum_k |F(k)|. C^1 dim = sum_k |F(k) ∩ F(k+1)|.
    C0 = sum(len(s) for s in stalks)
    # Count number of restriction-map edges (where r is defined)
    C1 = 0
    edges_list = []  # (src_k, src_idx, tgt_k, tgt_idx)
    stalk_lists = [sorted(s) for s in stalks]
    stalk_idx = [{e: i for i, e in enumerate(sl)} for sl in stalk_lists]
    for k in range(L):
        c_next = cycle[(k+1) % L]
        for x in stalk_lists[k]:
            q, alt_v, out = x
            key_next = (q, c_next[(q-1)%n], alt_v, c_next[(q+1)%n])
            if key_next in det:
                tgt = (q, alt_v, det[key_next])
                if tgt in stalk_idx[(k+1) % L]:
                    src_i = stalk_idx[k][x]
                    tgt_i = stalk_idx[(k+1) % L][tgt]
                    # offset in C^0
                    offset_src = sum(len(stalks[i]) for i in range(k)) + src_i
                    offset_tgt = sum(len(stalks[i]) for i in range((k+1)%L)) + tgt_i
                    edges_list.append((offset_src, offset_tgt))
                    C1 += 1

    if C0 == 0 or C1 == 0:
        return {'H1': 0, 'C0': C0, 'C1': C1, 'reason': 'empty-stalks-or-edges',
                'empty_stalks': [k for k in range(L) if len(stalks[k]) == 0]}

    # Build δ^0: C^0 → C^1
    d0 = np.zeros((C1, C0), dtype=np.uint8)
    for j, (src, tgt) in enumerate(edges_list):
        d0[j, src] = 1
        d0[j, tgt] = 1  # GF(2): minus = plus

    rk_d0 = rank_z2(d0)
    b0 = C0 - rk_d0
    # For nerve = 1-cycle, no δ^1 (nerve has no 2-simplices).
    b1 = C1 - rk_d0
    return {'H1': b1, 'C0': C0, 'C1': C1,
            'empty_stalks': [k for k in range(L) if len(stalks[k]) == 0]}


# ================================================================
# Candidate 4.2.2 — path sheaf
# ================================================================

def cech_h1_path(rec):
    """Sheaf on lifted forced-NG. Indexing set = directed edges of
    forced-NG. Stalks over edge e = (c, c') = configs reachable along
    walks starting at c, ending at c', using forced moves only.

    For path-consistency, restriction on a triangle (e1=(a,b), e2=(b,c),
    e12=(a,c)) requires the combined walk a→b→c matches the stalk of
    e12.

    Compact version: compute the cycle-space dimension of the forced-NG
    lifted graph itself (β_1 of the 1-skeleton, as a cell complex), with
    cells weighted by path-count mod 2. Forced-NG strongly connected
    implies β_1 = |E| - |V| + 1 for undirected.
    """
    V, E = w5.build_lifted_graph(rec)
    # Build undirected edge set
    edges_und = set()
    for s, t, _ in E:
        edges_und.add(tuple(sorted((s, t))))
    n_vert = len(V)
    n_edge = len(edges_und)
    if n_vert == 0:
        return {'H1': 0, 'nV': 0, 'nE': 0}
    # Connected components
    parent = list(range(n_vert))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    def union(x, y):
        rx, ry = find(x), find(y)
        if rx != ry: parent[rx] = ry
    for s, t in edges_und:
        union(s, t)
    ncomp = len(set(find(x) for x in range(n_vert)))
    b1 = n_edge - n_vert + ncomp
    return {'H1': b1, 'nV': n_vert, 'nE': n_edge, 'ncomp': ncomp}


# ================================================================
# Candidate 4.2.3 — convergence-parameterized sheaf
# ================================================================

def cech_h1_convergence(rec):
    """Sheaf on non-good configs. Stalks = minimum forced-steps from c
    to a good (cycle) config. Restriction on Hamming-1 neighbors:
    d(c') ∈ {d(c) ± 1, d(c)}.

    Cover: by level sets L_d = {c : d(c) = d}.
    H^1 obstructs a globally consistent depth assignment.

    Computation: compute d(c) via BFS on forced-NG, then check
    whether the Hamming-1 neighborhood relation is consistent
    with d-increments. Non-consistent = existence of a Hamming-1
    edge (c, c') with |d(c) - d(c')| > 1, an "H^1 defect."
    """
    ms = rec['ms']; n = len(ms)
    cycle = [tuple(c) for c in rec['cycle']]
    cycle_set = set(cycle)
    det = rec['det']

    # Use stay-completion for the forced graph. At a non-good config c,
    # follow the smallest-index single-priv move (if any).
    comp = dict(det)

    def successor(c):
        priv = []
        for i in range(n):
            L_ = c[(i-1)%n]; S_ = c[i]; R_ = c[(i+1)%n]
            out = comp.get((i, L_, S_, R_), S_)
            if out != S_: priv.append((i, out))
        if len(priv) == 0: return None
        i, out = priv[0]
        nc = list(c); nc[i] = out
        return tuple(nc)

    all_configs = list(iproduct(*(range(m) for m in ms)))
    # Compute d(c): BFS from cycle using inverse successor.
    # Simpler: forward-trace each config; d(c) = #steps until hit cycle.
    d = {c: 0 for c in cycle_set}
    for c in all_configs:
        if c in d: continue
        path = []
        cur = c
        seen = {cur}
        for _ in range(len(all_configs) + 1):
            if cur in d: break
            nxt = successor(cur)
            if nxt is None or nxt in seen:
                cur = None; break
            path.append(cur); seen.add(cur); cur = nxt
        if cur is None or cur not in d:
            for p in path: d[p] = -1  # unreachable / stuck
            continue
        base = d[cur]
        for i, p in enumerate(reversed(path)):
            d[p] = base + i + 1

    # Count Hamming-1 defects: edges (c, c') with d[c], d[c'] both ≥ 0,
    # and |d[c] - d[c']| > 1.
    defects = 0
    stuck = 0
    for c in all_configs:
        if d[c] == -1: stuck += 1
        for p in range(n):
            for v in range(ms[p]):
                if v == c[p]: continue
                nc = list(c); nc[p] = v; nc = tuple(nc)
                if nc <= c: continue  # avoid double-counting
                dc = d[c]; dnc = d[nc]
                if dc == -1 or dnc == -1: continue
                if abs(dc - dnc) > 1: defects += 1

    max_d = max((dv for dv in d.values() if dv >= 0), default=0)
    return {
        'H1_defects': defects,
        'max_depth': max_d,
        'n_stuck': stuck,
        'n_configs': len(all_configs),
    }


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


def build_at_corpus():
    DOCS_DIR = os.path.abspath(os.path.join(HERE, "..", "..", "..", "..", "docs"))
    sys.path.insert(0, DOCS_DIR)
    import verify_witnesses as vw
    at_corpus = []
    for n in range(5, 8):
        try:
            ms, fs, comp, cyc, mov = w5.build_clb_witness_v2(n)
            from verifier import verify_system
            if verify_system(ms, fs, verbose=False)['valid']:
                at_corpus.append({
                    'class': 'at_clb', 'n': n, 'ms': list(ms),
                    'cycle': [list(c) for c in cyc], 'movers': mov,
                    'det': dict(comp), 'L': len(cyc),
                    'product': int(np.prod(ms)),
                })
        except Exception: pass
    for name in ('witness_n5', 'witness_n6', 'witness_n7'):
        fn = getattr(vw, name, None)
        if fn is None: continue
        ms, rules = fn()
        r = w5.build_smalln_record(name[-2:], ms, rules)
        if r: at_corpus.append(r)
    return at_corpus


def main():
    t0 = time.time()
    print("=" * 72)
    print("Wave 6 T4 — Non-standard sheaves")
    print("=" * 72)

    sub_corpus = build_sub_corpus()
    at_corpus = build_at_corpus()
    print(f"\nCorpus: sub {len(sub_corpus)}, at {len(at_corpus)}")

    # Candidate 4.2.1
    print(f"\n=== Candidate 4.2.1 — single-priv-propagation sheaf ===")
    c1_rows = []
    for r in sub_corpus + at_corpus:
        try:
            res = cech_h1_priv_propagation(r)
            c1_rows.append({'class': r['class'], 'ms': r['ms'], 'n': r['n'],
                            'L': r['L'], **res})
        except Exception as e:
            print(f"  ms={tuple(r['ms'])}: error {e}")
    sub_H1 = [r['H1'] for r in c1_rows if r['class'] == 'sub']
    at_H1 = [r['H1'] for r in c1_rows if r['class'].startswith('at')]
    print(f"  sub H1: {sorted(set(sub_H1))}")
    print(f"   at H1: {sorted(set(at_H1))}")
    c1_disc = (set(sub_H1).isdisjoint(set(at_H1))
               and all(x > 0 for x in sub_H1)
               and all(x == 0 for x in at_H1))
    print(f"  discriminator (sub>0, at=0): {c1_disc}")

    # Candidate 4.2.2
    print(f"\n=== Candidate 4.2.2 — path (cycle-space) sheaf ===")
    c2_rows = []
    for r in sub_corpus + at_corpus:
        try:
            res = cech_h1_path(r)
            c2_rows.append({'class': r['class'], 'ms': r['ms'], 'n': r['n'],
                            'L': r['L'], **res})
        except Exception as e:
            pass
    sub_H1_2 = [r['H1'] for r in c2_rows if r['class'] == 'sub']
    at_H1_2 = [r['H1'] for r in c2_rows if r['class'].startswith('at')]
    print(f"  sub H1 (cycle-space β_1): min={min(sub_H1_2)} max={max(sub_H1_2)}")
    print(f"   at H1 (cycle-space β_1): min={min(at_H1_2)} max={max(at_H1_2)}")
    # Normalize by |V|
    print(f"  sub H1/|V|: [{min(r['H1']/r['nV'] for r in c2_rows if r['class']=='sub'):.3f},"
          f" {max(r['H1']/r['nV'] for r in c2_rows if r['class']=='sub'):.3f}]")
    print(f"   at H1/|V|: [{min(r['H1']/r['nV'] for r in c2_rows if r['class'].startswith('at')):.3f},"
          f" {max(r['H1']/r['nV'] for r in c2_rows if r['class'].startswith('at')):.3f}]")
    c2_disc = (all(r['H1'] > 0 for r in c2_rows if r['class'] == 'sub')
               and all(r['H1'] == 0 for r in c2_rows if r['class'].startswith('at')))
    print(f"  discriminator (sub>0, at=0): {c2_disc}")

    # Candidate 4.2.3
    print(f"\n=== Candidate 4.2.3 — convergence-parameterized sheaf ===")
    c3_rows = []
    for r in sub_corpus + at_corpus:
        try:
            res = cech_h1_convergence(r)
            c3_rows.append({'class': r['class'], 'ms': r['ms'], 'n': r['n'],
                            'L': r['L'], **res})
        except Exception as e:
            print(f"  ms={tuple(r['ms'])}: error {e}")
    print(f"{'class':<10} {'ms':<28} {'n':>2} {'L':>3} "
          f"{'H1_def':>7} {'max_d':>5} {'stuck':>5}")
    for r in c3_rows:
        print(f"{r['class']:<10} {str(tuple(r['ms'])):<28} {r['n']:>2} "
              f"{r['L']:>3} {r['H1_defects']:>7} {r['max_depth']:>5} "
              f"{r['n_stuck']:>5}")
    sub_def = [r['H1_defects'] for r in c3_rows if r['class'] == 'sub']
    at_def = [r['H1_defects'] for r in c3_rows if r['class'].startswith('at')]
    print(f"  sub H1_defects: [{min(sub_def)}, {max(sub_def)}]")
    print(f"   at H1_defects: [{min(at_def)}, {max(at_def)}]")
    c3_disc = (all(x > 0 for x in sub_def) and all(x == 0 for x in at_def))
    print(f"  discriminator (sub>0, at=0): {c3_disc}")

    # Verdict
    print(f"\n=== T4 verdict ===")
    anywhere_green = c1_disc or c2_disc or c3_disc
    if anywhere_green:
        verdict = 'GREEN'
        msg = (f"Candidate(s) discriminating: "
               f"4.2.1={c1_disc}, 4.2.2={c2_disc}, 4.2.3={c3_disc}")
    else:
        verdict = 'RED (all candidates)'
        msg = ("None of the three non-standard sheaf candidates discriminates "
               "sub from at cleanly. The non-trivial-restriction sheaf "
               "approach does not work with the natural constructions.")
    print(f"  {verdict}: {msg}")

    runtime = time.time() - t0
    out = {
        'verdict': verdict,
        'message': msg,
        '4.2.1_discriminates': c1_disc,
        '4.2.2_discriminates': c2_disc,
        '4.2.3_discriminates': c3_disc,
        '4.2.1_rows': c1_rows,
        '4.2.2_rows': c2_rows,
        '4.2.3_rows': c3_rows,
        'runtime_s': runtime,
    }
    with open(os.path.join(HERE, 'phaseW6_t4_results.json'), 'w') as f:
        json.dump(out, f, indent=2)
    print(f"\n  Runtime: {runtime:.1f}s")
    print(f"  Wrote phaseW6_t4_results.json")


if __name__ == '__main__':
    main()
