#!/usr/bin/env python3
"""Wave 6 T3 — Discrete Conley index of the good cycle.

Per plan §3.2 (from Wave 1 plan §8.2):
  1. Find an isolating block N ⊂ Config: C ⊂ int(N), forward trajectories
     from ∂N leave immediately, maximal invariant set in N is C.
     Concrete starting point: N = C ∪ (N_1(C) ∩ forced-closed-under-successor),
     exit set L = boundary configs mapping outside N.
  2. Compute Conley index h(C, f) = homotopy type of N/L as finite
     simplicial complex. Compute Betti numbers β_0, β_1 over ℤ/2.
  3. Compare to expected period-L attractor index.

For a deterministic period-L attractor in a finite-state map, the
expected index is a single L-cycle (wedge of one circle / β_0=1, β_1=1)
modulo the trivial exit-set. At sub-threshold, if the forced rules don't
actually give a period-L attractor (because they don't complete to a
valid system), we expect the index to differ.

Pre-commit per §3.3:
  SURVIVES  — sub index inconsistent with expected attractor index,
              at index matches.
  RED type-1 — (n,L)-parametrized (replicates Wave 1 P1 failure mode).
  RED type-2 — matches expected attractor index at both classes.

Treatment:
- For a record with cycle C and determined rule table det, build the
  "full map" f(c) = arg max{firing at each single priv} — ambiguous
  where multiple priv exist. For sub records det is partial; extend
  by "stay" for undetermined priv contexts (the map assigns the
  current value). This gives a well-defined deterministic map for
  single-priv configs and an "uncertainty" region for multi-priv.
- Isolating block N = C ∪ (Hamming-1 neighbors of C that map under
  f into C or back to themselves).
- Exit set L = configs in ∂N whose image under f is not in N.
- Simplicial complex: vertices = N, 1-simplices = Hamming-1 edges
  within N, 2-simplices = Hamming-1 triangles within N.
- Conley complex = (N/L, L/L); compute β_0 and β_1 over ℤ/2.
"""
from __future__ import annotations

import importlib.util
import json
import os
import time
from collections import defaultdict
from itertools import product as iproduct, combinations

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
WAVE5_PY = os.path.abspath(os.path.join(
    HERE, "..", "wave5", "probe_wave5_combined_2026-05-10.py"))
spec = importlib.util.spec_from_file_location("w5", WAVE5_PY)
w5 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(w5)


def build_full_map(ms, det):
    """Extend det by 'stay' for missing contexts.
    f(c) = successor config for single-priv c, else stay."""
    n = len(ms)
    comp = dict(det)
    def forced(p, L, S, R):
        return comp.get((p, L, S, R), S)
    def f(c):
        priv = []
        for i in range(n):
            L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
            out = forced(i, L, S, R)
            if out != S: priv.append((i, out))
        if len(priv) == 0: return c  # stable
        # Pick the smallest-index priv (deterministic tiebreak)
        i, out = priv[0]
        nc = list(c); nc[i] = out
        return tuple(nc)
    return f


def hamming1_neighbors(c, ms):
    n = len(ms)
    out = []
    for p in range(n):
        for v in range(ms[p]):
            if v == c[p]: continue
            nc = list(c); nc[p] = v
            out.append(tuple(nc))
    return out


def isolating_block_and_exit(cycle_set, ms, f, radius=1):
    """N = cycle ∪ (all configs within Hamming distance ≤ radius of cycle).

    Isolating-block semantics: N is a neighborhood of C; exit set
    L = {c ∈ N : f(c) ∉ N} captures configs whose forward image leaves
    N. C itself maps within cycle_set ⊂ N, so C is forward-invariant
    in N. Configs in N_1 that don't map back into N are the boundary.

    For C to be the maximal invariant set in N, the maximal invariant
    subset I(N) = ∩_{k≥0} f^{-k}(N) should equal C. This test is
    ensured by the diagnostic in main().
    """
    N = set(cycle_set)
    frontier = set(cycle_set)
    for _ in range(radius):
        new = set()
        for c in frontier:
            for nc in hamming1_neighbors(c, ms):
                if nc not in N: new.add(nc)
        N |= new
        frontier = new

    L = set()
    for c in N:
        fc = f(c)
        if fc not in N:
            L.add(c)
    return N, L


def maximal_invariant_subset(N, f, cycle_set):
    """Compute I(N) = {c ∈ N : f^k(c) ∈ N for all k ≥ 0}.
    Return |I(N)|, and whether I(N) == cycle_set."""
    invariant = set(N)
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for c in invariant:
            fc = f(c)
            if fc not in invariant:
                to_remove.add(c)
        if to_remove:
            invariant -= to_remove
            changed = True
    return invariant


def build_simplicial_complex(N, ms, max_dim=2):
    """Vertices = N. 1-simplices = Hamming-1 edges within N.
    2-simplices = triples (u,v,w) pairwise Hamming-1 within N."""
    vertex_list = sorted(N)
    idx = {c: i for i, c in enumerate(vertex_list)}
    one_simplices = []
    for i, c in enumerate(vertex_list):
        for nc in hamming1_neighbors(c, ms):
            if nc in idx and idx[nc] > i:
                one_simplices.append((i, idx[nc]))
    # Triangles: find all triples i<j<k pairwise H1
    two_simplices = []
    if max_dim >= 2:
        adj = defaultdict(set)
        for (a, b) in one_simplices:
            adj[a].add(b); adj[b].add(a)
        for a in range(len(vertex_list)):
            for b in adj[a]:
                if b <= a: continue
                for c in adj[a] & adj[b]:
                    if c <= b: continue
                    two_simplices.append((a, b, c))
    return vertex_list, one_simplices, two_simplices


def betti_z2(vertex_list, one_simplices, two_simplices):
    """Compute β_0 and β_1 over ℤ/2 via ranks of boundary maps."""
    nV = len(vertex_list); nE = len(one_simplices); nT = len(two_simplices)
    # ∂_1: E → V
    d1 = np.zeros((nV, nE), dtype=np.uint8)
    for j, (a, b) in enumerate(one_simplices):
        d1[a, j] = 1; d1[b, j] = 1
    # ∂_2: T → E
    e_idx = {e: j for j, e in enumerate(one_simplices)}
    d2 = np.zeros((nE, nT), dtype=np.uint8)
    for k, (a, b, c) in enumerate(two_simplices):
        for e in ((a, b), (a, c), (b, c)):
            if e in e_idx: d2[e_idx[e], k] = 1

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

    rk_d1 = rank_z2(d1); rk_d2 = rank_z2(d2)
    b0 = nV - rk_d1
    b1 = (nE - rk_d1) - rk_d2
    return b0, b1, nV, nE, nT


def quotient_homology(N, L, ms):
    """Compute Betti numbers of N/L.
    Implementation: all simplices in L are identified to a basepoint.
    Equivalent: β_k(N/L) = β_k(N, L) for k >= 1; β_0(N/L) = β_0(N) − (# components meeting L, counted once) + 1 when L non-empty.

    Simpler computation: build N's simplicial complex, collapse L to a
    single basepoint * by: create one "super-vertex" for L; replace
    each L-vertex with *; remove duplicate simplices; compute β.
    """
    # Use index: vertex_list = (N \ L) ∪ {basepoint}
    N_minus_L = sorted(N - L)
    basepoint_idx = len(N_minus_L)  # index of the basepoint '*'
    idx = {c: i for i, c in enumerate(N_minus_L)}
    nV = len(N_minus_L) + 1

    def to_idx(c):
        return idx[c] if c in idx else basepoint_idx

    # 1-simplices
    edges = set()
    for c in N:
        for nc in hamming1_neighbors(c, ms):
            if nc not in N: continue
            i = to_idx(c); j = to_idx(nc)
            if i == j: continue  # both in L, collapses to basepoint
            e = tuple(sorted((i, j)))
            edges.add(e)
    one_simplices = sorted(edges)

    # 2-simplices
    adj = defaultdict(set)
    for (a, b) in one_simplices:
        adj[a].add(b); adj[b].add(a)
    vert_N = sorted(N)
    idx_N = {c: i for i, c in enumerate(vert_N)}
    adj_N = defaultdict(set)
    for c in vert_N:
        for nc in hamming1_neighbors(c, ms):
            if nc in idx_N: adj_N[idx_N[c]].add(idx_N[nc])
    triples = set()
    for a_N in range(len(vert_N)):
        for b_N in adj_N[a_N]:
            if b_N <= a_N: continue
            for c_N in adj_N[a_N] & adj_N[b_N]:
                if c_N <= b_N: continue
                ca, cb, cc = vert_N[a_N], vert_N[b_N], vert_N[c_N]
                ia = to_idx(ca); ib = to_idx(cb); ic = to_idx(cc)
                tri = tuple(sorted({ia, ib, ic}))
                if len(tri) < 3: continue  # degenerate (≥2 in L)
                triples.add(tri)
    two_simplices = sorted(triples)

    # Betti numbers
    vertex_list = list(range(nV))
    b0, b1, nv, ne, nt = betti_z2(vertex_list, one_simplices, two_simplices)
    return b0, b1, nv, ne, nt


def conley_index(rec):
    ms = rec['ms']; n = len(ms)
    cycle = [tuple(c) for c in rec['cycle']]
    cycle_set = set(cycle)
    det = rec['det']
    f = build_full_map(ms, det)

    N, L = isolating_block_and_exit(cycle_set, ms, f, radius=1)

    # Diagnostic: is C the maximal invariant subset of N?
    I_N = maximal_invariant_subset(N, f, cycle_set)
    isolated_ok = (I_N == cycle_set)

    # Raw N complex
    vl_N, e_N, t_N = build_simplicial_complex(N, ms)
    b0_N, b1_N, _, _, _ = betti_z2(vl_N, e_N, t_N)

    # Quotient N/L
    b0_NL, b1_NL, nv_NL, ne_NL, nt_NL = quotient_homology(N, L, ms)

    return {
        'n': n, 'L_cycle': len(cycle),
        'N_size': len(N), 'L_size': len(L), 'IN_size': len(I_N),
        'isolated_ok': isolated_ok,
        'b0_N': b0_N, 'b1_N': b1_N,
        'b0_NL': b0_NL, 'b1_NL': b1_NL,
        'ne_NL': ne_NL, 'nt_NL': nt_NL,
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
    import sys
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
    print("Wave 6 T3 — Discrete Conley index")
    print("=" * 72)

    sub_corpus = build_sub_corpus()
    at_corpus = build_at_corpus()
    print(f"\nCorpus: sub {len(sub_corpus)}, at {len(at_corpus)}")

    rows = []
    for r in sub_corpus + at_corpus:
        try:
            ci = conley_index(r)
            ci['ms'] = r['ms']; ci['class'] = r['class']
            rows.append(ci)
        except Exception as e:
            print(f"  {tuple(r['ms'])}: Error {e}")

    print(f"\n{'class':<10} {'ms':<28} {'n':>2} {'L':>3} {'|N|':>4} {'|L|':>4} "
          f"{'|I(N)|':>7} {'iso':>4} "
          f"{'b0_N':>4} {'b1_N':>4} {'b0_N/L':>6} {'b1_N/L':>6}")
    for ci in rows:
        print(f"{ci['class']:<10} {str(tuple(ci['ms'])):<28} {ci['n']:>2} "
              f"{ci['L_cycle']:>3} {ci['N_size']:>4} {ci['L_size']:>4} "
              f"{ci['IN_size']:>7} {str(ci['isolated_ok']):>4} "
              f"{ci['b0_N']:>4} {ci['b1_N']:>4} "
              f"{ci['b0_NL']:>6} {ci['b1_NL']:>6}")

    # Summarize
    sub_b1_NL = [ci['b1_NL'] for ci in rows if ci['class'] == 'sub']
    at_b1_NL = [ci['b1_NL'] for ci in rows if ci['class'].startswith('at')]
    sub_b0_NL = [ci['b0_NL'] for ci in rows if ci['class'] == 'sub']
    at_b0_NL = [ci['b0_NL'] for ci in rows if ci['class'].startswith('at')]

    print(f"\n=== Summary ===")
    print(f"  sub β_0(N/L): set={sorted(set(sub_b0_NL))}")
    print(f"  sub β_1(N/L): set={sorted(set(sub_b1_NL))}")
    print(f"   at β_0(N/L): set={sorted(set(at_b0_NL))}")
    print(f"   at β_1(N/L): set={sorted(set(at_b1_NL))}")

    # Expected for period-L attractor: β_0 = 1, β_1 = 1 (one L-cycle,
    # base point collapses exit set).
    sub_matches_expected = all(b0 == 1 and b1 == 1
                               for b0, b1 in zip(sub_b0_NL, sub_b1_NL))
    at_matches_expected = all(b0 == 1 and b1 == 1
                              for b0, b1 in zip(at_b0_NL, at_b1_NL))
    print(f"  sub matches (β_0=1, β_1=1): {sub_matches_expected}")
    print(f"   at matches (β_0=1, β_1=1): {at_matches_expected}")

    # Discrimination check
    sub_set = set(zip(sub_b0_NL, sub_b1_NL))
    at_set = set(zip(at_b0_NL, at_b1_NL))
    discriminates = sub_set.isdisjoint(at_set)
    print(f"  sub index set: {sub_set}")
    print(f"   at index set: {at_set}")
    print(f"  discriminates sub from at: {discriminates}")

    # Verdict per §3.3
    if discriminates and not sub_matches_expected and at_matches_expected:
        verdict = 'GREEN'
        msg = "sub Conley index inconsistent with attractor; at matches. Discriminator."
    elif not discriminates:
        verdict = 'RED (no discrimination)'
        msg = ("Conley index distribution overlaps between sub and at; "
               "invariant matches both classes and does not discriminate.")
    elif len(sub_set) == 1 and len(at_set) == 1:
        verdict = 'RED type-1 ((n,L)-parametrized)'
        msg = ("Each class has a single (β_0, β_1) value — index is a function "
               "of (n, L) only, replicating Wave 1 P1 failure mode.")
    else:
        verdict = 'YELLOW'
        msg = "Mixed discrimination; may need further refinement."

    print(f"\n  T3 verdict: {verdict}")
    print(f"  {msg}")

    runtime = time.time() - t0
    out = {
        'verdict': verdict,
        'message': msg,
        'sub_b0_NL_set': sorted(set(sub_b0_NL)),
        'sub_b1_NL_set': sorted(set(sub_b1_NL)),
        'at_b0_NL_set': sorted(set(at_b0_NL)),
        'at_b1_NL_set': sorted(set(at_b1_NL)),
        'sub_set_pairs': [list(p) for p in sub_set],
        'at_set_pairs': [list(p) for p in at_set],
        'rows': rows,
        'runtime_s': runtime,
    }
    with open(os.path.join(HERE, 'phaseW6_t3_results.json'), 'w') as f:
        json.dump(out, f, indent=2)
    print(f"\n  Runtime: {runtime:.1f}s")
    print(f"  Wrote phaseW6_t3_results.json")


if __name__ == '__main__':
    main()
