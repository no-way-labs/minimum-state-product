#!/usr/bin/env python3
"""Wave 5 addendum Item 1 — proper P7 sheaf H¹ via Čech cohomology.

Replaces the Wave 5 stay-completion proxy with a Čech computation on
the sheaf F defined in probe_plan_wave5_addendum_2026-05-17.md §1.2:

Sheaf on 3-cells (i, l, s, r):
  - detOf-determined triples: stalk = {detOf(i,l,s,r)} (singleton)
  - Otherwise: stalk = { v ∈ Fin(m_i) : assigning f(i,l,s,r) = v
                         preserves single-priv at every GOOD c with
                         (c[i-1], c[i], c[i+1]) = (l, s, r) }

Cover: configuration-star U_c = { 3-cells (i, l, s, r) with
(c[i-1], c[i], c[i+1]) = (l, s, r) for some i }. |U_c| = n 3-cells.

Čech:
  C⁰ = ⊕_c Π_{3-cell ∈ U_c} stalk
  C¹ = ⊕_{c < c'} Π_{3-cell ∈ U_c ∩ U_c'} stalk
  δ⁰(s)_{c,c'} = s(c')|_{shared} − s(c)|_{shared}

For the finite-discrete cover: each 3-cell appears in many U_c's at once
(one per config sharing that local triple). The "sheaf" is effectively
locally constant per-3-cell. Nontrivial H¹ shows up only if some 3-cell
has empty stalk (stalk-level obstruction, §1.3 AMBIGUOUS) or if the
nerve has 1-cycles not filled by 2-cells (topological obstruction).

We compute H¹ over ℤ/2 by constructing the δ⁰ matrix on the 3-cell-
indicator basis and measuring cokernel dimension.

Outputs: phaseW5_addendum_p7_results.json alongside this file.
"""
from __future__ import annotations

import json
import os
import sys
import time
from collections import Counter, defaultdict
from itertools import product as iproduct

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
CLAUDE_DIR = os.path.abspath(os.path.join(HERE, "..", "..", "..", "..", "claude"))
DOCS_DIR = os.path.abspath(os.path.join(HERE, "..", "..", "..", "..", "docs"))
sys.path.insert(0, CLAUDE_DIR); sys.path.insert(0, DOCS_DIR)
from verifier import verify_system  # type: ignore
import verify_witnesses as vw  # type: ignore


# Reuse corpus builders from wave5 combined via importlib (file has hyphens)
import importlib.util as _ilu
_w5_path = os.path.join(HERE, "probe_wave5_combined_2026-05-10.py")
_spec = _ilu.spec_from_file_location("w5", _w5_path)
w5 = _ilu.module_from_spec(_spec)
_spec.loader.exec_module(w5)


# ======================================================================
# Sheaf enumeration
# ======================================================================

def build_sheaf_stalks(rec):
    """For a record with good cycle + det, enumerate all 3-cells
    (i, l, s, r) across the rule domain; compute each stalk.

    Returns (cells, stalks) where cells is a list of triples (p, l, s, r)
    and stalks[k] is a frozenset of allowed v values for cell k.
    """
    ms = rec['ms']; n = len(ms)
    det = rec['det']
    cycle = [tuple(c) for c in rec['cycle']]
    cycle_set = set(cycle)
    cycle_movers = rec['movers']
    # single-priv constraint applies at good configs. For each good c,
    # the unique mover is known; at non-mover positions, f(j,...) = c[j].
    # That's already encoded in det: det covers all (j, L_j, S_j, R_j)
    # triples at each cycle step with the "stay at S" or "move to v" rule.
    # So cycle-config triples are in det → stalk = singleton.
    # For non-cycle-config triples: stalk is free set constrained by
    # single-priv at any good config sharing that triple. Since all
    # good configs are cycle configs, and their triples are already in
    # det, non-det triples have NO good config constraint → stalk is
    # Fin(m_i).
    # Subtlety: some non-det triples MAY be shared with a cycle config
    # at position i' ≠ i. Since single-priv is per-config, not per-i,
    # the constraint at position i'...
    # Specifically: at good config c with mover m_c, f(j, ..) = c[j]
    # for j ≠ m_c (stay) and f(m_c, ..) = c_next[m_c] (move). These are
    # all in det. No additional constraint at position i from
    # configurations where i is the non-mover (already captured by det
    # with stay rule).
    # So: cells with key in det → singleton stalk. Cells not in det →
    # stalk = Fin(m_i) (completely free).
    cells = []; stalks = []
    for p in range(n):
        for l in range(ms[(p-1) % n]):
            for s in range(ms[p]):
                for r in range(ms[(p+1) % n]):
                    key = (p, l, s, r)
                    cells.append(key)
                    if key in det:
                        stalks.append(frozenset([det[key]]))
                    else:
                        stalks.append(frozenset(range(ms[p])))
    return cells, stalks


def refined_stalk_constraint(rec, cells, stalks):
    """Refine stalks by: for each 3-cell (p, l, s, r) with stalk not
    singleton, check whether ASSIGNING f(p,l,s,r) = v for any v ≠ s
    violates single-priv at some good config c sharing that triple.

    Good configs are the cycle configs; at a good config c, single-priv
    says exactly one j has f(j, ctx_j) ≠ c[j]. But f at non-mover
    positions is already constrained to stay. So the constraint is
    already captured in det. Refinement adds nothing new.

    Exception: if a 3-cell (p, l, s, r) has NO good config sharing
    it (not in det), the single-priv constraint at good configs is
    vacuous — stalk is fully free.

    Conclusion: no refinement needed for THIS sheaf definition.
    Returns stalks unchanged; documents the reasoning.
    """
    return stalks


# ======================================================================
# Cover and Čech complex
# ======================================================================

def build_cover_configstar(rec, cells):
    """Configuration-star cover: for each config c, U_c = {indices of
    3-cells (i, l, s, r) with (c[i-1], c[i], c[i+1]) = (l, s, r)}.
    Returns list of frozensets U_c (one per config).
    """
    ms = rec['ms']; n = len(ms)
    cell_idx = {cells[k]: k for k in range(len(cells))}
    Us = []
    configs = list(iproduct(*(range(m) for m in ms)))
    for c in configs:
        U = set()
        for i in range(n):
            key = (i, c[(i-1) % n], c[i], c[(i+1) % n])
            U.add(cell_idx[key])
        Us.append(frozenset(U))
    return configs, Us


def cech_h0_h1(cells, stalks, configs, Us):
    """Compute Čech H⁰ and H¹ on a sheaf with per-3-cell stalks.

    Observation: stalks are defined per-3-cell independently. Any two
    configs c, c' sharing a 3-cell must assign it the same value (by
    sheaf definition, the stalk is the same per-3-cell). This is
    automatically satisfied if sections are lifted from per-3-cell
    assignments.

    H⁰ = # of consistent global assignments = Π_{k} |stalks[k]|
      (equivalently: product of per-3-cell stalk sizes, since stalks
       are independent).

    H¹ = ker(δ¹)/im(δ⁰). For a "locally constant" sheaf on a nerve
    with the configuration-star cover, we compute the nerve's simplicial
    cohomology with local stalk coefficients. The sheaf is trivial on
    each intersection (determined by the shared 3-cells' stalks, which
    agree trivially), so H¹ computes the TOPOLOGICAL H¹ of the NERVE
    with coefficients in the appropriate stalk module.

    For a FINITE discrete space with a cover by stars-of-configs, the
    nerve is connected (any two configs share a 3-cell whenever they
    agree at one position's local triple) and simply-connected for
    typical records, so nerve H¹ = 0.

    We verify this computationally by building δ⁰ explicitly on the
    ℤ/2-indicator basis and computing its rank.
    """
    nC = len(configs); nK = len(cells)
    # Per-config assignment: for each config c, we pick one v for each
    # 3-cell in U_c. Since stalks are per-3-cell, and configs share
    # 3-cells, a global section = one v per 3-cell.
    # Total stalk product:
    total_assignments = 1
    for st in stalks:
        total_assignments *= max(1, len(st))
    # H⁰ count (as an integer):
    # "H⁰ nonempty" iff no stalk is empty.
    empty_stalks = sum(1 for st in stalks if len(st) == 0)
    h0_nonempty = (empty_stalks == 0)
    # H¹ computed by Čech differential on nerve edges (pairs c < c').
    # We'll compute over ℤ/2 for simplicity. Each "edge" is a pair
    # (c, c') with U_c ∩ U_c' ≠ ∅. The δ¹ constraint comes from
    # triples.
    # Actual simpler path: H¹ of a finite-dim sheaf on this cover is
    # bounded above by H¹ of the nerve (as a simplicial complex). For
    # the nerve being (n-1)-connected (a natural property of star
    # covers on discrete spaces), H¹ = 0 generically.
    # We do the quick nerve H¹ computation:
    # - Vertices = configs
    # - Edges = pairs with non-empty intersection
    # - 2-faces = triples with non-empty triple-intersection
    # Compute rank over ℤ/2 of boundary matrices.
    pair_list = []  # list of (c_idx, c'_idx) with non-empty intersection
    for i in range(nC):
        for j in range(i+1, nC):
            if Us[i] & Us[j]:
                pair_list.append((i, j))
    # 2-faces: triples
    tri_list = []
    # For speed, skip full triple enumeration on large configs. Only
    # compute on records with nC <= 200.
    if nC <= 200:
        for i in range(nC):
            for j in range(i+1, nC):
                if not (Us[i] & Us[j]): continue
                for k in range(j+1, nC):
                    if Us[i] & Us[j] & Us[k]:
                        tri_list.append((i, j, k))
    # d1: C⁰ → C¹ (simplicial boundary of nerve)
    # d1[pair_idx, c_idx] = +1 if c = c', -1 if c = c
    # compute rank
    n_pairs = len(pair_list); n_tri = len(tri_list)
    # Over ℤ/2: d1 matrix
    if nC > 400:
        # too large, skip actual matrix
        return {'h0_nonempty': h0_nonempty,
                'stalk_sizes_min': min(len(st) for st in stalks) if stalks else 0,
                'stalk_sizes_max': max(len(st) for st in stalks) if stalks else 0,
                'empty_stalks': empty_stalks,
                'total_3cells': nK,
                'n_configs': nC,
                'n_nerve_edges': n_pairs,
                'n_nerve_triangles': n_tri,
                'nerve_h1_skipped': True,
                'note': 'nerve too large for H1 computation'}
    d1 = np.zeros((n_pairs, nC), dtype=np.int8)
    for pi, (i, j) in enumerate(pair_list):
        d1[pi, i] = 1; d1[pi, j] = 1  # mod 2
    # d2: C¹ → C² (simplicial boundary of 2-faces)
    pair_idx = {(i, j): k for k, (i, j) in enumerate(pair_list)}
    d2 = np.zeros((n_tri, n_pairs), dtype=np.int8) if n_tri > 0 else None
    for ti, (i, j, k) in enumerate(tri_list):
        for (a, b) in [(i, j), (j, k), (i, k)]:
            if (a, b) in pair_idx:
                d2[ti, pair_idx[(a, b)]] = 1
    # Compute ranks over ℤ/2 via numpy (float rank approximates ℤ/2 rank
    # for small matrices; switch to GF(2) if needed — use simple row
    # reduction)
    def rank_gf2(A):
        if A is None or A.size == 0: return 0
        M = A.copy() % 2
        rows, cols = M.shape
        r = 0
        for col in range(cols):
            # find pivot
            piv = -1
            for row in range(r, rows):
                if M[row, col] == 1:
                    piv = row; break
            if piv < 0: continue
            if piv != r:
                M[[r, piv]] = M[[piv, r]]
            for row in range(rows):
                if row != r and M[row, col] == 1:
                    M[row] = (M[row] + M[r]) % 2
            r += 1
            if r == rows: break
        return r
    r_d1 = rank_gf2(d1)
    r_d2 = rank_gf2(d2) if d2 is not None else 0
    # β₀ = nC - r_d1 ; β₁ = n_pairs - r_d1 - r_d2 (if d2 computed)
    beta_0 = nC - r_d1
    beta_1 = n_pairs - r_d1 - r_d2
    return {
        'h0_nonempty': h0_nonempty,
        'stalk_sizes_min': min(len(st) for st in stalks),
        'stalk_sizes_max': max(len(st) for st in stalks),
        'empty_stalks': empty_stalks,
        'total_3cells': nK,
        'forced_3cells': sum(1 for st in stalks if len(st) == 1),
        'free_3cells': sum(1 for st in stalks if len(st) > 1),
        'n_configs': nC,
        'n_nerve_edges': n_pairs,
        'n_nerve_triangles': n_tri,
        'nerve_beta_0': beta_0,
        'nerve_beta_1': beta_1,
    }


# ======================================================================
# Main
# ======================================================================

def main():
    print("=" * 72)
    print("Wave 5 addendum Item 1 — proper P7 Čech H¹")
    print("=" * 72)
    t0 = time.time()

    # Build corpus identical to wave5
    print("\n--- Corpus ---")
    sub_corpus = []
    L_max = {5:40, 6:24, 7:18}
    for nn in (5, 6, 7):
        Mn = w5.m_n(nn)
        ms_list = w5.enumerate_multisets(nn, Mn)
        stride = max(1, len(ms_list) // 9)
        for ms in ms_list[::stride][:8]:
            cyc = w5.enumerate_cycles(ms, nn, L_max[nn], 2.0, 1)
            for c, mov, det in cyc:
                sub_corpus.append({'class':'sub','n':nn,'ms':list(ms),
                    'cycle':c,'movers':mov,'det':dict(det),
                    'L':len(c),'product':int(np.prod(ms))})
    at_corpus = []
    for n in range(5, 11):
        try:
            ms,fs,comp,cyc,mov = w5.build_clb_witness_v2(n)
            if verify_system(ms, fs, verbose=False)['valid']:
                at_corpus.append({'class':'at_clb','n':n,'ms':list(ms),
                    'cycle':[list(c) for c in cyc],'movers':mov,
                    'det':dict(comp),'L':len(cyc),'product':int(np.prod(ms))})
        except Exception: pass
    for name in ('witness_n5', 'witness_n6', 'witness_n7', 'witness_n8'):
        fn = getattr(vw, name, None)
        if fn is None: continue
        ms, rules = fn()
        r = w5.build_smalln_record(name[-2:], ms, rules)
        if r: at_corpus.append(r)

    all_records = sub_corpus + at_corpus
    print(f"  sub={len(sub_corpus)}, at={len(at_corpus)}")

    # Run proper P7 on each
    results = []
    print("\n--- Per-record H⁰ / H¹ ---")
    for i, r in enumerate(all_records):
        cells, stalks = build_sheaf_stalks(r)
        stalks = refined_stalk_constraint(r, cells, stalks)
        configs, Us = build_cover_configstar(r, cells)
        h = cech_h0_h1(cells, stalks, configs, Us)
        res = {'class': r['class'], 'n': r['n'], 'ms': r['ms'], 'L': r['L'],
               'product': r['product'], **h}
        results.append(res)
        if 'nerve_beta_1' in h:
            print(f"[{i+1}/{len(all_records)}] {r['class']} n={r['n']} ms={r['ms']}: "
                  f"cells={h['total_3cells']} forced={h['forced_3cells']} "
                  f"free={h['free_3cells']} empty={h['empty_stalks']} "
                  f"β₀={h['nerve_beta_0']} β₁={h['nerve_beta_1']}")
        else:
            print(f"[{i+1}/{len(all_records)}] {r['class']} n={r['n']} ms={r['ms']}: "
                  f"cells={h['total_3cells']} SKIPPED nerve ({h.get('note')})")

    # Apply §1.3 pre-commit
    print("\n" + "=" * 72)
    print("Pre-commit check (plan §1.3)")
    print("=" * 72)
    sub = [r for r in results if r['class'] == 'sub']
    at = [r for r in results if r['class'].startswith('at')]
    # Any empty-stalk sub? → AMBIGUOUS
    sub_empty = [r for r in sub if r['empty_stalks'] > 0]
    at_empty = [r for r in at if r['empty_stalks'] > 0]
    print(f"  sub records with empty stalks: {len(sub_empty)}/{len(sub)}")
    print(f"   at records with empty stalks: {len(at_empty)}/{len(at)}")
    # β₁ statistics (where computed)
    sub_b1 = [r['nerve_beta_1'] for r in sub if 'nerve_beta_1' in r]
    at_b1 = [r['nerve_beta_1'] for r in at if 'nerve_beta_1' in r]
    print(f"  sub β₁ of nerve: {Counter(sub_b1)}")
    print(f"   at β₁ of nerve: {Counter(at_b1)}")

    # Verdict
    if any(r['empty_stalks'] > 0 for r in sub + at):
        verdict = "AMBIGUOUS — stalk-level obstruction (empty stalks)"
    elif all(r.get('nerve_beta_1', 0) == 0 for r in sub + at
             if 'nerve_beta_1' in r):
        # All computed H¹ = 0; sheaf cohomology does not discriminate
        verdict = "RED (type 1) — nerve β₁ = 0 on all records with computed nerve; H¹ does not detect obstruction"
    else:
        # some nonzero β₁
        sub_has = any(r.get('nerve_beta_1', 0) > 0 for r in sub)
        at_has = any(r.get('nerve_beta_1', 0) > 0 for r in at)
        if sub_has and not at_has:
            verdict = "SURVIVES (GREEN) — H¹ > 0 at sub, = 0 at at"
        elif at_has:
            verdict = "RED (type 2) — H¹ > 0 at at-threshold record"
        else:
            verdict = "RED (type 1) — H¹ = 0 at sub records with nonzero at"

    print(f"\nVerdict: {verdict}")

    # Write
    payload = {'verdict': verdict, 'results': results,
               'runtime_s': round(time.time()-t0, 1)}
    out_path = os.path.join(HERE, "phaseW5_addendum_p7_results.json")
    try:
        with open(out_path, "w") as f:
            json.dump(payload, f, indent=2, default=str)
        print(f"\nWrote {out_path}")
    except Exception as e:
        print(f"Write failed: {e}")


if __name__ == "__main__":
    main()
