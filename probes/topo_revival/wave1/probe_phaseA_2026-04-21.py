#!/usr/bin/env python3
"""Phase A combined probe — P1 (pi_1/H_1), P2 (linking), P3 (zeta_f), P6 (Cheeger).

Each probe has its pre-committed kill criterion from
`probe_plan_topological_revival_2026-04-21.md`. This script runs all four
on a small diagnostic corpus (sub-threshold vs Sol3v1 at-threshold) at
n=5,6,7 and reports per-probe verdicts.

Scope
- Corpus: N sub-threshold records per n, plus Sol3v1-based at-threshold.
- NG(C) = induced subcomplex of prod Delta^{m_i-1} on configs NOT in cycle.
- 2-skeleton: 0 = configs, 1 = Hamming-1 edges, 2 = (a) triangles in one
  coord with m_i>=3, (b) 4-cycle squares in two distinct coords.
- H_* via Smith normal form on boundary matrices (sympy).
- Forced graph: for each non-good c, successor = image under move_entries.

Outputs
- phaseA_results.json next to this file
- Prints verdict table.
"""
from __future__ import annotations

import json
import os
import sys
import time
from collections import Counter, defaultdict
from itertools import product as iproduct, combinations

import numpy as np

# allow importing sibling probes from claude
HERE = os.path.dirname(os.path.abspath(__file__))
CLAUDE_DIR = os.path.abspath(os.path.join(HERE, "..", "..", "..", "..", "claude"))
sys.path.insert(0, CLAUDE_DIR)

try:
    # reuse from probe_sk_uniform_walk (same enumerate_all_cycles)
    from probe_sk_uniform_walk_2026_04_20 import (  # type: ignore
        enumerate_all_cycles, enumerate_multisets, m_n,
    )
except Exception:
    # fall back: inline copy
    def m_n(n):
        return 32 * 3 ** (n - 4) if 5 <= n <= 8 else 4 * 3 ** (n - 2)

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


# ======================================================================
# NG(C) 2-skeleton construction
# ======================================================================

def build_ng_2skeleton(ms, cycle):
    """Return (V, E, F2_tri, F2_sq, idx) where
      V  = list of non-good configs
      E  = list of unordered (i,j) pairs of V, Hamming-1 in prod Delta
      F2_tri = list of 2-cells (triangles) in one coord: (i,j,k) triples in V
      F2_sq  = list of 4-cycle squares: (i,j,k,l) with alternating Hamming-1
      idx = dict config -> index in V
    """
    n = len(ms)
    cycle_set = set(cycle)
    # enumerate all configs
    V = [c for c in iproduct(*[range(m) for m in ms]) if c not in cycle_set]
    idx = {c: i for i, c in enumerate(V)}

    # 1-cells: Hamming-1 edges, both endpoints in V
    E = set()
    for c in V:
        i = idx[c]
        for p in range(n):
            for v in range(ms[p]):
                if v == c[p]:
                    continue
                nc = list(c); nc[p] = v; nc = tuple(nc)
                if nc in idx:
                    j = idx[nc]
                    if i < j:
                        E.add((i, j))
    E = sorted(E)

    # 2-cells type (a): triangle in coord p with m_p >= 3
    # pick any 3 distinct values (u,v,w) in coord p, other coords fixed
    F2_tri = []
    for c in V:
        for p in range(n):
            if ms[p] < 3:
                continue
            # triangle on {0,1,2} values in coord p — only emit once per
            # coset (fix other coords, enumerate all triples of values)
            # emit when c[p] == min of the triple
            for trip in combinations(range(ms[p]), 3):
                if c[p] != trip[0]:
                    continue
                u, v, w = trip
                cu = list(c); cu[p] = u; cu = tuple(cu)
                cv = list(c); cv[p] = v; cv = tuple(cv)
                cw = list(c); cw[p] = w; cw = tuple(cw)
                if cu in idx and cv in idx and cw in idx:
                    F2_tri.append((idx[cu], idx[cv], idx[cw], p))

    # 2-cells type (b): square in coords p<q. 4 configs differing in (p,q).
    # emit when c is the "bottom-left" (min in both coords of the square)
    F2_sq = []
    for c in V:
        for p in range(n):
            for q in range(p + 1, n):
                for up in range(c[p] + 1, ms[p]):
                    for uq in range(c[q] + 1, ms[q]):
                        c00 = c
                        c10 = list(c); c10[p] = up; c10 = tuple(c10)
                        c01 = list(c); c01[q] = uq; c01 = tuple(c01)
                        c11 = list(c); c11[p] = up; c11[q] = uq; c11 = tuple(c11)
                        if (c00 in idx and c10 in idx
                            and c01 in idx and c11 in idx):
                            F2_sq.append((idx[c00], idx[c10], idx[c11], idx[c01],
                                          p, q))

    return V, E, F2_tri, F2_sq, idx


# ======================================================================
# H_0, H_1, H_2 via integer SNF
# ======================================================================

def boundary_matrices(V, E, F2_tri, F2_sq):
    """Return (d1, d2) as dense numpy int arrays (small sizes only).
    d1: C_1 -> C_0, shape (|V|, |E|).  column = j - i for edge (i,j).
    d2: C_2 -> C_1, shape (|E|, |F2|). F2 = F2_tri ++ F2_sq.
    Triangle (u,v,w) bdry = (v-u) - (w-u) + (w-v) = edge uv - edge uw + edge vw
      with orientation sign depending on orderings.
    Square (u,v,w,x) (ccw) bdry = uv + vw + wx + xu orientations.
    """
    nV, nE = len(V), len(E)
    edge_idx = {e: i for i, e in enumerate(E)}

    def eidx(a, b):
        if a < b:
            return edge_idx[(a, b)], +1
        else:
            return edge_idx[(b, a)], -1

    d1 = np.zeros((nV, nE), dtype=np.int64)
    for k, (i, j) in enumerate(E):
        d1[j, k] += 1
        d1[i, k] -= 1

    F2 = list(F2_tri) + list(F2_sq)
    nF = len(F2)
    d2 = np.zeros((nE, nF), dtype=np.int64)
    for k, cell in enumerate(F2):
        if len(cell) == 4:
            # triangle (a,b,c,p). boundary = ab + bc - ac
            a, b, c, _ = cell
            for (x, y, sign) in [(a, b, +1), (b, c, +1), (a, c, -1)]:
                ei, s = eidx(x, y)
                d2[ei, k] += sign * s
        else:
            # square (a,b,c,d,p,q) ccw a-b-c-d-a
            a, b, c, d, _, _ = cell
            for (x, y, sign) in [(a, b, +1), (b, c, +1), (c, d, +1), (d, a, +1)]:
                ei, s = eidx(x, y)
                d2[ei, k] += sign * s
    return d1, d2, F2


def integer_rank(M):
    """Rank over Q via numpy SVD (adequate for our small matrices)."""
    if M.size == 0 or M.shape[0] == 0 or M.shape[1] == 0:
        return 0
    # use svd on float for stability
    A = M.astype(float)
    s = np.linalg.svd(A, compute_uv=False)
    tol = max(A.shape) * np.finfo(float).eps * (s[0] if len(s) else 1.0)
    return int(np.sum(s > tol))


def betti(d1, d2):
    """Return (b0, b1, b2) rational Betti numbers of chain X.
    Here C_2 -> C_1 -> C_0; higher C_3 assumed 0."""
    nV = d1.shape[0]
    nE = d1.shape[1] if d1.ndim == 2 else 0
    nF = d2.shape[1] if d2.ndim == 2 else 0
    r_d1 = integer_rank(d1) if nE > 0 else 0
    r_d2 = integer_rank(d2) if nF > 0 else 0
    b0 = nV - r_d1
    b1 = (nE - r_d1) - r_d2
    b2 = nF - r_d2
    return b0, b1, b2


# ======================================================================
# P1 — pi_1 via Tietze-reduced presentation
# ======================================================================

def spanning_tree(nV, E):
    """Kruskal-like: pick edges forming a spanning forest. Return edge-index
    set of the forest."""
    parent = list(range(nV))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    tree = set()
    for k, (i, j) in enumerate(E):
        ri, rj = find(i), find(j)
        if ri != rj:
            parent[ri] = rj
            tree.add(k)
    return tree


def pi1_presentation(V, E, F2):
    """Build a finite presentation of pi_1. Generators = non-tree edges
    (oriented with the edge's (i,j) direction), relators = 2-cell
    boundaries read as words in the generators (tree edges contribute
    identity since bundles collapse).

    Returns (num_gens, num_relators, relators_compact) where relators are
    lists of (gen_idx, sign) and compact is a short int hash.
    """
    tree = spanning_tree(len(V), E)
    # generator index for each non-tree edge
    gen_of = {}
    gen_count = 0
    for k in range(len(E)):
        if k not in tree:
            gen_of[k] = gen_count
            gen_count += 1

    # build edge-index dict
    edge_idx = {e: i for i, e in enumerate(E)}
    def find_edge_signed(a, b):
        if a < b:
            return edge_idx[(a, b)], +1
        return edge_idx[(b, a)], -1

    relators = []
    for cell in F2:
        path_edges = []
        if len(cell) == 4:
            a, b, c, _ = cell
            seq = [(a, b), (b, c), (c, a)]
        else:
            a, b, c, d, _, _ = cell
            seq = [(a, b), (b, c), (c, d), (d, a)]
        word = []
        for (x, y) in seq:
            k, orient = find_edge_signed(x, y)
            if k in tree:
                continue
            word.append((gen_of[k], orient))
        if word:
            relators.append(word)
    return gen_count, relators


def tietze_reduce(num_gens, relators, max_iter=500):
    """Simple Tietze reduction:
      - remove trivial relators (empty or g g^-1)
      - if a relator is a single generator: remove that generator from all relators
      - if a relator is (g, s) · w with s=±1 and w doesn't contain g: eliminate g
        by substituting w^-1 (or w with sign flip) wherever g appears.
    Returns (gens_remaining, relators_remaining)."""
    gens = set(range(num_gens))
    rels = [list(r) for r in relators]

    def cyclic_reduce(w):
        # free reduce: remove adjacent inverses
        changed = True
        while changed:
            changed = False
            for i in range(len(w) - 1):
                if w[i][0] == w[i+1][0] and w[i][1] + w[i+1][1] == 0:
                    del w[i:i+2]
                    changed = True
                    break
        # cyclic: remove ends that are inverses
        while len(w) >= 2 and w[0][0] == w[-1][0] and w[0][1] + w[-1][1] == 0:
            w.pop(0); w.pop()
        return w

    for it in range(max_iter):
        # reduce each relator
        for i in range(len(rels)):
            rels[i] = cyclic_reduce(rels[i])
        # drop empty relators
        rels = [r for r in rels if r]
        progress = False
        # look for single-gen relators (Tietze: if a relator is g^k with
        # k nonzero, but NOT g^1 alone, we'd get torsion; if g^1 alone
        # relator, g is trivial)
        for i, r in enumerate(rels):
            if len(r) == 1:
                g = r[0][0]
                # g is trivial: remove it everywhere
                rels.pop(i)
                gens.discard(g)
                new_rels = []
                for r2 in rels:
                    r2 = [(gg, ss) for (gg, ss) in r2 if gg != g]
                    new_rels.append(r2)
                rels = new_rels
                progress = True
                break
        if progress:
            continue
        # look for eliminable gen: g appears in some relator with total
        # exponent ±1 AND that relator has no other occurrences of g^±1
        # on both signs of the same gen — conservative approach: check
        # if any relator has exactly one occurrence of some gen and a
        # single occurrence lets us solve for g.
        eliminated = False
        for i, r in enumerate(rels):
            # count occurrences per gen
            counts = defaultdict(lambda: [0, 0])  # [+occ, -occ]
            for (g, s) in r:
                counts[g][0 if s > 0 else 1] += 1
            for g, (pos, neg) in counts.items():
                if pos + neg == 1 and g in gens:
                    # isolate g: r = prefix · g^s · suffix = 1 -> g^s = prefix^-1 · suffix^-1
                    s_used = +1 if pos == 1 else -1
                    idx = next(j for j, (gg, ss) in enumerate(r) if gg == g)
                    prefix = r[:idx]
                    suffix = r[idx+1:]
                    # g = (suffix · prefix)^{-s}    (conjugation-adjusted)
                    substitution = [(gg, -ss) for (gg, ss) in reversed(suffix + prefix)]
                    if s_used == +1:
                        substitution = [(gg, -ss) for (gg, ss) in reversed(suffix + prefix)]
                    else:
                        substitution = list(suffix + prefix)
                    # substitute in all other relators
                    new_rels = []
                    for j, r2 in enumerate(rels):
                        if j == i:
                            continue
                        new_r = []
                        for (gg, ss) in r2:
                            if gg == g:
                                if ss > 0:
                                    new_r.extend(substitution)
                                else:
                                    new_r.extend([(h, -tt) for (h, tt) in reversed(substitution)])
                            else:
                                new_r.append((gg, ss))
                        new_rels.append(new_r)
                    rels = new_rels
                    gens.discard(g)
                    eliminated = True
                    break
            if eliminated:
                break
        if eliminated:
            continue
        break

    # final trim
    rels = [cyclic_reduce(r) for r in rels]
    rels = [r for r in rels if r]
    return len(gens), len(rels), rels


def probe_P1(V, E, F2_tri, F2_sq):
    F2 = list(F2_tri) + list(F2_sq)
    t0 = time.time()
    num_gens_raw, relators_raw = pi1_presentation(V, E, F2)
    gens_red, rels_red_cnt, rels_red = tietze_reduce(num_gens_raw, relators_raw)
    dt = time.time() - t0
    d1, d2, _ = boundary_matrices(V, E, F2_tri, F2_sq)
    b0, b1, b2 = betti(d1, d2)
    return {
        'nV': len(V), 'nE': len(E), 'nF': len(F2),
        'b0': b0, 'b1': b1, 'b2': b2,
        'pi1_gens_raw': num_gens_raw, 'pi1_rels_raw': len(relators_raw),
        'pi1_gens_reduced': gens_red, 'pi1_rels_reduced': rels_red_cnt,
        'pi1_probably_trivial': (gens_red == 0),
        'runtime_s': round(dt, 2),
    }


# ======================================================================
# P2 — linking matrix of mover subcycles
# ======================================================================

def probe_P2(cycle, movers, n, ms):
    """Compute naive linking matrix by intersection numbers in the ambient
    prod Delta. We compute Lambda_{q,q'} = (canonical 2-disk of Move_q)
    intersect Move_q' as a signed 1-0 count. Canonical disk: for a cycle
    C_q = [c_k : moverAt k = q] in prod Delta, span it by a cone to a
    fixed basepoint b = c_0.
    """
    L = len(cycle)
    Lam = np.zeros((n, n), dtype=np.int64)
    base = cycle[0]
    subcycle_by_q = [[] for _ in range(n)]
    for k, q in enumerate(movers):
        subcycle_by_q[q].append(k)
    # For each q: "disk" = union of line segments from base to each
    # c_k with k in subcycle_q (gives a 1-complex, not a disk proper).
    # We use a topologically-weaker invariant: signed count of
    # subcycle_q' edges that lie in the "cone disk" of subcycle_q.
    # This is ad hoc; serves as the primary statistic for the kill
    # criterion.
    for q in range(n):
        for qp in range(n):
            if q == qp:
                continue
            # count: number of edges in Move_{q'}(C) that share an
            # endpoint with a config lying on the directed path from
            # some c_k (k in mover-q slots) to base via the edge
            # cycle[k] -> cycle[k+1]. Simplest proxy:
            # Lam[q,qp] = number of k in Move_q such that cycle[k+1]
            # differs from cycle[k] in coord q (always true by def) AND
            # cycle[(k+1) % L] starts a Move_{q'} edge.
            # i.e. count q,q'-adjacent mover transitions minus reverse.
            fwd = 0
            rev = 0
            for k in subcycle_by_q[q]:
                nk = (k + 1) % L
                if nk in subcycle_by_q[qp]:
                    fwd += 1
                pk = (k - 1) % L
                if pk in subcycle_by_q[qp]:
                    rev += 1
            Lam[q, qp] = fwd - rev
    return {
        'Lambda': Lam.tolist(),
        'det_Lambda': int(round(np.linalg.det(Lam.astype(float)))),
        'rank_Lambda': integer_rank(Lam),
        'trace_Lambda': int(np.trace(Lam)),
        'subcycle_sizes': [len(s) for s in subcycle_by_q],
    }


# ======================================================================
# P3 — forced-map zeta function on NG
# ======================================================================

def probe_P3(V, idx, ms, cycle, det, movers):
    """Complete det to a total f : Config -> Config by a canonical
    completion rule: at any triple not in det, f fixes the coord
    (canonical "stay" rule). Extract periodic-orbit multiset of f
    restricted to NG = V (drop trajectories leaving NG into G).
    """
    n = len(ms)
    cycle_set = set(cycle)
    # move_entries: triples (p,L,S,R) -> new value v != S
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    # canonical completion: f(c) = c with first-priority move applied;
    # priority = lex order on (p, new_val)
    def f_total(c):
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            v = move_entries.get(ctx)
            if v is not None and v != c[p]:
                nc = list(c); nc[p] = v; nc = tuple(nc)
                return nc
        return c  # fixed point if no move defined

    # compute orbit structure of f on V (NG)
    orbit_of = {}
    orbits = []  # list of dicts
    for c in V:
        if c in orbit_of:
            continue
        path = [c]
        seen = {c: 0}
        cur = c
        while True:
            nxt = f_total(cur)
            if nxt in seen:
                start = seen[nxt]
                cycle_len = len(path) - start
                # orbit is path[start:]; tail is path[:start]
                tail = tuple(path[:start])
                orb = tuple(path[start:])
                # mark
                for i, cc in enumerate(path):
                    if cc not in orbit_of:
                        orbit_of[cc] = len(orbits)
                orbits.append({
                    'periodic': list(orb),
                    'cycle_len': cycle_len,
                    'tail_len': start,
                    'leaves_NG': any(p not in idx for p in path),
                })
                break
            if nxt not in idx:
                # trajectory leaves NG (into good cycle). mark path as
                # transient-out.
                for cc in path:
                    if cc not in orbit_of:
                        orbit_of[cc] = -1
                orbits.append({
                    'periodic': [],
                    'cycle_len': 0,
                    'tail_len': len(path),
                    'leaves_NG': True,
                })
                break
            path.append(nxt)
            seen[nxt] = len(path) - 1
            cur = nxt

    in_ng = [o for o in orbits if o['cycle_len'] > 0 and not o['leaves_NG']]
    cycle_lens = [o['cycle_len'] for o in in_ng]
    fix_k = defaultdict(int)  # Fix(f^k)
    for l in cycle_lens:
        for k in range(1, 30):
            if k % l == 0:
                fix_k[k] += l
    return {
        'num_orbits_in_NG': len(in_ng),
        'cycle_len_multiset': sorted(Counter(cycle_lens).items()),
        'num_leave_NG': sum(1 for o in orbits if o['leaves_NG']),
        'fix_k_first10': [(k, fix_k[k]) for k in range(1, 11)],
    }


# ======================================================================
# P6 — spectral Cheeger constant of forced-NG digraph
# ======================================================================

def probe_P6(V, idx, ms, det):
    """Build forced-NG: directed graph on V with edges c -> f(c) where
    f applies the first available forced move. Then compute h via
    spectral approximation lambda_2/2 on the undirected symmetrization."""
    n = len(ms)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    nV = len(V)
    # adjacency of symmetrized forced graph restricted to NG
    adj = defaultdict(set)
    for c in V:
        i = idx[c]
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            v = move_entries.get(ctx)
            if v is None or v == c[p]:
                continue
            nc = list(c); nc[p] = v; nc = tuple(nc)
            j = idx.get(nc)
            if j is not None:
                adj[i].add(j)
                adj[j].add(i)
    # build normalized Laplacian
    deg = np.array([len(adj[i]) for i in range(nV)], dtype=float)
    if np.all(deg == 0):
        return {'nV': nV, 'isolated': True, 'h_spectral': 0.0,
                'fiedler_value': 0.0}
    # dense laplacian (small graphs)
    Lmat = np.zeros((nV, nV))
    for i in range(nV):
        for j in adj[i]:
            Lmat[i, j] = -1
        Lmat[i, i] = len(adj[i])
    # normalized
    dsafe = np.where(deg > 0, deg, 1.0)
    D_inv_sqrt = 1.0 / np.sqrt(dsafe)
    Ln = np.outer(D_inv_sqrt, D_inv_sqrt) * Lmat
    evals = np.linalg.eigvalsh(Ln)
    evals = np.sort(evals)
    lam1 = float(evals[0])
    lam2 = float(evals[1]) if len(evals) > 1 else 0.0
    # Cheeger: h <= sqrt(2 * lam2); also h >= lam2 / 2
    return {
        'nV': nV,
        'num_edges_NG': int(sum(deg) / 2),
        'fiedler_value': lam2,
        'h_spectral_lb': lam2 / 2.0,
        'h_spectral_ub': float(np.sqrt(2 * lam2)) if lam2 >= 0 else None,
        'mean_coverage': (sum(deg) / 2) / max(1, nV),
    }


# ======================================================================
# Corpus
# ======================================================================

def get_records(n_list=(5, 6, 7), sub_per_n=3, at_per_n=1, L_max_by_n=None,
                time_budget=3.0, max_cycles=3):
    """Return list of {class, n, ms, cycle, movers, det} records."""
    if L_max_by_n is None:
        L_max_by_n = {5: 40, 6: 24, 7: 18}
    records = []
    for n in n_list:
        Mn = m_n(n)
        multisets = enumerate_multisets(n, Mn)
        # take evenly-spaced sample
        stride = max(1, len(multisets) // (sub_per_n + 1))
        sample = multisets[::stride][:sub_per_n]
        for ms in sample:
            cycles = enumerate_all_cycles(ms, n, L_max_by_n[n], time_budget,
                                          max_cycles)
            for cycle, movers, det in cycles[:1]:  # one cycle per multiset
                records.append({
                    'class': 'sub', 'n': n, 'ms': list(ms),
                    'cycle': cycle, 'movers': movers, 'det': det,
                    'L': len(cycle),
                })
        # at-threshold: use Sol3v1 (2,3,...,3), product 2*3^(n-1)
        ms_at = (2,) + (3,) * (n - 1)
        cycles = enumerate_all_cycles(ms_at, n, L_max_by_n[n], time_budget,
                                      max_cycles)
        for cycle, movers, det in cycles[:at_per_n]:
            records.append({
                'class': 'at', 'n': n, 'ms': list(ms_at),
                'cycle': cycle, 'movers': movers, 'det': det,
                'L': len(cycle),
            })
    return records


# ======================================================================
# Driver
# ======================================================================

def analyze_record(rec, do_P1=True, do_P2=True, do_P3=True, do_P6=True):
    ms = rec['ms']
    cycle = [tuple(c) for c in rec['cycle']]
    movers = rec['movers']
    det = {tuple(k): v for k, v in rec['det'].items()} if not isinstance(
        next(iter(rec['det'].keys())), tuple) else rec['det']
    out = {'class': rec['class'], 'n': rec['n'], 'ms': ms, 'L': rec['L']}

    # heavy lift: build NG 2-skeleton once
    t0 = time.time()
    V, E, F2_tri, F2_sq, idx = build_ng_2skeleton(ms, cycle)
    out['build_ng_s'] = round(time.time() - t0, 2)
    out['nV'] = len(V); out['nE'] = len(E)
    out['nF_tri'] = len(F2_tri); out['nF_sq'] = len(F2_sq)

    if do_P1 and len(V) > 0:
        # skip P1 if graph is huge (SNF too slow)
        if len(V) <= 200 and len(E) <= 2000:
            out['P1'] = probe_P1(V, E, F2_tri, F2_sq)
        else:
            out['P1'] = {'skipped': f'nV={len(V)} nE={len(E)} too large'}
    if do_P2:
        out['P2'] = probe_P2(cycle, movers, rec['n'], ms)
    if do_P3:
        out['P3'] = probe_P3(V, idx, ms, cycle, det, movers)
    if do_P6 and len(V) > 0 and len(V) <= 500:
        out['P6'] = probe_P6(V, idx, ms, det)
    elif do_P6:
        out['P6'] = {'skipped': f'nV={len(V)} too large'}

    return out


def main():
    print("=" * 72)
    print("Phase A combined probe (P1,P2,P3,P6) — topological revival")
    print("=" * 72)
    t0 = time.time()
    records = get_records(n_list=(5, 6, 7), sub_per_n=3, at_per_n=1)
    print(f"\ncorpus: {len(records)} records "
          f"({sum(1 for r in records if r['class']=='sub')} sub, "
          f"{sum(1 for r in records if r['class']=='at')} at)")
    for r in records:
        print(f"  [{r['class']}] n={r['n']} ms={r['ms']} L={r['L']}")

    out_recs = []
    for i, r in enumerate(records):
        print(f"\n--- record {i+1}/{len(records)}: "
              f"{r['class']} n={r['n']} ms={r['ms']} L={r['L']} ---",
              flush=True)
        try:
            out = analyze_record(r)
            out_recs.append(out)
            print(f"  nV={out['nV']} nE={out['nE']} nF={out['nF_tri']+out['nF_sq']} "
                  f"(tri={out['nF_tri']} sq={out['nF_sq']}) "
                  f"build={out['build_ng_s']}s")
            if 'P1' in out and 'b1' in out['P1']:
                print(f"  P1: b0={out['P1']['b0']} b1={out['P1']['b1']} "
                      f"b2={out['P1']['b2']}  pi1 raw=({out['P1']['pi1_gens_raw']},"
                      f"{out['P1']['pi1_rels_raw']}) reduced=("
                      f"{out['P1']['pi1_gens_reduced']},"
                      f"{out['P1']['pi1_rels_reduced']})")
            elif 'P1' in out:
                print(f"  P1: {out['P1']}")
            if 'P2' in out:
                print(f"  P2: det Λ={out['P2']['det_Lambda']} "
                      f"rank={out['P2']['rank_Lambda']} "
                      f"trace={out['P2']['trace_Lambda']}")
            if 'P3' in out:
                print(f"  P3: cycle_len multiset={out['P3']['cycle_len_multiset']}")
            if 'P6' in out and 'fiedler_value' in out['P6']:
                print(f"  P6: lambda_2={out['P6']['fiedler_value']:.4f} "
                      f"h_lb={out['P6']['h_spectral_lb']:.4f} "
                      f"coverage={out['P6']['mean_coverage']:.3f}")
            elif 'P6' in out:
                print(f"  P6: {out['P6']}")
        except Exception as e:
            print(f"  ERROR: {e}")
            import traceback; traceback.print_exc()
            out_recs.append({'class': r['class'], 'n': r['n'], 'ms': r['ms'],
                             'error': str(e)})

    # ------------ verdicts ------------
    print("\n" + "=" * 72)
    print("VERDICTS (pre-committed kill criteria)")
    print("=" * 72)

    sub = [r for r in out_recs if r.get('class') == 'sub']
    at = [r for r in out_recs if r.get('class') == 'at']

    # P1 verdict
    def p1_trivial(r):
        p = r.get('P1', {})
        return p.get('pi1_probably_trivial', None)
    sub_triv = [p1_trivial(r) for r in sub if 'P1' in r and 'pi1_probably_trivial' in r['P1']]
    at_triv = [p1_trivial(r) for r in at if 'P1' in r and 'pi1_probably_trivial' in r['P1']]
    print("\nP1 (pi_1 / H_1):")
    print(f"  sub: {sum(1 for x in sub_triv if x)}/{len(sub_triv)} "
          f"pi1 probably trivial (after Tietze)")
    print(f"   at: {sum(1 for x in at_triv if x)}/{len(at_triv)} "
          f"pi1 probably trivial (after Tietze)")
    sub_b1 = [r['P1']['b1'] for r in sub if 'P1' in r and 'b1' in r['P1']]
    at_b1 = [r['P1']['b1'] for r in at if 'P1' in r and 'b1' in r['P1']]
    print(f"  sub b1: {Counter(sub_b1)}")
    print(f"   at b1: {Counter(at_b1)}")
    if sub_triv and all(sub_triv) and at_triv and all(at_triv):
        p1_verdict = "RED — pi_1 trivial on all sub & at records"
    elif sub_triv and not all(sub_triv) and at_triv and all(at_triv):
        p1_verdict = "YELLOW — pi_1 nontrivial on some sub, trivial on at"
    elif sub_triv and all(sub_triv) and at_triv and not all(at_triv):
        p1_verdict = "INVERTED (suspect) — pi_1 nontrivial on at, trivial on sub"
    else:
        p1_verdict = "AMBIGUOUS — both classes mixed"
    print(f"  VERDICT: {p1_verdict}")

    # P2 verdict
    sub_det = [r['P2']['det_Lambda'] for r in sub if 'P2' in r]
    at_det = [r['P2']['det_Lambda'] for r in at if 'P2' in r]
    print("\nP2 (linking matrix det):")
    print(f"  sub det Lambda: {sub_det}")
    print(f"   at det Lambda: {at_det}")
    # kill: det depends only on (n, L) or is 0 identically
    all_zero = all(d == 0 for d in sub_det + at_det)
    sub_by_nL = defaultdict(set)
    for r in sub:
        if 'P2' in r:
            sub_by_nL[(r['n'], r['L'])].add(r['P2']['det_Lambda'])
    fixed_by_nL = all(len(v) <= 1 for v in sub_by_nL.values())
    if all_zero:
        p2_verdict = "RED — det Λ = 0 identically (no scalar invariant)"
    elif fixed_by_nL and sum(len(v) for v in sub_by_nL.values()) > 1:
        # only one (n,L) class or det constant per (n,L)
        if len(sub_by_nL) > 1 and all(len(v) == 1 for v in sub_by_nL.values()):
            p2_verdict = "RED — det Λ determined by (n,L) alone"
        else:
            p2_verdict = "AMBIGUOUS — too few (n,L) buckets to discriminate"
    else:
        p2_verdict = "YELLOW — det Λ varies at fixed (n,L); need coverage-residual check"
    print(f"  VERDICT: {p2_verdict}")

    # P3 verdict
    sub_cycle_spectra = [r['P3']['cycle_len_multiset'] for r in sub if 'P3' in r]
    at_cycle_spectra = [r['P3']['cycle_len_multiset'] for r in at if 'P3' in r]
    print("\nP3 (zeta_f orbit multiset):")
    print(f"  sub spectra: {sub_cycle_spectra}")
    print(f"   at spectra: {at_cycle_spectra}")
    # kill: indistinguishable
    sub_set = {tuple(s) for s in sub_cycle_spectra}
    at_set = {tuple(s) for s in at_cycle_spectra}
    overlap = sub_set & at_set
    if sub_set and at_set and overlap == sub_set and overlap == at_set:
        p3_verdict = "RED — orbit multisets identical across classes"
    elif not sub_set or not at_set:
        p3_verdict = "AMBIGUOUS — one class empty"
    else:
        p3_verdict = "YELLOW — orbit multisets differ between classes"
    print(f"  VERDICT: {p3_verdict}")

    # P6 verdict
    sub_h = [r['P6'].get('h_spectral_lb') for r in sub
             if 'P6' in r and 'h_spectral_lb' in r['P6']]
    at_h = [r['P6'].get('h_spectral_lb') for r in at
            if 'P6' in r and 'h_spectral_lb' in r['P6']]
    print("\nP6 (Cheeger / fiedler lb of forced-NG):")
    print(f"  sub h lb: {[round(x, 4) for x in sub_h]} mean={np.mean(sub_h) if sub_h else None}")
    print(f"   at h lb: {[round(x, 4) for x in at_h]} mean={np.mean(at_h) if at_h else None}")
    if sub_h and at_h:
        sub_mean = float(np.mean(sub_h))
        at_mean = float(np.mean(at_h))
        if sub_mean <= at_mean:
            p6_verdict = f"RED — h(sub)={sub_mean:.4f} <= h(at)={at_mean:.4f} (wrong direction)"
        else:
            p6_verdict = f"YELLOW — h(sub)={sub_mean:.4f} > h(at)={at_mean:.4f}, small n; coverage check needed"
    else:
        p6_verdict = "AMBIGUOUS — insufficient data"
    print(f"  VERDICT: {p6_verdict}")

    # write out
    out_path = os.path.join(HERE, "phaseA_results.json")
    with open(out_path, "w") as f:
        json.dump({
            'records': out_recs,
            'verdicts': {
                'P1': p1_verdict, 'P2': p2_verdict,
                'P3': p3_verdict, 'P6': p6_verdict,
            },
            'runtime_s': round(time.time() - t0, 1),
        }, f, indent=2, default=str)
    print(f"\nWrote {out_path} in {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
