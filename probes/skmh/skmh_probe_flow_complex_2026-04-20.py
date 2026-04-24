#!/usr/bin/env python3
"""SKMH Exploration 8 — forced-graph flow complex.

Six probes on state-space topology failed to discriminate ms. Pivoting.

FLOW COMPLEX K_f(ms, C):
  0-cells: NG(C) configs (non-cycle configurations)
  1-cells: directed forced-move edges (c, c') where det(C) forces c -> c'
             at some position p (i.e., (p, c[L p], c[p], c[R p]) ∈ det(C))
  2-cells: commuting non-adjacent squares — pairs (p, q) with |p-q|>1 (mod n)
             where det is defined at c for both p and q, and the resulting
             configurations share the common corner c'''.

This complex ENCODES DET(C). Its topology sees:
  - which NG configs are "forced-reachable" under det (β_0)
  - whether the forced moves themselves form loops / higher structure (β_1+)
  - directly ms-sensitive because det(C)'s coverage of NG depends on ms.

E8 probe: compute β_0, β_1 of K_f on 18 cycles; see if it discriminates.

Key tension: det(C) at sub-threshold ms may fail to cover NG well (few
forced edges → many β_0 components → signal). At at-threshold, det(C)
covers better (β_0 = 1 or small).
"""
from __future__ import annotations
import importlib.util
import os
import sys
import time
from collections import defaultdict
import numpy as np

sys.setrecursionlimit(100000)

_HERE = os.path.dirname(os.path.abspath(__file__))
_CLAUDE = os.path.normpath(
    os.path.join(_HERE, "..", "..", "..", "claude"))
spec = importlib.util.spec_from_file_location(
    "probe_a",
    os.path.join(
        _CLAUDE,
        "probe_sk_hamming1_empty_discriminator_2026-04-17.py"))
probe_a = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe_a)
enumerate_cycles_multistart = probe_a.enumerate_cycles_multistart


def M_n_sharp(n):
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def build_flow_complex(ms, cycle, det):
    """Build the forced-graph flow complex.

    Returns (ng_vertices, edges, squares) where
      ng_vertices: list of NG config tuples
      edges: list of (i, j) for undirected edge between ng_vertices[i], [j]
             (dedup'd; only includes edges where both endpoints in NG)
      squares: list of (i0, i1, i2, i3) where i0-i1-i3-i2-i0 forms
               a commuting square via det at non-adjacent positions
    """
    n = len(ms)
    cycle_set = set(tuple(c) for c in cycle)
    ng_configs = []
    idx = {}
    for c in _iter_configs(ms):
        if c not in cycle_set:
            idx[c] = len(ng_configs)
            ng_configs.append(c)

    # det is a dict (p, L, S, R) -> value; forced move at c position p exists
    # iff that key ∈ det and det[key] != c[p] (move, not stay).
    # We count stays separately (they are "self-loops" — skip for complex).
    def forced_targets(c):
        out = {}  # p -> c'
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in det:
                newv = det[key]
                if newv == c[p]:
                    continue
                nc = list(c)
                nc[p] = newv
                nc = tuple(nc)
                out[p] = nc
        return out

    # 1-cells: (i, j) with i < j; edges where one endpoint has a forced move
    # leading to the other. Undirected.
    edge_set = set()
    forced_cache = {}
    for c in ng_configs:
        ft = forced_targets(c)
        forced_cache[c] = ft
        i = idx[c]
        for p, nc in ft.items():
            if nc in idx:
                j = idx[nc]
                a, b = (i, j) if i < j else (j, i)
                if a != b:
                    edge_set.add((a, b))
    edges = sorted(edge_set)

    # 2-cells: commuting non-adjacent squares.
    # (c, c', c'', c''') with c -p-> c', c -q-> c'', c' -q-> c''', c'' -p-> c'''
    # require |p-q| > 1 mod n (non-adjacent), all four configs in NG.
    squares = []
    square_set = set()
    for c in ng_configs:
        ft = forced_cache[c]
        plist = sorted(ft.keys())
        for a in range(len(plist)):
            for b in range(a + 1, len(plist)):
                p = plist[a]
                q = plist[b]
                # non-adjacent check (on ring Z/n)
                dd = min((p - q) % n, (q - p) % n)
                if dd <= 1:
                    continue
                cp = ft[p]
                cq = ft[q]
                if cp not in forced_cache or cq not in forced_cache:
                    continue
                # c' -q-> ?
                ft_cp = forced_cache[cp]
                ft_cq = forced_cache[cq]
                if q not in ft_cp or p not in ft_cq:
                    continue
                c_pq = ft_cp[q]
                c_qp = ft_cq[p]
                if c_pq != c_qp or c_pq not in idx:
                    continue
                sq = tuple(sorted([idx[c], idx[cp], idx[cq], idx[c_pq]]))
                if sq in square_set:
                    continue
                square_set.add(sq)
                squares.append(sq)
    return ng_configs, edges, squares


def _iter_configs(ms):
    """Yield all configs of ms."""
    import itertools
    for c in itertools.product(*[range(m) for m in ms]):
        yield tuple(c)


def flow_betti(ng_configs, edges, squares):
    """Compute β_0, β_1 of the 2-complex (vertices, edges, squares).

    Treat vertices, 1-cells, 2-cells.  Use ∂_1 : C_1 → C_0 and ∂_2 : C_2
    → C_1 with standard orientations (edges: tail-head, squares: four
    boundary edges summed with signs).
    """
    V = len(ng_configs)
    E = len(edges)
    F = len(squares)
    edge_idx = {e: k for k, e in enumerate(edges)}

    if V == 0:
        return {"V": 0, "E": E, "F": F, "beta_0": 0, "beta_1": 0}
    d1 = np.zeros((V, E), dtype=np.int64)
    for k, (a, b) in enumerate(edges):
        d1[a, k] -= 1
        d1[b, k] += 1

    r1 = int(np.linalg.matrix_rank(d1.astype(np.float64))) if E > 0 else 0

    if F == 0:
        r2 = 0
    else:
        d2 = np.zeros((E, F), dtype=np.int64)
        for k, sq in enumerate(squares):
            # sq is sorted 4-tuple of vertex indices; boundary = sum of
            # the 4 edges with alternating orientation. For a generic
            # CW 2-cell on 4 vertices, we need to know the edge order.
            # Since sq is sorted, we use a canonical boundary: the
            # boundary edges of a square (a, b, c, d) are {a-b, b-c,
            # c-d, d-a}.  We'll take the 4 pairs and find them.
            a, b, c, d = sq
            perim = [(a, b), (b, c), (c, d), (d, a)]
            # canonicalize each as sorted pair; missing edges = square
            # not actually filled in our model; skip them.
            signs = [+1, +1, -1, -1]  # alternate, arbitrary consistent
            for sign, (u, v) in zip(signs, perim):
                key = (u, v) if u < v else (v, u)
                if key in edge_idx:
                    actual_sign = sign if u < v else -sign
                    d2[edge_idx[key], k] += actual_sign
        r2 = int(np.linalg.matrix_rank(d2.astype(np.float64)))

    beta_0 = V - r1
    beta_1 = E - r1 - r2
    return {
        "V": V, "E": E, "F": F,
        "rank_d1": r1, "rank_d2": r2,
        "beta_0": beta_0, "beta_1": beta_1,
    }


def run_multiset(n, ms, prod, max_cycles=2):
    threshold = M_n_sharp(n)
    tag = ("sub" if prod < threshold
           else "at" if prod == threshold else "super")
    L_max = 3 * n + 6
    cycles = enumerate_cycles_multistart(
        ms, n, L_min=6, L_max=L_max,
        time_budget=30.0, max_cycles=max_cycles)
    results = []
    for i, (cyc, movers, det) in enumerate(cycles):
        t0 = time.time()
        ng, edges, squares = build_flow_complex(ms, cyc, det)
        bt = flow_betti(ng, edges, squares)
        dt = time.time() - t0
        print(f"[E8] ms={ms} n={n} tag={tag} L={len(cyc)} cyc{i}:")
        print(f"    V={bt['V']} E={bt['E']} F={bt['F']}  "
              f"β_0={bt['beta_0']} β_1={bt['beta_1']}  "
              f"|det|={len(det)}  ({dt:.2f}s)")
        results.append({
            "n": n, "ms": ms, "prod": prod, "tag": tag,
            "L": len(cyc), "V": bt["V"], "E": bt["E"], "F": bt["F"],
            "beta_0": bt["beta_0"], "beta_1": bt["beta_1"],
            "det_size": len(det),
        })
    return results


def main():
    prod_ms = [
        (5, (2, 2, 2, 2, 2), 32),
        (5, (2, 2, 2, 2, 3), 48),
        (5, (2, 2, 2, 3, 3), 72),
        (5, (2, 2, 3, 3, 3), 108),
        (5, (2, 2, 2, 3, 4), 96),
        (5, (3, 3, 3, 3, 3), 243),
        (6, (2, 2, 2, 2, 3, 3), 144),
        (6, (2, 2, 2, 3, 3, 3), 216),
        (6, (2, 2, 2, 3, 3, 4), 288),
    ]
    all_results = []
    for n, ms, prod in prod_ms:
        print(f"\n[E8] === ms={ms} n={n} ∏={prod} "
              f"(M_n*={M_n_sharp(n)}) ===")
        res = run_multiset(n, ms, prod, max_cycles=2)
        all_results.extend(res)

    print("\n[E8] ===== SUMMARY =====")
    print(f"{'ms':<18} {'tag':<5} {'L':>3} {'|det|':>6} "
          f"{'V':>5} {'E':>5} {'F':>4} {'β_0':>4} {'β_1':>4} "
          f"{'E/V':>6}")
    for r in all_results:
        print(f"{str(r['ms']):<18} {r['tag']:<5} {r['L']:>3} "
              f"{r['det_size']:>6} "
              f"{r['V']:>5} {r['E']:>5} {r['F']:>4} "
              f"{r['beta_0']:>4} {r['beta_1']:>4} "
              f"{r['E']/max(r['V'],1):>6.3f}")
    # β_0 discriminator?
    subs = [r for r in all_results if r['tag'] == 'sub']
    ats = [r for r in all_results if r['tag'] == 'at']
    sups = [r for r in all_results if r['tag'] == 'super']
    print(f"\n[E8] β_0 range: sub={[r['beta_0'] for r in subs]}")
    print(f"[E8] β_0 range: at={[r['beta_0'] for r in ats]}")
    print(f"[E8] β_0 range: super={[r['beta_0'] for r in sups]}")
    print(f"\n[E8] β_1 range: sub={[r['beta_1'] for r in subs]}")
    print(f"[E8] β_1 range: at={[r['beta_1'] for r in ats]}")
    print(f"[E8] β_1 range: super={[r['beta_1'] for r in sups]}")
    return all_results


if __name__ == "__main__":
    main()
