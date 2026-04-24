#!/usr/bin/env python3
"""SKMH E11 — triple complex topology.

A new object entirely. Most previous probes lived on state-space
(∏Δ^{m_i-1}) or dynamics-graph (forced graph). The triple complex
lives on the RULE-CONSTRAINT SPACE.

Triple: (p, L, S, R) — a local context at position p with L=c[p-1],
S=c[p], R=c[p+1]. Total triples T_total = Σ_p m_{p-1} m_p m_{p+1}.

Triple complex K_T(ms):
  0-cells: all triples
  1-cells: (t, t') where t at position p, t' at position p+1 mod n,
           and t, t' share their context overlap (S_t = L_{t'}, R_t = S_{t'}).
           — "consecutive compatible triples"
  2-cells: chains (t_{p-1}, t_p, t_{p+1}) with overlap consistency between
           consecutive pairs.

NG-triple subcomplex K_T_NG = triples NOT in det(C).
Cycle-triple subcomplex K_T_C = triples IN det(C).

Hypothesis: the interaction between K_T_C and K_T_NG, captured by
H_*(K_T, K_T_NG), might discriminate sub vs at threshold.

Also compute β_0, β_1 of K_T_NG directly — the "extension space
triple graph". If it's ms-sensitive in the LB direction, big win.
"""
from __future__ import annotations
import importlib.util
import itertools
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


def all_triples(ms):
    n = len(ms)
    for p in range(n):
        for L in range(ms[(p - 1) % n]):
            for S in range(ms[p]):
                for R in range(ms[(p + 1) % n]):
                    yield (p, L, S, R)


def consecutive_adj(t, t_next, ms, n):
    """Is (t, t_next) a consecutive-compatible pair?

    t at position p, t_next at position (p+1) mod n. Compatibility:
      S_t = L_{t_next} AND R_t = S_{t_next}.
    """
    p, L, S, R = t
    p2, L2, S2, R2 = t_next
    if p2 != (p + 1) % n:
        return False
    return S == L2 and R == S2


def build_triple_complex(ms, det_keys):
    """Build triple complex restricted to triples NOT in det.

    Returns (ng_triples, edges_ng_only).
    """
    n = len(ms)
    all_t = list(all_triples(ms))
    in_det = set(det_keys)
    ng_triples = [t for t in all_t if t not in in_det]
    idx = {t: k for k, t in enumerate(ng_triples)}
    # Group triples by position for fast adjacency lookup
    by_pos = defaultdict(list)
    for t in ng_triples:
        by_pos[t[0]].append(t)

    edges = set()
    for t in ng_triples:
        p = t[0]
        # look at position p+1 triples
        for t2 in by_pos[(p + 1) % n]:
            if consecutive_adj(t, t2, ms, n):
                i = idx[t]
                j = idx[t2]
                a, b = (i, j) if i < j else (j, i)
                edges.add((a, b))
    return ng_triples, sorted(edges), idx


def betti_01_from_graph(V, edges):
    """β_0, β_1 for undirected graph with V vertices and edge list."""
    parent = list(range(V))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for a, b in edges:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb
    cc = len(set(find(i) for i in range(V)))
    # β_1 = E - V + β_0 for a connected graph; general: = E - (V - CC)
    beta1 = len(edges) - (V - cc)
    return cc, beta1


def cycle_triples(det):
    return list(det.keys())


def run_multiset(n, ms, prod, max_cycles=2):
    threshold = M_n_sharp(n)
    tag = ("sub" if prod < threshold
           else "at" if prod == threshold else "super")
    L_max = 3 * n + 6
    cycles = enumerate_cycles_multistart(
        ms, n, L_min=6, L_max=L_max,
        time_budget=30.0, max_cycles=max_cycles)
    results = []
    T_total = sum(ms[(p - 1) % n] * ms[p] * ms[(p + 1) % n]
                  for p in range(n))
    for i, (cyc, movers, det) in enumerate(cycles):
        # NG-triples complex
        ng_triples, edges_ng, idx_ng = build_triple_complex(
            ms, det_keys=list(det.keys()))
        # Also full triple complex (all triples, for reference)
        full_tr, edges_full, _ = build_triple_complex(ms, det_keys=[])

        cc_ng, b1_ng = betti_01_from_graph(len(ng_triples), edges_ng)
        cc_full, b1_full = betti_01_from_graph(
            len(full_tr), edges_full)

        print(f"[E11] ms={ms} tag={tag} L={len(cyc)} cyc{i} "
              f"|det|={len(det)} T_total={T_total}")
        print(f"      full triple graph: V={len(full_tr)} E={len(edges_full)} "
              f"β_0={cc_full} β_1={b1_full}")
        print(f"      NG triple graph:   V={len(ng_triples)} "
              f"E={len(edges_ng)} β_0={cc_ng} β_1={b1_ng}")
        results.append({
            "n": n, "ms": ms, "prod": prod, "tag": tag, "cyc": i,
            "L": len(cyc), "T_total": T_total, "det_size": len(det),
            "V_full": len(full_tr), "E_full": len(edges_full),
            "b0_full": cc_full, "b1_full": b1_full,
            "V_ng": len(ng_triples), "E_ng": len(edges_ng),
            "b0_ng": cc_ng, "b1_ng": b1_ng,
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
        print(f"\n[E11] === ms={ms} n={n} ∏={prod} "
              f"(M*={M_n_sharp(n)}) ===")
        res = run_multiset(n, ms, prod)
        all_results.extend(res)

    print("\n===== E11 TRIPLE COMPLEX SUMMARY =====")
    print(f"{'ms':<18} {'tag':<5} {'L':>3} {'T_tot':>6} {'|det|':>6} "
          f"{'V_ng':>6} {'b0_ng':>6} {'b1_ng':>6} "
          f"{'b0_full':>8} {'b1_full':>8}")
    for r in all_results:
        print(f"{str(r['ms']):<18} {r['tag']:<5} {r['L']:>3} "
              f"{r['T_total']:>6} {r['det_size']:>6} "
              f"{r['V_ng']:>6} {r['b0_ng']:>6} {r['b1_ng']:>6} "
              f"{r['b0_full']:>8} {r['b1_full']:>8}")

    print("\n===== TAG-GROUPED TRIPLE-NG β_0 =====")
    for tag in ["sub", "at", "super"]:
        entries = [r for r in all_results if r["tag"] == tag]
        if entries:
            vals = [r["b0_ng"] for r in entries]
            print(f"  {tag}: β_0(NG_triples) range = "
                  f"{sorted(set(vals))}, n={len(entries)} cycles")


if __name__ == "__main__":
    main()
