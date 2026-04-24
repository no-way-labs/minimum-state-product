#!/usr/bin/env python3
"""SKMH E9 + E18 combined.

E9: re-analyze E8 flow-complex β_0 with coverage-normalization.
     Compute β_0 / (coverage-ratio). If all variance is coverage-
     explained, normalized β_0 is uniform. If residual signal remains,
     that residual is LB-direction-relevant.

E18: SCC-level structure of the DIRECTED forced graph.
     Closed SCCs (strongly connected components with no outgoing edges
     to outside the SCC) are exactly SK-witnesses.
     Count: total SCCs, closed SCCs, largest SCC size, topology of
     SCC-quotient graph.
"""
from __future__ import annotations
import importlib.util
import os
import sys
import time
from collections import defaultdict


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


def build_directed_forced(ms, cycle, det):
    """Return (ng_list, edges_directed) — NG configs + (src->dst)
    directed edges from det (not including stay entries)."""
    import itertools
    n = len(ms)
    cycle_set = set(tuple(c) for c in cycle)
    ng = []
    idx = {}
    for c in itertools.product(*[range(m) for m in ms]):
        c = tuple(c)
        if c not in cycle_set:
            idx[c] = len(ng)
            ng.append(c)
    edges = []
    for c in ng:
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in det:
                v = det[key]
                if v == c[p]:
                    continue
                nc = list(c)
                nc[p] = v
                nc = tuple(nc)
                if nc in idx:
                    edges.append((idx[c], idx[nc]))
    return ng, idx, edges


def tarjan_scc(n_nodes, adj):
    """Tarjan's SCC. adj: list of lists of neighbors. Return list of
    SCCs (each SCC is a list of node indices)."""
    idx = [-1] * n_nodes
    lowlink = [0] * n_nodes
    on_stack = [False] * n_nodes
    stack = []
    counter = [0]
    sccs = []

    def strong(v, path):
        idx[v] = counter[0]
        lowlink[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on_stack[v] = True
        for w in adj[v]:
            if idx[w] == -1:
                path.append(('visit', w))
            elif on_stack[w]:
                lowlink[v] = min(lowlink[v], idx[w])
        return

    # iterative version to avoid Python recursion limits
    def tarjan_iter(start):
        if idx[start] != -1:
            return
        work = [(start, iter(adj[start]))]
        idx[start] = counter[0]
        lowlink[start] = counter[0]
        counter[0] += 1
        stack.append(start)
        on_stack[start] = True
        while work:
            v, it = work[-1]
            found_child = False
            for w in it:
                if idx[w] == -1:
                    idx[w] = counter[0]
                    lowlink[w] = counter[0]
                    counter[0] += 1
                    stack.append(w)
                    on_stack[w] = True
                    work.append((w, iter(adj[w])))
                    found_child = True
                    break
                elif on_stack[w]:
                    if idx[w] < lowlink[v]:
                        lowlink[v] = idx[w]
            if not found_child:
                work.pop()
                if work:
                    parent = work[-1][0]
                    if lowlink[v] < lowlink[parent]:
                        lowlink[parent] = lowlink[v]
                if lowlink[v] == idx[v]:
                    scc = []
                    while True:
                        u = stack.pop()
                        on_stack[u] = False
                        scc.append(u)
                        if u == v:
                            break
                    sccs.append(scc)

    for s in range(n_nodes):
        if idx[s] == -1:
            tarjan_iter(s)
    return sccs


def scc_structure(ng, edges):
    """Return dict with SCC counts and classification (closed / open)."""
    V = len(ng)
    adj = [[] for _ in range(V)]
    for a, b in edges:
        adj[a].append(b)
    sccs = tarjan_scc(V, adj)

    scc_of = [0] * V
    for k, scc in enumerate(sccs):
        for v in scc:
            scc_of[v] = k

    # Closed SCCs: no outgoing edge from the SCC to a different SCC
    closed = []
    for k, scc in enumerate(sccs):
        has_outside_edge = False
        scc_set = set(scc)
        for v in scc:
            for w in adj[v]:
                if w not in scc_set:
                    has_outside_edge = True
                    break
            if has_outside_edge:
                break
        if not has_outside_edge:
            closed.append(scc)

    # Closed SCCs where all vertices lack forced-out = sinks in NG
    # (SK witness candidates, if their forced edges stay within scc).
    # Specifically: a closed SCC of size ≥ 1 in which every vertex HAS
    # ≥ 1 forced out-edge (to inside scc) = genuine forced-closed
    # NG subset = SK witness. If scc has size ≥ 1 and no forced edges,
    # it's a "no forced move" config — also SK witness (degenerate).
    forced_closed = []
    for scc in closed:
        scc_set = set(scc)
        all_have_forced = True
        for v in scc:
            if not any(w in scc_set for w in adj[v]):
                if adj[v]:
                    # has edges but all leaving — contradicts closed
                    all_have_forced = False
                    break
                # no edges at all: degenerate SK witness (isolated)
        forced_closed.append(scc)

    sizes = sorted([len(s) for s in sccs], reverse=True)
    closed_sizes = sorted([len(s) for s in closed], reverse=True)
    return {
        "num_sccs": len(sccs),
        "num_closed_sccs": len(closed),
        "largest_scc": sizes[0] if sizes else 0,
        "scc_sizes": sizes[:10],
        "closed_scc_sizes": closed_sizes[:10],
    }


def triples_total(ms):
    n = len(ms)
    return sum(ms[(p - 1) % n] * ms[p] * ms[(p + 1) % n]
               for p in range(n))


def run_multiset(n, ms, prod, max_cycles=2):
    threshold = M_n_sharp(n)
    tag = ("sub" if prod < threshold
           else "at" if prod == threshold else "super")
    L_max = 3 * n + 6
    cycles = enumerate_cycles_multistart(
        ms, n, L_min=6, L_max=L_max,
        time_budget=30.0, max_cycles=max_cycles)
    results = []
    T_tot = triples_total(ms)
    for i, (cyc, movers, det) in enumerate(cycles):
        ng, idx, edges = build_directed_forced(ms, cyc, det)
        scc = scc_structure(ng, edges)
        # E9 coverage normalization
        coverage = len(det) / max(T_tot, 1)
        # undirected connected components via union-find
        parent = list(range(len(ng)))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        def union(a, b):
            ra = find(a)
            rb = find(b)
            if ra != rb:
                parent[ra] = rb

        for a, b in edges:
            union(a, b)
        undirected_cc = len(set(find(i) for i in range(len(ng))))

        norm_undir = undirected_cc / max(coverage, 1e-9)

        print(f"[E9/18] ms={ms} tag={tag} L={len(cyc)} "
              f"|det|={len(det)} T_tot={T_tot} cov={coverage:.3f}")
        print(f"        V={len(ng)} E={len(edges)} "
              f"undir_CC={undirected_cc} (norm/cov={norm_undir:.1f})")
        print(f"        SCCs={scc['num_sccs']} closed={scc['num_closed_sccs']} "
              f"largest={scc['largest_scc']} "
              f"top_sizes={scc['scc_sizes']}")
        results.append({
            "n": n, "ms": ms, "prod": prod, "tag": tag, "cyc": i,
            "L": len(cyc),
            "det_size": len(det),
            "T_tot": T_tot, "coverage": coverage,
            "V": len(ng), "E": len(edges),
            "undir_cc": undirected_cc,
            "norm_undir_cc": norm_undir,
            "num_sccs": scc["num_sccs"],
            "num_closed_sccs": scc["num_closed_sccs"],
            "largest_scc": scc["largest_scc"],
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
        print(f"\n[E9/18] === ms={ms} n={n} ∏={prod} "
              f"(M*={M_n_sharp(n)}) ===")
        res = run_multiset(n, ms, prod)
        all_results.extend(res)

    print("\n===== E9 COVERAGE-NORMALIZED SUMMARY =====")
    print(f"{'ms':<18} {'tag':<5} {'L':>3} {'cov':>6} {'undir_cc':>10} "
          f"{'norm':>8} {'closed_sccs':>12} {'|SK_cand|':>10}")
    for r in all_results:
        sk_cand = r["num_closed_sccs"]  # closed SCCs = SK-style witnesses
        print(f"{str(r['ms']):<18} {r['tag']:<5} {r['L']:>3} "
              f"{r['coverage']:>6.3f} {r['undir_cc']:>10} "
              f"{r['norm_undir_cc']:>8.1f} "
              f"{r['num_closed_sccs']:>12} {sk_cand:>10}")

    print("\n===== TAG-GROUPED CLOSED-SCC STATS =====")
    for tag in ["sub", "at", "super"]:
        entries = [r for r in all_results if r["tag"] == tag]
        if entries:
            vals = [r["num_closed_sccs"] for r in entries]
            print(f"  {tag}: closed_SCCs range = {sorted(set(vals))}, "
                  f"n={len(entries)} cycles, min={min(vals)}, "
                  f"max={max(vals)}, avg={sum(vals)/len(vals):.1f}")


if __name__ == "__main__":
    main()
