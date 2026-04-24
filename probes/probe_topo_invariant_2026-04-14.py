#!/usr/bin/env python3
"""Topological invariant probe — step-2 of the research brief.

For each benchmark multiset (sub-threshold tail vs threshold witness),
enumerate candidate full-coverage good cycles, build the determined bad
graph, and compute several invariants per cycle:

  - |non-good| (= state space minus good cycle)
  - determined-edge count in bad graph
  - sink-kernel size + rounds
  - non-trivial SCC count, largest SCC size
  - shortest directed cycle length in the kernel
  - binary-projection bad graph: |V_b|, |E_b|, cycle-space rank
  - fiber-switching edge count (moves at binary vs non-binary positions)
  - cycle-space rank of the raw bad graph (|E|-|V|+components)

Then we aggregate per multiset and ask: is there a scalar that cleanly
separates "tail" (should be obstructed) from "witness" (should survive)?
"""

from collections import defaultdict, deque
import os
import sys
import time

sys.path.insert(0, os.path.dirname(__file__))

from cic_lifting_proof2 import (
    enumerate_cycles,
    build_forced_graph,
    iterative_sink_removal,
    find_sccs,
)


BENCHMARKS = [
    # (label, n, ms, role)
    ("n5_tail",    5, (2, 2, 2, 3, 3),       "tail"),
    ("n6_tail",    6, (2, 2, 2, 3, 3, 3),    "tail"),
    ("n5_witness", 5, (2, 2, 2, 3, 4),       "witness"),
    ("n6_witness", 6, (2, 2, 2, 4, 3, 3),    "witness"),
    ("n7_witness", 7, (3, 2, 2, 2, 3, 4, 3), "witness"),
    # n=8 witness product 2592 > 500 guard; skipped here, noted in report.
]


def binary_positions(ms):
    return [i for i, m in enumerate(ms) if m == 2]


def project_binary(cfg, bpos):
    return tuple(cfg[i] for i in bpos)


def shortest_cycle_in_kernel(kernel, adj):
    """BFS from each kernel node along edges that stay in kernel, return
    shortest cycle length (None if kernel empty)."""
    if not kernel:
        return None
    best = None
    kset = kernel if isinstance(kernel, set) else set(kernel)
    for src in kset:
        # BFS tracking depth; first time we revisit src via in-edge gives cycle length.
        dist = {src: 0}
        q = deque([src])
        found = None
        while q:
            u = q.popleft()
            du = dist[u]
            for v, _ in adj.get(u, []):
                if v not in kset:
                    continue
                if v == src:
                    cand = du + 1
                    if found is None or cand < found:
                        found = cand
                    continue
                if v not in dist:
                    dist[v] = du + 1
                    q.append(v)
        if found is not None:
            if best is None or found < best:
                best = found
    return best


def count_components_undirected(nodes, adj):
    """Underlying-graph components. Edges treated as undirected."""
    und = defaultdict(set)
    for u in nodes:
        for v, _ in adj.get(u, []):
            if v in nodes:
                und[u].add(v)
                und[v].add(u)
    seen = set()
    comps = 0
    for s in nodes:
        if s in seen:
            continue
        comps += 1
        stack = [s]
        while stack:
            x = stack.pop()
            if x in seen:
                continue
            seen.add(x)
            for y in und.get(x, ()):
                if y not in seen:
                    stack.append(y)
    return comps


def compute_invariants(n, ms, cycle, movers, det):
    good_set = set(cycle)
    non_good, non_good_set, adj = build_forced_graph(ms, n, det, good_set)

    V = len(non_good)
    E = sum(len(adj[c]) for c in non_good)

    kernel, rounds, removed = iterative_sink_removal(non_good, adj)
    sccs = find_sccs(list(kernel), adj)
    nt_scc_count = len(sccs)
    largest_scc = max((len(s) for s in sccs), default=0)

    short_cyc = shortest_cycle_in_kernel(kernel, adj)

    # Cycle-space rank of raw bad graph (underlying undirected, multi-edges
    # collapsed).
    comps = count_components_undirected(non_good_set, adj) if V > 0 else 0
    # Count underlying edges once.
    und_edges = 0
    seen_edge = set()
    for u in non_good:
        for v, _ in adj.get(u, []):
            if u == v:
                continue
            key = (u, v) if u < v else (v, u)
            if key in seen_edge:
                continue
            seen_edge.add(key)
            und_edges += 1
    cycle_rank = und_edges - V + comps if V > 0 else 0

    # Binary projection graph.
    bpos = binary_positions(ms)
    proj_V = set()
    proj_E_dir = set()  # directed edges between distinct projections
    fiber_stay = 0
    fiber_switch = 0
    for u in non_good:
        pu = project_binary(u, bpos)
        proj_V.add(pu)
        for v, p in adj.get(u, []):
            pv = project_binary(v, bpos)
            if pu == pv:
                fiber_stay += 1
            else:
                fiber_switch += 1
                proj_E_dir.add((pu, pv))
    bV = len(proj_V)
    bE = len(proj_E_dir)

    # Binary projection underlying components / rank.
    if bV > 0:
        # Build undirected adjacency over projection nodes.
        und_b = defaultdict(set)
        for (u, v) in proj_E_dir:
            und_b[u].add(v)
            und_b[v].add(u)
        seen_b = set()
        bcomps = 0
        for s in proj_V:
            if s in seen_b:
                continue
            bcomps += 1
            stack = [s]
            while stack:
                x = stack.pop()
                if x in seen_b:
                    continue
                seen_b.add(x)
                for y in und_b.get(x, ()):
                    if y not in seen_b:
                        stack.append(y)
        # Undirected edges in projection (distinct unordered pairs).
        und_b_edges = len({tuple(sorted((a, b))) for (a, b) in proj_E_dir if a != b})
        b_cycle_rank = und_b_edges - bV + bcomps
    else:
        b_cycle_rank = 0

    return {
        "cycle_len": len(cycle),
        "movers": len(set(movers)),
        "V": V,
        "E": E,
        "kernel": len(kernel),
        "rounds": rounds,
        "nt_scc": nt_scc_count,
        "largest_scc": largest_scc,
        "short_cyc": short_cyc,
        "fiber_stay": fiber_stay,
        "fiber_switch": fiber_switch,
        "cycle_rank": cycle_rank,
        "bV": bV,
        "bE": bE,
        "b_rank": b_cycle_rank,
    }


def run_benchmark(label, n, ms, role):
    print(f"\n===== {label}  n={n}  ms={ms}  role={role} =====")
    t0 = time.time()
    cycles = enumerate_cycles(ms, n, max_cycles=25, max_time=45.0)
    print(f"enumerate_cycles: {len(cycles)} cycles in {time.time()-t0:.1f}s")
    full = [(c, m, d) for c, m, d in cycles if set(m) == set(range(n))]
    print(f"full-coverage cycles (all procs moved): {len(full)}")

    rows = []
    for idx, (cycle, movers, det) in enumerate(full):
        inv = compute_invariants(n, ms, cycle, movers, det)
        rows.append(inv)

    if not rows:
        print("  (no full-coverage cycles found — cannot compute invariants)")
        return {"label": label, "role": role, "rows": rows}

    def col(key):
        return [r[key] for r in rows]

    def summ(key, fmt="{}"):
        vals = [v for v in col(key) if v is not None]
        if not vals:
            return "n/a"
        return f"min={min(vals)} max={max(vals)} mean={sum(vals)/len(vals):.1f}"

    print(f"  V (non-good):        {summ('V')}")
    print(f"  E (bad edges):       {summ('E')}")
    print(f"  kernel size:         {summ('kernel')}")
    print(f"  rounds to stable:    {summ('rounds')}")
    print(f"  non-triv SCC count:  {summ('nt_scc')}")
    print(f"  largest SCC:         {summ('largest_scc')}")
    print(f"  shortest bad cyc:    {summ('short_cyc')}")
    print(f"  fiber switch:        {summ('fiber_switch')}")
    print(f"  fiber stay:          {summ('fiber_stay')}")
    print(f"  cycle rank (raw):    {summ('cycle_rank')}")
    print(f"  bin proj |V_b|:      {summ('bV')}")
    print(f"  bin proj |E_b|:      {summ('bE')}")
    print(f"  bin proj cyc rank:   {summ('b_rank')}")

    # Count cycles with empty kernel.
    empty_kernel = sum(1 for r in rows if r["kernel"] == 0)
    print(f"  cycles with EMPTY kernel: {empty_kernel} / {len(rows)}")

    return {"label": label, "role": role, "rows": rows}


def main():
    results = []
    for (label, n, ms, role) in BENCHMARKS:
        results.append(run_benchmark(label, n, ms, role))

    print("\n\n========== CROSS-BENCHMARK SUMMARY ==========")
    print(f"{'label':<14}{'role':<10}{'cycs':<6}{'empty_k':<9}"
          f"{'min_k':<7}{'min_scc':<9}{'min_shortc':<12}{'min_brank':<11}")
    for res in results:
        if not res["rows"]:
            print(f"{res['label']:<14}{res['role']:<10}0")
            continue
        rows = res["rows"]
        empty_k = sum(1 for r in rows if r["kernel"] == 0)
        min_k = min(r["kernel"] for r in rows)
        min_scc = min(r["nt_scc"] for r in rows)
        sc_vals = [r["short_cyc"] for r in rows if r["short_cyc"] is not None]
        min_sc = min(sc_vals) if sc_vals else "n/a"
        min_brank = min(r["b_rank"] for r in rows)
        print(f"{res['label']:<14}{res['role']:<10}{len(rows):<6}{empty_k:<9}"
              f"{min_k:<7}{min_scc:<9}{str(min_sc):<12}{min_brank:<11}")

    print("\nKey question per column:")
    print("  empty_k  : does ANY cycle have an empty determined-bad kernel?")
    print("  min_k    : smallest kernel over all enumerated cycles")
    print("  min_scc  : smallest non-triv SCC count over cycles")
    print("  min_sc   : shortest bad cycle length (smaller = tighter recurrence)")
    print("  min_brank: smallest binary-projection cycle-space rank")
    print("A separator would show tails uniformly positive and witnesses")
    print("having at least one cycle with zero or dramatically smaller value.")


if __name__ == "__main__":
    main()
