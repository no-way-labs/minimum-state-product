#!/usr/bin/env python3
"""
CONVERGENCE PROOF 19: Anomalous Edge Cycle Analysis
====================================================

CROSS-POLLINATION WITH CUP'S FRAMEWORK:
- CUP proved: Δfc≤0 subgraph is a DAG via (fc, Ψ) lexicographic potential.
- Only 4 anomalous entries (out of 45 privileged) have Δfc > 0.
- Question: can the 4 anomalous edges create cycles when combined with
  the Δfc≤0 DAG?

This script:
1. Identifies all anomalous transitions in the bad-config graph
2. For each anomalous transition c→c': checks if c is reachable from c'
   via Δfc≤0 edges (which would create a cycle)
3. Builds the "anomalous excursion graph" and checks for cycles
4. Analyzes (fc, Ψ) values along anomalous excursions
5. Looks for structural reasons why anomalous edges can't create cycles
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import deque, defaultdict


def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))


def classify_entry(L, S, R, out):
    if out == S:
        return "stay"
    if out == L:
        return "copy_L"
    if out == R:
        return "copy_R"
    return "anomalous"


def frontier_type(a, b):
    if a == b:
        return 0
    return (b - a) % 3


def w1(j, n):
    if j == n - 1:
        return 0
    if j == n - 2:
        return 1
    return j + 1


def w2(j, n):
    if j == n - 1:
        return 0
    if 1 <= j <= n - 2:
        return n - 1 - j
    return n - 1


def psi(c, n):
    total = 0
    for j in range(n):
        ft = frontier_type(c[j], c[(j + 1) % n])
        if ft == 1:
            total += w1(j, n)
        elif ft == 2:
            total += w2(j, n)
    return total


def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def analyze(n_val):
    ms, fs = build_system(n_val)
    n = n_val
    result = verify_system(ms, fs)
    assert result['valid']

    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    print(f"\n{'=' * 70}")
    print(f"n = {n_val}: {len(bad_list)} bad configs")
    print(f"{'=' * 70}")

    # Classify all transitions
    anom_edges = []  # anomalous transitions
    dfc_le0_adj = defaultdict(list)  # Δfc≤0 adjacency (for reachability)
    all_edges = []

    for c in bad_list:
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c)
                lst[i] = out
                succ = tuple(lst)
                if succ in bad_set:
                    dfc = delta_fc(L, S, R, out)
                    cls = classify_entry(L, S, R, out)
                    all_edges.append((c, succ, i, dfc, cls))
                    if dfc <= 0:
                        dfc_le0_adj[c].append(succ)
                    if cls == "anomalous":
                        anom_edges.append((c, succ, i, dfc))

    print(f"  Total transitions: {len(all_edges)}")
    print(f"  Δfc≤0 transitions: {sum(1 for _, _, _, d, _ in all_edges if d <= 0)}")
    print(f"  Anomalous transitions: {len(anom_edges)}")

    # ═══════════════════════════════════════════════════════════
    # Q1: Which anomalous entries are used?
    # ═══════════════════════════════════════════════════════════
    anom_types = defaultdict(int)
    for c, succ, i, dfc in anom_edges:
        L = c[(i - 1) % n]
        S = c[i]
        R = c[(i + 1) % n]
        out = succ[i]
        anom_types[(i, L, S, R, out, dfc)] += 1
    print(f"\n  Anomalous entry usage:")
    for (pos, L, S, R, out, dfc), count in sorted(anom_types.items()):
        tname = {0: 'T_bot', 1: 'T_low', n-2: 'T_high', n-1: 'T_top'}.get(pos, 'T_mid')
        print(f"    {tname}(P{pos}): ({L},{S},{R})→{out}, Δfc={dfc:+d}, used {count}x")

    # ═══════════════════════════════════════════════════════════
    # Q2: For each anomalous edge c→c', is c reachable from c'
    #     via Δfc≤0 edges?
    # ═══════════════════════════════════════════════════════════
    # Compute reachability from each anomalous target in Δfc≤0 subgraph
    # This is a BFS from c' restricted to Δfc≤0 edges
    print(f"\n  Q2: Single-anomalous cycle check")
    single_cycles = 0
    for c, succ, i, dfc in anom_edges:
        # BFS from succ in Δfc≤0 subgraph, checking if c is reachable
        visited = set()
        queue = deque([succ])
        visited.add(succ)
        found = False
        while queue and not found:
            node = queue.popleft()
            for nxt in dfc_le0_adj.get(node, []):
                if nxt == c:
                    found = True
                    break
                if nxt not in visited:
                    visited.add(nxt)
                    queue.append(nxt)
        if found:
            single_cycles += 1
            print(f"    CYCLE FOUND: {c} →[anom]→ {succ} →[Δfc≤0]→ ... → {c}")
    print(f"  Single-anomalous cycles: {single_cycles}")

    # ═══════════════════════════════════════════════════════════
    # Q3: Build anomalous excursion graph
    # Vertices: configs that are sources or targets of anomalous edges
    # Edges: c→c' if there's a Δfc≤0 path from c to some config c_a,
    #         then an anomalous edge c_a→c'
    # ═══════════════════════════════════════════════════════════

    # More precisely: for each anomalous edge a→b:
    # - a is an "anomalous source"
    # - b is an "anomalous target"
    # We want to know: from each anomalous target b, which anomalous
    # sources are reachable via Δfc≤0 paths?

    anom_sources = set(c for c, _, _, _ in anom_edges)
    anom_targets = set(succ for _, succ, _, _ in anom_edges)

    print(f"\n  Q3: Anomalous excursion graph")
    print(f"    Anomalous source configs: {len(anom_sources)}")
    print(f"    Anomalous target configs: {len(anom_targets)}")

    # For each anomalous target, BFS to find reachable anomalous sources
    excursion_edges = []  # (target_b, reachable_source_a)
    for b in anom_targets:
        visited = set()
        queue = deque([b])
        visited.add(b)
        reachable_sources = []
        while queue:
            node = queue.popleft()
            if node in anom_sources and node != b:
                reachable_sources.append(node)
                # Don't stop — keep searching for more sources
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt)
                    queue.append(nxt)
        for src in reachable_sources:
            excursion_edges.append((b, src))
        # Also check if b itself is an anomalous source
        if b in anom_sources:
            excursion_edges.append((b, b))

    print(f"    Excursion edges (target → reachable source): {len(excursion_edges)}")

    # Build full excursion graph: anomalous_source → anomalous_target → anomalous_source
    # Anomalous edge: source a → target b
    # Excursion edge: target b → source a' (via Δfc≤0 path)
    # Combined: a → b → a' (one "excursion step")
    # Check for cycles in the excursion graph on anomalous sources

    excursion_graph = defaultdict(set)
    for c, succ, _, _ in anom_edges:
        # c is source, succ is target
        for (b, src) in excursion_edges:
            if b == succ:
                excursion_graph[c].add(src)

    # Check for cycles in excursion_graph using DFS
    color = {c: 0 for c in anom_sources}  # 0=white, 1=gray, 2=black
    has_cycle = False
    for start in anom_sources:
        if color[start] != 0:
            continue
        stack = [(start, False)]
        while stack and not has_cycle:
            node, returning = stack.pop()
            if returning:
                color[node] = 2
                continue
            if color[node] == 1:
                color[node] = 2
                continue
            if color[node] == 2:
                continue
            color[node] = 1
            stack.append((node, True))
            for nxt in excursion_graph.get(node, set()):
                if nxt not in color:
                    color[nxt] = 0
                if color.get(nxt, 0) == 1:
                    has_cycle = True
                    break
                if color.get(nxt, 0) == 0:
                    stack.append((nxt, False))

    print(f"    Excursion graph has cycle: {'YES ✗' if has_cycle else 'NO ✓'}")

    # ═══════════════════════════════════════════════════════════
    # Q4: (fc, Ψ) analysis of anomalous edges
    # ═══════════════════════════════════════════════════════════
    print(f"\n  Q4: (fc, Ψ) values at anomalous edges")
    for c, succ, i, dfc in anom_edges[:15]:
        fc_c = fc(c, n)
        psi_c = psi(c, n)
        fc_s = fc(succ, n)
        psi_s = psi(succ, n)
        print(f"    {c}→{succ}: (fc,Ψ)=({fc_c},{psi_c})→({fc_s},{psi_s}), "
              f"Δfc={dfc:+d}, ΔΨ={psi_s - psi_c:+d}")
    if len(anom_edges) > 15:
        print(f"    ... ({len(anom_edges) - 15} more)")

    # ═══════════════════════════════════════════════════════════
    # Q5: Key structural question: from anomalous target c',
    #     what is the MAXIMUM (fc, Ψ) reachable via Δfc≤0 path?
    #     It must be BELOW the anomalous source's (fc, Ψ).
    # ═══════════════════════════════════════════════════════════
    print(f"\n  Q5: fc/Ψ gap analysis")
    # For each anomalous edge c→c': compute (fc,Ψ) of c and c'.
    # c has (fc_c, Ψ_c). c' has (fc_c', Ψ_c') > (fc_c, Ψ_c) lex.
    # For a cycle: from c', we need to reach some config d with
    # (fc_d, Ψ_d) ≥ (fc_c, Ψ_c) (to then take an anomalous edge
    # from d back to... something).
    # But: from c', all Δfc≤0 paths go DOWNHILL in (fc, Ψ).
    # So (fc_d, Ψ_d) < (fc_c', Ψ_c').
    # The question: can (fc_d, Ψ_d) be high enough to take another
    # anomalous edge that eventually leads back to c?

    # Compute: for each anomalous target, what (fc,Ψ) range is reachable?
    for c, succ, i, dfc in anom_edges[:5]:
        fc_c = fc(c, n)
        psi_c = psi(c, n)
        fc_s = fc(succ, n)
        psi_s = psi(succ, n)

        # BFS from succ, find min and max (fc,Ψ) reachable
        visited = set()
        queue = deque([succ])
        visited.add(succ)
        max_fc = fc_s
        min_fc = fc_s
        reached_sources = []
        while queue:
            node = queue.popleft()
            fn = fc(node, n)
            max_fc = max(max_fc, fn)
            min_fc = min(min_fc, fn)
            if node in anom_sources:
                reached_sources.append((node, fn, psi(node, n)))
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt)
                    queue.append(nxt)

        print(f"    From anom target {succ}: (fc,Ψ)=({fc_s},{psi_s})")
        print(f"      Reachable fc range: [{min_fc}, {max_fc}]")
        print(f"      Reachable anom sources: {len(reached_sources)}")
        if reached_sources:
            for src, f, p in reached_sources[:5]:
                print(f"        → source {src}: (fc,Ψ)=({f},{p})")

    return len(anom_edges), has_cycle


if __name__ == '__main__':
    for nv in range(5, 13):
        prod = 4 * 3 ** (nv - 2)
        if prod > 300000:
            break
        analyze(nv)
