#!/usr/bin/env python3
"""
CONVERGENCE PROOF 53: Double-Zero DAG Verification + Structure
================================================================

BREAKTHROUGH from proof52: The double-zero subgraph (Δint(2,1)=0 AND
Δint(2,0)=0) is a DAG for n=9,10! No pair-count potential can prove this
(LP δ=0), so the DAG property comes from POSITIONAL structure.

This script:
1. Verify double-zero DAG for n=5..12
2. Investigate structure: what ordering makes it a DAG?
3. Check: does the FULL zero-edge subgraph have any cycles?
   (If zero-edges are already a DAG, we don't even need the (2,0) layer!)
4. Characterize the DAG rank function for double-zero edges
"""

import sys
import os
import time
import numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict


def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))


def build_excursion_graph(n_val):
    ms, fs = build_system(n_val)
    n = n_val
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    anom_edges = []
    dfc_le0_adj = defaultdict(list)
    for c in bad_list:
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c); lst[i] = out; succ = tuple(lst)
                if succ in bad_set:
                    dfc = delta_fc(L, S, R, out)
                    if dfc <= 0: dfc_le0_adj[c].append(succ)
                    if out != L and out != R: anom_edges.append((c, succ, i, dfc))

    anom_sources = set(c for c, _, _, _ in anom_edges)
    anom_target_map = defaultdict(list)
    for c, succ, i, dfc in anom_edges:
        anom_target_map[succ].append(c)

    exc_edges = set()
    for b in set(s for _, s, _, _ in anom_edges):
        visited = set(); queue = [b]; visited.add(b); head = 0
        while head < len(queue):
            node = queue[head]; head += 1
            if node in anom_sources:
                for src in anom_target_map.get(b, []):
                    exc_edges.add((src, node))
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt); queue.append(nxt)

    return list(exc_edges), ms


def tarjan_has_cycle(adj, nodes):
    """Return True if directed graph has a cycle (non-trivial SCC)."""
    index_counter = [0]
    stack = []
    on_stack = set()
    index_map = {}
    lowlink = {}

    def strongconnect(v):
        index_map[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)

        for w in adj.get(v, []):
            if w not in index_map:
                result = strongconnect(w)
                if result:
                    return True
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], index_map[w])

        if lowlink[v] == index_map[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                scc.append(w)
                if w == v:
                    break
            if len(scc) > 1:
                return True  # Non-trivial SCC = cycle
        return False

    sys.setrecursionlimit(2000000)
    for node in nodes:
        if node not in index_map:
            if strongconnect(node):
                return True
    return False


def compute_dag_ranks(adj, nodes):
    """Compute DAG rank (longest path to a sink) for each node."""
    # Topological sort + longest path
    in_degree = defaultdict(int)
    for u in adj:
        for v in adj[u]:
            in_degree[v] += 1

    # Find sinks (out-degree 0)
    all_nodes_with_edges = set()
    for u in adj:
        all_nodes_with_edges.add(u)
        for v in adj[u]:
            all_nodes_with_edges.add(v)

    sinks = [v for v in all_nodes_with_edges if v not in adj or len(adj[v]) == 0]

    # BFS from sinks (reverse edges)
    rev_adj = defaultdict(list)
    for u in adj:
        for v in adj[u]:
            rev_adj[v].append(u)

    rank = {}
    queue = list(sinks)
    for s in sinks:
        rank[s] = 0
    head = 0
    while head < len(queue):
        v = queue[head]; head += 1
        for u in rev_adj.get(v, []):
            new_rank = rank[v] + 1
            if u not in rank or new_rank > rank[u]:
                rank[u] = new_rank
                queue.append(u)

    return rank


def interior_pair_deltas(u, v, n):
    delta = {}
    for a in range(3):
        for b in range(3):
            count_u = sum(1 for j in range(2, n-2) if u[j] == a and u[(j+1)%n] == b)
            count_v = sum(1 for j in range(2, n-2) if v[j] == a and v[(j+1)%n] == b)
            delta[(a, b)] = count_v - count_u
    return delta


def main():
    # ═══════════════════════════════════════════════════════════
    # STEP 1: Verify DAG property for zero-edge and double-zero subgraphs
    # ═══════════════════════════════════════════════════════════
    print("=" * 70)
    print("STEP 1: DAG verification for filtered subgraphs")
    print("=" * 70)
    print()
    print(f"{'n':>3} | {'total':>8} | {'zero':>8} | {'dbl-zero':>8} | "
          f"{'zero DAG':>9} | {'dz DAG':>9} | {'time':>5}")
    print("-" * 70)

    for n_val in range(5, 13):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        # Build subgraphs
        adj_zero = defaultdict(list)
        adj_dz = defaultdict(list)
        nodes_zero = set()
        nodes_dz = set()
        n_total = len(exc_edges)

        for u, v in exc_edges:
            deltas = interior_pair_deltas(u, v, n)

            if deltas[(2, 1)] == 0:
                adj_zero[u].append(v)
                nodes_zero.add(u)
                nodes_zero.add(v)

                if deltas[(2, 0)] == 0:
                    adj_dz[u].append(v)
                    nodes_dz.add(u)
                    nodes_dz.add(v)

        n_zero = sum(len(adj_zero[u]) for u in adj_zero)
        n_dz = sum(len(adj_dz[u]) for u in adj_dz)

        # Check for cycles
        zero_dag = not tarjan_has_cycle(adj_zero, nodes_zero) if nodes_zero else True
        dz_dag = not tarjan_has_cycle(adj_dz, nodes_dz) if nodes_dz else True

        dt = time.time() - t0
        print(f"{n_val:>3} | {n_total:>8} | {n_zero:>8} | {n_dz:>8} | "
              f"{'DAG' if zero_dag else 'CYCLE':>9} | "
              f"{'DAG' if dz_dag else 'CYCLE':>9} | {dt:>5.1f}s")

    # ═══════════════════════════════════════════════════════════
    # STEP 2: Investigate DAG structure for zero-edge subgraph
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 2: Zero-edge subgraph DAG analysis")
    print("=" * 70)

    for n_val in [8, 9, 10]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        adj_zero = defaultdict(list)
        nodes_zero = set()
        for u, v in exc_edges:
            deltas = interior_pair_deltas(u, v, n)
            if deltas[(2, 1)] == 0:
                adj_zero[u].append(v)
                nodes_zero.add(u)
                nodes_zero.add(v)

        # Compute DAG ranks
        ranks = compute_dag_ranks(adj_zero, nodes_zero)

        max_rank = max(ranks.values()) if ranks else 0
        n_ranked = len(ranks)

        # Find sinks
        sinks = [v for v in nodes_zero
                 if v not in adj_zero or len(adj_zero[v]) == 0]

        dt = time.time() - t0
        print(f"\n  n={n_val}: {len(nodes_zero)} nodes, "
              f"max_rank={max_rank}, sinks={len(sinks)} ({dt:.1f}s)")

        # Show sink configs
        for s in sorted(sinks)[:5]:
            print(f"    Sink: {s}")

        # Rank distribution
        from collections import Counter
        rank_hist = Counter(ranks.values())
        print(f"    Rank distribution (top 5):")
        for r, count in sorted(rank_hist.items())[:5]:
            print(f"      Rank {r}: {count} configs")
        print(f"      ...")
        for r, count in sorted(rank_hist.items())[-3:]:
            print(f"      Rank {r}: {count} configs")

    # ═══════════════════════════════════════════════════════════
    # STEP 3: What ordering makes zero-edges a DAG?
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 3: Candidate ordering for zero-edge DAG")
    print("=" * 70)

    for n_val in [8, 9, 10]:
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        # Collect zero edges with various candidate orderings
        n_tested = 0
        violations = defaultdict(int)
        total = defaultdict(int)

        for u, v in exc_edges:
            deltas = interior_pair_deltas(u, v, n)
            if deltas[(2, 1)] != 0:
                continue
            n_tested += 1

            # Candidate orderings (decreasing on edges u→v means v < u):

            # 1. Pair of (2,0) count, (0,1) count
            d20_u = sum(1 for j in range(n) if u[j]==2 and u[(j+1)%n]==0)
            d20_v = sum(1 for j in range(n) if v[j]==2 and v[(j+1)%n]==0)
            d01_u = sum(1 for j in range(n) if u[j]==0 and u[(j+1)%n]==1)
            d01_v = sum(1 for j in range(n) if v[j]==0 and v[(j+1)%n]==1)

            total['d20'] += 1
            if d20_v > d20_u: violations['d20'] += 1

            total['d01'] += 1
            if d01_v > d01_u: violations['d01'] += 1

            # 2. (d20, d01) lexicographic
            total['lex_d20_d01'] += 1
            if (d20_v, d01_v) > (d20_u, d01_u): violations['lex_d20_d01'] += 1

            # 3. Hamming distance to sink = (0,0,2,0,...,0)
            sink = tuple([0]*2 + [2] + [0]*(n-3))
            ham_u = sum(1 for j in range(n) if u[j] != sink[j])
            ham_v = sum(1 for j in range(n) if v[j] != sink[j])
            total['hamming'] += 1
            if ham_v > ham_u: violations['hamming'] += 1

            # 4. Sum of values
            sum_u = sum(u)
            sum_v = sum(v)
            total['sum_val'] += 1
            if sum_v > sum_u: violations['sum_val'] += 1

            # 5. Count of 1s (value 1 = anomalous output)
            ones_u = sum(1 for x in u if x == 1)
            ones_v = sum(1 for x in v if x == 1)
            total['count_1'] += 1
            if ones_v > ones_u: violations['count_1'] += 1

            # 6. Position-weighted count of 1s
            pw1_u = sum(j for j in range(n) if u[j] == 1)
            pw1_v = sum(j for j in range(n) if v[j] == 1)
            total['pw_1'] += 1
            if pw1_v > pw1_u: violations['pw_1'] += 1

            # 7. Frontier count
            fc_u = sum(1 for j in range(n) if u[j] != u[(j+1)%n])
            fc_v = sum(1 for j in range(n) if v[j] != v[(j+1)%n])
            total['fc'] += 1
            if fc_v > fc_u: violations['fc'] += 1

            # 8. Config lexicographic
            total['config_lex'] += 1
            if v > u: violations['config_lex'] += 1

            # 9. Number of interior positions differing from dominant boundary
            # Left boundary propagates 0, right boundary propagates 0
            # Interior "anomaly" = not 0 (except position 2 which should be 2)
            anom_u = sum(1 for j in range(2, n-2) if u[j] != 0 and j != 2)
            anom_v = sum(1 for j in range(2, n-2) if v[j] != 0 and j != 2)
            total['interior_anom'] += 1
            if anom_v > anom_u: violations['interior_anom'] += 1

            # 10. Position of leftmost non-zero in interior (excluding pos 2)
            lnz_u = next((j for j in range(3, n-2) if u[j] != 0), n)
            lnz_v = next((j for j in range(3, n-2) if v[j] != 0), n)
            total['leftmost_nz'] += 1
            if lnz_v < lnz_u: violations['leftmost_nz'] += 1  # leftmost moves left = bad

        print(f"\n  n={n_val}: {n_tested} zero edges")
        print(f"  Candidate orderings (violations = v > u):")
        for name in ['d20', 'd01', 'lex_d20_d01', 'hamming', 'sum_val',
                      'count_1', 'pw_1', 'fc', 'config_lex',
                      'interior_anom', 'leftmost_nz']:
            v = violations[name]
            t = total[name]
            pct = 100 * v / t if t > 0 else 0
            marker = "  ← PERFECT" if v == 0 else ""
            print(f"    {name:>20}: {v:>6}/{t} ({pct:>5.1f}%) violations{marker}")

    # ═══════════════════════════════════════════════════════════
    # STEP 4: Check if zero-edge DAG implies proof
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 4: Proof structure if zero-edge subgraph is DAG")
    print("=" * 70)
    print()
    print("If the zero-edge subgraph (Δint(2,1)=0) is a DAG for all n:")
    print("  1. Δfc≤0 subgraph is DAG [PROVED: (fc,Ψ) potential]")
    print("  2. Every cycle needs anomalous edge [PROVED]")
    print("  3. Cycle ↔ excursion graph cycle [PROVED]")
    print("  4a. Δint(2,1) ≥ 0 on all excursion edges [PROVED]")
    print("  4b. Zero-edge subgraph is DAG [TO PROVE]")
    print()
    print("  Then: any excursion cycle must have Δint(2,1)=0 on every edge")
    print("  (because Σ Δint(2,1) = 0 in a cycle, and each term ≥ 0).")
    print("  So the cycle lies entirely in the zero-edge subgraph.")
    print("  But that subgraph is a DAG → contradiction.")
    print()
    print("  This is a COMPLETE proof! No need for (2,0) layer or pair potential!")
    print("  The only gap: prove zero-edge subgraph is DAG for all n.")


if __name__ == '__main__':
    main()
