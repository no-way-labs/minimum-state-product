#!/usr/bin/env python3
"""
CONVERGENCE PROOF 27: LP-based Excursion Potential Search
=========================================================

KEY THEOREM: Full graph is DAG ⟺ Excursion graph is DAG.
(Proof: any cycle in full graph projects to cycle in excursion graph.)

This script uses Linear Programming to search for a potential function
on the excursion graph. For each edge a→a', we need Φ(a) > Φ(a').

Try increasingly complex function forms:
1. Linear: Φ(c) = Σ wⱼ c[j]
2. Quadratic: Φ(c) = Σᵢⱼ wᵢⱼ c[i]c[j] + Σ wⱼ c[j]
3. Indicator: Φ(c) = Σⱼ,v wⱼᵥ [c[j]=v]
4. Pair: Φ(c) = Σⱼ,v,w wⱼᵥw [c[j]=v & c[j+1]=w]

For small n, the excursion graph has few nodes, making LP feasible.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
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

    # Build transitions
    anom_edges = []
    dfc_le0_adj = defaultdict(list)

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
                    if dfc <= 0:
                        dfc_le0_adj[c].append(succ)
                    if cls == "anomalous":
                        anom_edges.append((c, succ, i, dfc))

    anom_sources = set(c for c, _, _, _ in anom_edges)
    anom_targets = set(succ for _, succ, _, _ in anom_edges)

    # Build excursion graph
    target_to_sources = defaultdict(list)
    for b in anom_targets:
        visited = set()
        queue = deque([b])
        visited.add(b)
        while queue:
            node = queue.popleft()
            if node in anom_sources and node != b:
                target_to_sources[b].append(node)
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt)
                    queue.append(nxt)
        if b in anom_sources:
            target_to_sources[b].append(b)

    exc_graph = defaultdict(set)
    for c, succ, i, dfc in anom_edges:
        for src in target_to_sources.get(succ, []):
            exc_graph[c].add(src)

    # Collect all excursion edges as (source, target) pairs
    exc_edges = []
    for a in exc_graph:
        for ap in exc_graph[a]:
            exc_edges.append((a, ap))

    all_exc_nodes = set()
    for a, ap in exc_edges:
        all_exc_nodes.add(a)
        all_exc_nodes.add(ap)
    all_exc_nodes = sorted(all_exc_nodes)
    node_idx = {c: i for i, c in enumerate(all_exc_nodes)}

    print(f"  Excursion graph: {len(all_exc_nodes)} nodes, {len(exc_edges)} edges")

    # ═══════════════════════════════════════════════════════════
    # TEST 1: Linear potential Φ(c) = Σ wⱼ c[j]
    # For each edge (a, a'): Σ wⱼ (a[j] - a'[j]) > 0
    # Check feasibility using Farkas' lemma / simplex
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 1: Linear potential feasibility")

    # Compute difference vectors
    diff_vecs = []
    for a, ap in exc_edges:
        diff = tuple(a[j] - ap[j] for j in range(n))
        diff_vecs.append(diff)

    # Check: is there w such that w · d > 0 for all d in diff_vecs?
    # Equivalent: is the convex cone of {-d : d in diff_vecs} disjoint from
    # the positive orthant? Or: does the system w·d ≥ 1 have a solution?

    # Simple approach: try many candidate weight vectors
    best_violations = len(exc_edges)
    best_weights = None

    # Try weight vectors: axis-aligned, sums, differences
    candidates_w = []
    for j in range(n):
        w = [0] * n
        w[j] = 1
        candidates_w.append(w)
        w2 = [0] * n
        w2[j] = -1
        candidates_w.append(w2)

    # Linear combinations
    for j1 in range(n):
        for j2 in range(j1 + 1, n):
            for s1 in [-1, 1]:
                for s2 in [-1, 1]:
                    w = [0] * n
                    w[j1] = s1
                    w[j2] = s2
                    candidates_w.append(w)

    # Position-weighted
    for k in range(-3, 4):
        candidates_w.append([k * j + 1 for j in range(n)])
        candidates_w.append([j ** 2 + k for j in range(n)])

    for w in candidates_w:
        viol = sum(1 for d in diff_vecs if sum(w[j] * d[j] for j in range(n)) <= 0)
        if viol < best_violations:
            best_violations = viol
            best_weights = w[:]

    print(f"    Best linear: w={best_weights}, violations={best_violations}/{len(exc_edges)}")

    # ═══════════════════════════════════════════════════════════
    # TEST 2: Indicator potential Φ(c) = Σⱼ Σᵥ wⱼᵥ [c[j]=v]
    # This is equivalent to arbitrary function per position
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 2: Indicator potential feasibility")

    # For each config c, compute feature vector:
    # features[c] = [c[0]=0, c[0]=1, c[0]=2, c[1]=0, ..., c[n-1]=2]
    # where c[j]=2 is only for ternary positions

    def indicator_features(c):
        feats = []
        for j in range(n):
            for v in range(ms[j]):
                feats.append(1 if c[j] == v else 0)
        return feats

    n_feats = sum(ms)
    print(f"    Feature dimension: {n_feats}")

    # Compute difference features for each edge
    diff_feats = []
    for a, ap in exc_edges:
        fa = indicator_features(a)
        fap = indicator_features(ap)
        diff_feats.append(tuple(fa[k] - fap[k] for k in range(n_feats)))

    # Try to find weights: simple heuristic search
    # For small n, try random/systematic search
    import random
    random.seed(42)

    best_ind_viol = len(exc_edges)
    best_ind_weights = None

    # Systematic: try each single feature
    for k in range(n_feats):
        for sign in [1, -1]:
            w = [0] * n_feats
            w[k] = sign
            viol = sum(1 for d in diff_feats if sum(w[i] * d[i] for i in range(n_feats)) <= 0)
            if viol < best_ind_viol:
                best_ind_viol = viol
                best_ind_weights = w[:]

    # Try pairs
    for k1 in range(n_feats):
        for k2 in range(k1 + 1, n_feats):
            for s1 in [-1, 1]:
                for s2 in [-1, 1]:
                    w = [0] * n_feats
                    w[k1] = s1
                    w[k2] = s2
                    viol = sum(1 for d in diff_feats if sum(w[i] * d[i] for i in range(n_feats)) <= 0)
                    if viol < best_ind_viol:
                        best_ind_viol = viol
                        best_ind_weights = w[:]

    # Random search
    for _ in range(10000):
        w = [random.randint(-5, 5) for _ in range(n_feats)]
        viol = sum(1 for d in diff_feats if sum(w[i] * d[i] for i in range(n_feats)) <= 0)
        if viol < best_ind_viol:
            best_ind_viol = viol
            best_ind_weights = w[:]
            if viol == 0:
                break

    print(f"    Best indicator: violations={best_ind_viol}/{len(exc_edges)}")
    if best_ind_viol == 0 and best_ind_weights:
        # Decode the weights
        idx = 0
        for j in range(n):
            wvals = []
            for v in range(ms[j]):
                wvals.append(best_ind_weights[idx])
                idx += 1
            print(f"      Position {j}: w({','.join(map(str, wvals))})")

    # ═══════════════════════════════════════════════════════════
    # TEST 3: Pair potential Φ(c) = Σⱼ wⱼ(c[j], c[j+1])
    # Function of adjacent pairs (like fc and Ψ)
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 3: Pair (frontier) potential feasibility")

    def pair_features(c):
        feats = []
        for j in range(n):
            j1 = (j + 1) % n
            for v1 in range(ms[j]):
                for v2 in range(ms[j1]):
                    feats.append(1 if c[j] == v1 and c[j1] == v2 else 0)
        return feats

    n_pair_feats = sum(ms[j] * ms[(j + 1) % n] for j in range(n))
    print(f"    Pair feature dimension: {n_pair_feats}")

    diff_pair_feats = []
    for a, ap in exc_edges:
        fa = pair_features(a)
        fap = pair_features(ap)
        diff_pair_feats.append(tuple(fa[k] - fap[k] for k in range(n_pair_feats)))

    # Random search for pair weights
    best_pair_viol = len(exc_edges)

    for _ in range(50000):
        w = [random.randint(-5, 5) for _ in range(n_pair_feats)]
        viol = sum(1 for d in diff_pair_feats
                   if sum(w[i] * d[i] for i in range(n_pair_feats)) <= 0)
        if viol < best_pair_viol:
            best_pair_viol = viol
            if viol == 0:
                print(f"    FOUND pair potential with 0 violations!")
                break

    print(f"    Best pair: violations={best_pair_viol}/{len(exc_edges)}")

    # ═══════════════════════════════════════════════════════════
    # TEST 4: Direct node potential via LP relaxation
    # Assign a real number Φ(c) to each excursion node
    # such that Φ(a) > Φ(a') for all edges.
    # This ALWAYS works if the graph is a DAG (just use rank).
    # But can we find a potential that GENERALIZES across n?
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 4: Excursion DAG rank analysis")

    # Compute excursion rank
    in_deg = {v: 0 for v in all_exc_nodes}
    for a in exc_graph:
        for b in exc_graph[a]:
            in_deg[b] = in_deg.get(b, 0) + 1

    q = deque(v for v in all_exc_nodes if in_deg[v] == 0)
    topo = []
    while q:
        v = q.popleft()
        topo.append(v)
        for w_v in exc_graph.get(v, set()):
            in_deg[w_v] -= 1
            if in_deg[w_v] == 0:
                q.append(w_v)

    exc_rank = {}
    for v in reversed(topo):
        exc_rank[v] = max((exc_rank[w_v] + 1 for w_v in exc_graph.get(v, set())),
                          default=0)

    exc_depth = max(exc_rank.values()) if exc_rank else 0
    print(f"    Excursion depth: {exc_depth} (2(n-4) = {2*(n-4)})")

    # For each node, output features vs rank
    print(f"\n    Complete excursion graph (rank, config):")
    for r in range(exc_depth, -1, -1):
        nodes_at_r = [v for v in all_exc_nodes if exc_rank[v] == r]
        for v in nodes_at_r[:3]:
            interior = tuple(v[j] for j in range(2, n - 2))
            boundary = (v[0], v[1], v[n - 2], v[n - 1])
            print(f"      rank={r}: {v} int={interior} bnd={boundary}")
        if len(nodes_at_r) > 3:
            print(f"      ... ({len(nodes_at_r) - 3} more at rank {r})")

    # ═══════════════════════════════════════════════════════════
    # TEST 5: Check if rank is determined by interior alone
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 5: Is excursion rank determined by interior?")
    int_to_ranks = defaultdict(set)
    for v in all_exc_nodes:
        interior = tuple(v[j] for j in range(2, n - 2))
        int_to_ranks[interior].add(exc_rank[v])

    determined = all(len(ranks) == 1 for ranks in int_to_ranks.values())
    print(f"    Determined by interior alone: {determined}")
    if not determined:
        for interior, ranks in sorted(int_to_ranks.items()):
            if len(ranks) > 1:
                print(f"      int={interior}: ranks={sorted(ranks)}")

    # ═══════════════════════════════════════════════════════════
    # TEST 6: Does (interior_sorted_desc, boundary) determine rank?
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 6: Rank determined by (interior, fc, Ψ)?")
    ifp_to_ranks = defaultdict(set)
    for v in all_exc_nodes:
        interior = tuple(v[j] for j in range(2, n - 2))
        from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top

        def frontier_type(a, b):
            if a == b: return 0
            return (b - a) % 3
        def w1(j):
            if j == n - 1: return 0
            if j == n - 2: return 1
            return j + 1
        def w2(j):
            if j == n - 1: return 0
            if 1 <= j <= n - 2: return n - 1 - j
            return n - 1
        def psi_v(c):
            total = 0
            for j in range(n):
                ft = frontier_type(c[j], c[(j + 1) % n])
                if ft == 1: total += w1(j)
                elif ft == 2: total += w2(j)
            return total
        fc = sum(1 for j in range(n) if v[j] != v[(j + 1) % n])
        ps = psi_v(v)
        key = (interior, fc, ps)
        ifp_to_ranks[key].add(exc_rank[v])

    determined2 = all(len(ranks) == 1 for ranks in ifp_to_ranks.values())
    print(f"    Determined by (interior, fc, Ψ): {determined2}")
    if not determined2:
        cnt = sum(1 for ranks in ifp_to_ranks.values() if len(ranks) > 1)
        print(f"    Ambiguous keys: {cnt}/{len(ifp_to_ranks)}")


if __name__ == '__main__':
    for nv in range(5, 10):
        prod = 4 * 3 ** (nv - 2)
        if prod > 100000:
            break
        analyze(nv)
