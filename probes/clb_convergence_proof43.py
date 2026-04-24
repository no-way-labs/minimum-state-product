#!/usr/bin/env python3
"""
CONVERGENCE PROOF 43: Iterated Monotonicity Chain
===================================================

KEY INSIGHT: On ALL excursion edges, Δint(2,1) ≥ 0.
On the Δint(2,1)=0 subgraph (zero edges), Δint(2,0) ≥ 0 (from proof38).

QUESTION: On the Δint(2,1)=0 ∧ Δint(2,0)=0 sub-subgraph,
is there ANOTHER monotone interior pair?

If we can find a CHAIN of monotone pairs that eventually exhausts
all edges, we get a lexicographic potential:
  (S₁, S₂, S₃, ...) where Sₖ = position-weighted count of pair k.
Each level is non-increasing, and at least one decreases.

TEST 1: On Δint(2,1)=0 edges, which pairs are monotone?
TEST 2: Restrict to Δint(2,1)=0 ∧ Δint(2,0)=0, find next monotone pair
TEST 3: Continue the chain until all edges are handled
TEST 4: Check if the chain is n-independent (same pair sequence for all n)
"""

import sys
import os
import time
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


def interior_delta(u, v, n, a, b):
    """Position-weighted interior Δ for pair (a,b)."""
    delta = 0
    for j in range(2, n-2):
        d_u = int(u[j] == a and u[(j+1) % n] == b)
        d_v = int(v[j] == a and v[(j+1) % n] == b)
        delta += j * (d_u - d_v)
    return delta


def main():
    pairs = [(a, b) for a in range(3) for b in range(3)]

    print("=" * 70)
    print("ITERATED MONOTONICITY CHAIN")
    print("=" * 70)
    print()

    # For each n, find the chain
    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        # Compute all interior deltas
        edge_deltas = {}
        for u, v in exc_edges:
            deltas = {}
            for a, b in pairs:
                deltas[(a, b)] = interior_delta(u, v, n, a, b)
            edge_deltas[(u, v)] = deltas

        # Start with all edges
        remaining = set((u, v) for u, v in exc_edges)
        chain = []
        level = 0

        while remaining:
            # Find monotone pairs on remaining edges
            monotone = []
            for a, b in pairs:
                if (a, b) in [p for p, _ in chain]:
                    continue  # Already used
                min_d = min(edge_deltas[(u, v)][(a, b)] for u, v in remaining)
                max_d = max(edge_deltas[(u, v)][(a, b)] for u, v in remaining)
                if min_d >= 0:
                    # Count how many edges this eliminates (Δ > 0)
                    n_strict = sum(1 for u, v in remaining
                                   if edge_deltas[(u, v)][(a, b)] > 0)
                    monotone.append(((a, b), n_strict, min_d))

            if not monotone:
                break

            # Choose the one that eliminates the most edges
            monotone.sort(key=lambda x: -x[1])
            best_pair, n_elim, _ = monotone[0]

            # Remove edges with Δ > 0 for this pair
            zero_edges = set()
            for u, v in remaining:
                if edge_deltas[(u, v)][best_pair] == 0:
                    zero_edges.add((u, v))
                elif edge_deltas[(u, v)][best_pair] < 0:
                    # Shouldn't happen since min_d >= 0
                    print(f"    ERROR: negative delta for monotone pair!")
                    break

            n_removed = len(remaining) - len(zero_edges)
            chain.append((best_pair, n_removed))
            remaining = zero_edges
            level += 1

        dt = time.time() - t0
        total = len(exc_edges)
        handled = sum(n_rem for _, n_rem in chain)

        print(f"n={n_val}: {total} edges, chain length={len(chain)}, "
              f"handled={handled}/{total} ({dt:.1f}s)")
        for i, ((a, b), n_rem) in enumerate(chain):
            pct = 100 * n_rem / total if total else 0
            print(f"  Level {i}: Δint({a},{b}) ≥ 0 → "
                  f"eliminates {n_rem} ({pct:.1f}%)")
        if remaining:
            print(f"  REMAINING: {len(remaining)} edges (not handled)")
            # What do the remaining edges look like?
            if len(remaining) <= 20:
                for u, v in list(remaining)[:10]:
                    d = edge_deltas[(u, v)]
                    nonzero = {p: d[p] for p in pairs if d[p] != 0}
                    print(f"    {u} → {v}: {nonzero}")
        else:
            print(f"  ALL EDGES HANDLED — chain is complete!")

    # ═══════════════════════════════════════════════════════════
    # Summary: is the chain n-independent?
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("CHAIN CONSISTENCY CHECK")
    print("=" * 70)
    print()

    # Re-run with focus on the chain ordering
    chains = {}
    for n_val in range(5, 12):
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        edge_deltas = {}
        for u, v in exc_edges:
            deltas = {}
            for a, b in pairs:
                deltas[(a, b)] = interior_delta(u, v, n, a, b)
            edge_deltas[(u, v)] = deltas

        remaining = set((u, v) for u, v in exc_edges)
        chain = []

        while remaining:
            monotone = []
            for a, b in pairs:
                if (a, b) in [p for p, _ in chain]:
                    continue
                min_d = min(edge_deltas[(u, v)][(a, b)] for u, v in remaining)
                if min_d >= 0:
                    n_strict = sum(1 for u, v in remaining
                                   if edge_deltas[(u, v)][(a, b)] > 0)
                    monotone.append(((a, b), n_strict))

            if not monotone:
                break

            monotone.sort(key=lambda x: -x[1])
            best_pair, n_elim = monotone[0]
            zero_edges = set(
                (u, v) for u, v in remaining
                if edge_deltas[(u, v)][best_pair] == 0
            )
            chain.append((best_pair, len(remaining) - len(zero_edges)))
            remaining = zero_edges

        chains[n_val] = [p for p, _ in chain]
        print(f"  n={n_val}: chain = {chains[n_val]}, "
              f"remaining = {len(remaining)}")

    # Check consistency
    print()
    for i in range(max(len(v) for v in chains.values())):
        level_pairs = {}
        for n_val, chain in chains.items():
            if i < len(chain):
                level_pairs[n_val] = chain[i]
        vals = set(level_pairs.values())
        consistent = "CONSISTENT" if len(vals) == 1 else f"VARIES: {vals}"
        print(f"  Level {i}: {level_pairs} — {consistent}")


if __name__ == '__main__':
    main()
