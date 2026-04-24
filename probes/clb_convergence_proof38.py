#!/usr/bin/env python3
"""
CONVERGENCE PROOF 38: Interior Change Boundedness for Zero Edges
==================================================================

KEY QUESTION: For zero-edge excursions (Δint(2,1)=0), are the interior
non-(2,1) pair changes BOUNDED independent of n?

If yes: the zero-edge constraint set is FINITE, and LP feasibility
can be checked once for all n.

REASONING: Zero edges come from boundary-type anomalous firings
(T_bot, T_mid@2, T_high, T_top). The cascade from these firings
propagates through the interior, but:
- The cascade converts values (e.g., 1→1 via copy_L propagation)
- The interior pair changes depend on HOW FAR the cascade reaches
- For longer rings, the cascade might propagate further, changing
  more interior pairs

Let's check if the interior Δ values grow with n or stabilize.
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


def main():
    print("=" * 70)
    print("INTERIOR CHANGE BOUNDEDNESS FOR ZERO EDGES")
    print("=" * 70)

    for n_val in range(6, 12):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        # Compute interior pair changes for zero edges
        pair_names = [(a, b) for a in range(3) for b in range(3)]
        int_ranges = {(a, b): [float('inf'), float('-inf')]
                      for a in range(3) for b in range(3)}

        n_zero = 0
        n_total = len(exc_edges)

        # Max position of change for zero edges
        max_change_pos = 0

        for u, v in exc_edges:
            # Compute interior (2,1) change
            s_u = sum(j for j in range(2, n-2) if u[j] == 2 and u[(j+1) % n] == 1)
            s_v = sum(j for j in range(2, n-2) if v[j] == 2 and v[(j+1) % n] == 1)
            if s_u != s_v:
                continue  # Positive edge

            n_zero += 1

            # For this zero edge: compute interior changes for ALL pairs
            for a, b in pair_names:
                if (a, b) == (2, 1):
                    continue
                delta = 0
                for j in range(2, n-2):
                    d_u = int(u[j] == a and u[(j+1) % n] == b)
                    d_v = int(v[j] == a and v[(j+1) % n] == b)
                    delta += j * (d_u - d_v)
                lo, hi = int_ranges[(a, b)]
                int_ranges[(a, b)] = [min(lo, delta), max(hi, delta)]

            # Check which positions differ between u and v
            for j in range(n):
                if u[j] != v[j]:
                    max_change_pos = max(max_change_pos, j)

        dt = time.time() - t0
        print(f"\nn={n_val}: {n_zero} zero edges / {n_total} total ({dt:.1f}s)")
        print(f"  Max differing position (src vs tgt): {max_change_pos}")
        print(f"  Interior Δ ranges (position-weighted, φ=j):")
        for a, b in pair_names:
            if (a, b) == (2, 1):
                continue
            lo, hi = int_ranges[(a, b)]
            if lo <= hi:
                print(f"    ({a},{b}): [{lo}, {hi}]")

    # ═══════════════════════════════════════════════════════════
    # Also check: what positions differ between src and tgt?
    # ═══════════════════════════════════════════════════════════
    print("\n" + "=" * 70)
    print("POSITION DIFFERENCE ANALYSIS FOR ZERO EDGES")
    print("=" * 70)

    for n_val in [8, 9, 10, 11]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        pos_diff_counts = defaultdict(int)
        n_zero = 0
        max_diff_set_size = 0

        for u, v in exc_edges:
            s_u = sum(j for j in range(2, n-2) if u[j] == 2 and u[(j+1) % n] == 1)
            s_v = sum(j for j in range(2, n-2) if v[j] == 2 and v[(j+1) % n] == 1)
            if s_u != s_v:
                continue
            n_zero += 1

            diff_positions = frozenset(j for j in range(n) if u[j] != v[j])
            n_diff = len(diff_positions)
            max_diff_set_size = max(max_diff_set_size, n_diff)

            # Which positions differ?
            for j in diff_positions:
                pos_diff_counts[j] += 1

        dt = time.time() - t0
        print(f"\nn={n_val}: {n_zero} zero edges ({dt:.1f}s)")
        print(f"  Max positions differing: {max_diff_set_size}")

        # Count by position (relative to boundaries)
        bnd_count = sum(pos_diff_counts.get(j, 0) for j in [0, 1, n-2, n-1])
        near_bnd = sum(pos_diff_counts.get(j, 0) for j in [2, 3, n-3, n-4])
        deep_int = sum(pos_diff_counts.get(j, 0)
                       for j in range(4, n-4))
        print(f"  Position diff distribution:")
        print(f"    Boundary (0,1,n-2,n-1): {bnd_count}")
        print(f"    Near-boundary (2,3,n-3,n-4): {near_bnd}")
        print(f"    Deep interior (4..n-5): {deep_int}")

        # Show per-position
        for j in sorted(pos_diff_counts.keys()):
            label = "bnd" if j in [0, 1, n-2, n-1] else "near" if j in [2, 3, n-3, n-4] else "deep"
            pct = 100 * pos_diff_counts[j] / n_zero if n_zero else 0
            print(f"    pos {j:>2} ({label}): {pos_diff_counts[j]:>7} ({pct:.1f}%)")


if __name__ == '__main__':
    main()
