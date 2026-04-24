#!/usr/bin/env python3
"""Analyze the topological structure of the bad-config DAG.

Compute topological ranks and look for patterns that might suggest
an analytical convergence proof.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import deque, defaultdict, Counter
from cup2_final_verify import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system


def compute_topo_ranks(ms, fs, good_set, n):
    """Compute topological rank (longest path from sources) for each bad config."""
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(c for c in all_configs if c not in good_set)

    # Build adjacency: c → successors within bad set
    in_deg = {c: 0 for c in bad_set}
    adj = {c: [] for c in bad_set}
    for c in bad_set:
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c)
                lst[i] = new_S
                succ = tuple(lst)
                if succ in bad_set:
                    adj[c].append(succ)
                    in_deg[succ] += 1

    # Kahn's algorithm with rank tracking
    q = deque(c for c in bad_set if in_deg[c] == 0)
    rank = {}
    for c in q:
        rank[c] = 0

    topo_order = []
    while q:
        c = q.popleft()
        topo_order.append(c)
        for s in adj[c]:
            in_deg[s] -= 1
            rank[s] = max(rank.get(s, 0), rank[c] + 1)
            if in_deg[s] == 0:
                q.append(s)

    assert len(topo_order) == len(bad_set), "Not a DAG!"

    # Also compute "out_good" count: how many successors land in good set
    out_good = {}
    for c in bad_set:
        cnt = 0
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c)
                lst[i] = new_S
                succ = tuple(lst)
                if succ in good_set:
                    cnt += 1
        out_good[c] = cnt

    return rank, adj, out_good, bad_set


def frontier_count(c, n):
    count = 0
    for i in range(n):
        if c[i] != c[(i + 1) % n]:
            count += 1
    return count


def privilege_count(c, fs, n):
    cnt = 0
    for i in range(n):
        L = c[(i - 1) % n]
        S = c[i]
        R = c[(i + 1) % n]
        if fs[i](L, S, R) != S:
            cnt += 1
    return cnt


def main():
    print("TOPOLOGICAL STRUCTURE OF BAD-CONFIG DAG")
    print("=" * 90)

    for nv in [5, 6, 7, 8]:
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        rank, adj, out_good, bad_set = compute_topo_ranks(ms, fs, good_set, n)
        max_rank = max(rank.values()) if rank else 0

        print(f"\nn={nv}: {len(bad_set)} bad configs, max rank={max_rank}")

        # Rank distribution
        rank_dist = Counter(rank.values())
        print(f"  Rank distribution: {dict(sorted(rank_dist.items()))}")

        # Privilege count vs rank
        print(f"\n  {'rank':>4} {'count':>5} {'avg_priv':>8} {'avg_front':>9} {'avg_sum':>7} {'avg_outgood':>11}")
        for r in range(min(max_rank + 1, 20)):
            configs_at_rank = [c for c in bad_set if rank[c] == r]
            if not configs_at_rank:
                continue
            avg_priv = sum(privilege_count(c, fs, n) for c in configs_at_rank) / len(configs_at_rank)
            avg_front = sum(frontier_count(c, n) for c in configs_at_rank) / len(configs_at_rank)
            avg_sum = sum(sum(c) for c in configs_at_rank) / len(configs_at_rank)
            avg_og = sum(out_good[c] for c in configs_at_rank) / len(configs_at_rank)
            print(f"  {r:>4} {len(configs_at_rank):>5} {avg_priv:>8.2f} {avg_front:>9.2f} {avg_sum:>7.2f} {avg_og:>11.2f}")

        if max_rank > 20:
            # Show last few ranks
            for r in range(max(max_rank - 3, 20), max_rank + 1):
                configs_at_rank = [c for c in bad_set if rank[c] == r]
                if not configs_at_rank:
                    continue
                avg_priv = sum(privilege_count(c, fs, n) for c in configs_at_rank) / len(configs_at_rank)
                avg_front = sum(frontier_count(c, n) for c in configs_at_rank) / len(configs_at_rank)
                avg_sum = sum(sum(c) for c in configs_at_rank) / len(configs_at_rank)
                avg_og = sum(out_good[c] for c in configs_at_rank) / len(configs_at_rank)
                print(f"  {r:>4} {len(configs_at_rank):>5} {avg_priv:>8.2f} {avg_front:>9.2f} {avg_sum:>7.2f} {avg_og:>11.2f}")

    # Deep dive: look at the LONGEST PATHS in the DAG for n=6
    print("\n\nLONGEST PATH ANALYSIS (n=6)")
    print("-" * 70)
    nv = 6
    ms, fs = build_system(nv)
    n = nv
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    rank, adj, out_good, bad_set = compute_topo_ranks(ms, fs, good_set, n)
    max_rank = max(rank.values())

    # Find a config at max rank and trace its longest path
    max_config = [c for c in bad_set if rank[c] == max_rank][0]
    print(f"Max rank config: {max_config}, rank={max_rank}")
    print(f"Tracing longest path from rank {max_rank} toward sinks:")

    current = max_config
    path = [current]
    while True:
        # Find successor with highest rank (to trace longest path)
        best_succ = None
        best_rank = -1
        best_mover = -1
        for i in range(n):
            L = current[(i - 1) % n]
            S = current[i]
            R = current[(i + 1) % n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(current)
                lst[i] = new_S
                succ = tuple(lst)
                if succ in bad_set and rank.get(succ, -1) > best_rank:
                    best_rank = rank[succ]
                    best_succ = succ
                    best_mover = i
                elif succ in good_set:
                    pass  # skip
        if best_succ is None:
            # All successors go to good set
            break
        path.append(best_succ)
        fc = frontier_count(current, n)
        fc2 = frontier_count(best_succ, n)
        pc = privilege_count(current, fs, n)
        print(f"  {current} →[P{best_mover}]→ {best_succ}  "
              f"front:{fc}→{fc2} priv:{pc}")
        current = best_succ
        if len(path) > 25:
            print("  (truncated)")
            break

    # Where does the last config go?
    print(f"\n  Final: {current}")
    for i in range(n):
        L = current[(i - 1) % n]
        S = current[i]
        R = current[(i + 1) % n]
        new_S = fs[i](L, S, R)
        if new_S != S:
            lst = list(current)
            lst[i] = new_S
            succ = tuple(lst)
            in_good = succ in good_set
            print(f"    P{i}: {current} → {succ} {'(GOOD)' if in_good else '(BAD)'}")

    # Check: do BAD configs with multiple privileges always have at least
    # one successor with strictly lower rank?
    print("\n\nMULTI-PRIVILEGE MONOTONICITY CHECK")
    print("-" * 70)
    for nv in [5, 6, 7, 8]:
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        rank, adj, out_good, bad_set = compute_topo_ranks(ms, fs, good_set, n)

        multi_priv = [c for c in bad_set if privilege_count(c, fs, n) > 1]
        all_decrease = True
        for c in multi_priv:
            min_succ_rank = float('inf')
            for s in adj[c]:
                min_succ_rank = min(min_succ_rank, rank[s])
            # Also check successors in good set (rank = -1 conceptually)
            if out_good[c] > 0:
                min_succ_rank = -1
            if min_succ_rank >= rank[c]:
                all_decrease = False
                print(f"  n={nv}: {c} rank={rank[c]} but min_succ_rank={min_succ_rank}")

        # Also check: for single-privilege bad configs (only one choice)
        single_priv = [c for c in bad_set if privilege_count(c, fs, n) == 1]
        single_decrease = True
        for c in single_priv:
            for s in adj[c]:
                if rank[s] >= rank[c]:
                    single_decrease = False
                    # already know it's a DAG, but let's verify
        print(f"  n={nv}: multi_priv={len(multi_priv)}, all_have_decreasing_succ={all_decrease}, "
              f"single_priv={len(single_priv)}, single_always_decrease={single_decrease}")


if __name__ == "__main__":
    main()
