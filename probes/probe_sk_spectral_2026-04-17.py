#!/usr/bin/env python3
"""Spectral / walk-count lower bound for |SK|.

Each non-trivial SCC contains a closed walk through all its nodes. So:
  sum of (# closed walks of length k in F|_SK)_k captures SCC structure.

Specifically: if F|_SK has adjacency matrix A, then
   trace(A^k) = # closed walks of length k
   rank(A) ≤ |SK|
   number of non-zero eigenvalues ≥ # non-trivial SCCs

For a tighter angle, consider:
  - Iterated forcing: F^k(x) for x ∈ SK cycles through k-many configs.
  - Each forced cycle in F|_SK has length dividing the "period" of F.

Probe:
  - Compute min closed walk length in F|_SK (smallest forced cycle length)
  - For each node in SK, compute its "period" = gcd of closed walk lengths
  - Is min_cycle_length ≥ some value that grows with n?
  - Is sum of (# nodes covered by cycles of length k) ≥ 2^(n-1)?

Also: count "forced orbits" starting from each SK node and see how many
distinct orbits cover SK.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time
import math
import sys
sys.setrecursionlimit(100000)


def enumerate_cycles(ms, n, L_min, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []; seen = set(); t0 = time.time()
    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            if L < L_min: return
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen:
                seen.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max: return
        for p in range(n):
            Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp); forced = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced is not None and forced != new_val: continue
                new_det = dict(det); new_det[km] = new_val; ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si: ok = False; break
                    new_det[ki] = Si
                if not ok: continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path): continue
                dfs(start, nc, new_det, path + [nc], movers + [p])
    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget: break
        dfs(start, start, {}, [start], [])
    return found


def compute_sk_and_adj(ms, n, cycle, det):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n): V[i].add(c[i])
    V_sorted = [sorted(V[i]) for i in range(n)]
    all_configs = list(iproduct(*V_sorted))
    cycle_set = set(cycle)
    non_good = [c for c in all_configs if c not in cycle_set]
    ng_set = set(non_good)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in move_entries:
                nc = list(c); nc[p] = move_entries[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append(nc)
    remaining = set(non_good)
    while True:
        sinks = {c for c in remaining if not any(t in remaining for t in adj.get(c, []))}
        if not sinks: break
        remaining -= sinks
    return remaining, adj, V_sorted


def find_short_cycles_bfs(sk, adj, max_len):
    """Find closed walks in F|_SK of length ≤ max_len starting at each node."""
    min_cycle_len = float('inf')
    cycle_len_histogram = Counter()
    # For each node, BFS to find shortest return
    for start in sk:
        dist = {start: 0}
        frontier = [start]
        level = 0
        while frontier and level < max_len:
            level += 1
            next_frontier = []
            for u in frontier:
                for v in adj.get(u, []):
                    if v not in sk: continue
                    if v == start:
                        cycle_len_histogram[level] += 1
                        if level < min_cycle_len:
                            min_cycle_len = level
                        continue  # don't extend
                    if v not in dist:
                        dist[v] = level
                        next_frontier.append(v)
            frontier = next_frontier
    return min_cycle_len, cycle_len_histogram


def enumerate_simple_cycles(sk, adj, max_len, max_count):
    """Enumerate simple directed cycles in F|_SK up to max_len."""
    cycles_found = []
    sk_list = sorted(sk)
    sk_set = set(sk)
    def dfs(start, cur, path):
        if len(cycles_found) >= max_count: return
        if len(path) > max_len: return
        for nxt in adj.get(cur, []):
            if nxt not in sk_set: continue
            if nxt == start:
                if len(path) >= 1:
                    cycles_found.append(tuple(path))
                continue
            if nxt in path: continue
            dfs(start, nxt, path + (nxt,))
    for start in sk_list[:50]:
        dfs(start, start, (start,))
    return cycles_found


def main():
    print("=" * 100)
    print("SPECTRAL / WALK-COUNT: min forced-cycle length and structure in F|_SK")
    print("=" * 100)

    plan = [
        (5, [(2,2,2,3,3)], 14, 3, 15.0),
        (6, [(2,2,2,3,3,3)], 17, 2, 30.0),
        (7, [(2,2,2,3,3,3,3)], 17, 1, 40.0),
        (8, [(2,2,2,3,3,3,3,3)], 19, 1, 60.0),
    ]

    for n, ms_list, L_max, max_cycles, tb in plan:
        bound = 2 ** (n - 1)
        print(f"\n=== n={n}  bound=2^{n-1}={bound} ===")
        for ms in ms_list:
            cycles = enumerate_cycles(ms, n, L_min=2*n+2, L_max=L_max,
                                      time_budget=tb, max_cycles=max_cycles)
            for ci, (cycle, movers, det) in enumerate(cycles):
                sk, adj, V_sorted = compute_sk_and_adj(ms, n, cycle, det)
                if not sk: continue
                print(f"\n  ms={ms} L={len(cycle)} cycle#{ci}  |SK|={len(sk)}")

                # Shortest cycle length via BFS
                try:
                    min_cycle, cyc_hist = find_short_cycles_bfs(sk, adj, max_len=20)
                    print(f"    min forced-cycle length in F|_SK: {min_cycle}")
                    hist_short = {k: v for k, v in sorted(cyc_hist.items()) if k <= 10}
                    print(f"    cycle-length histogram (k→count at k, k≤10): {hist_short}")
                except Exception as e:
                    print(f"    cycle search error: {e}")

                # Enumerate short simple cycles
                if len(sk) <= 200:
                    try:
                        simple_cycles = enumerate_simple_cycles(sk, adj,
                                                                max_len=min(8, len(sk)), max_count=500)
                        lens = Counter(len(c) for c in simple_cycles)
                        print(f"    simple cycles (starting from first 50 nodes, len ≤ 8): {dict(sorted(lens.items()))}")
                        # Nodes covered by short simple cycles
                        covered = set()
                        for c in simple_cycles:
                            covered.update(c)
                        print(f"    nodes covered by simple cycles (len ≤ 8): {len(covered)}")
                    except Exception as e:
                        print(f"    simple-cycle error: {e}")


if __name__ == "__main__":
    main()
