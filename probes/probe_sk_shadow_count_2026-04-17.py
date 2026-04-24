#!/usr/bin/env python3
"""Count shadow cycles in F|_SK: how many distinct L-length closed walks?

Previous finding: min closed-walk length in F|_SK = L. So every forced cycle
has length ≥ L. Simplest case: forced cycles of length EXACTLY L.

Questions:
  (a) How many distinct simple cycles of length L exist in F|_SK?
  (b) Are all SK nodes in at least one length-L cycle?
  (c) If SK nodes are partitioned into length-L cycles, that gives
      |SK| = L × (# cycles).  We'd need (# cycles) ≥ 2^(n-1)/L.

Algorithm: start at each SK node, follow F deterministically (choose any
forced successor at each step — pick lexicographic for reproducibility).
Since min_out ≥ 1 and no short cycles, we enter a length-L cycle eventually.
Record the cycle.

Alternative: do Johnson-style simple-cycle enumeration but capped at length L.
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


def enumerate_simple_cycles_at_length(sk, adj, target_len):
    """Enumerate all simple directed cycles of length EXACTLY target_len in F|_SK."""
    sk_set = set(sk)
    cycles = []
    visited_as_start = set()
    # For efficiency, use canonical form: cycle's starting node is the minimum
    for start in sorted(sk):
        if start in visited_as_start: continue
        stack = [(start, (start,), {start})]
        while stack:
            cur, path, path_set = stack.pop()
            if len(path) == target_len:
                # Must return to start
                if start in adj.get(cur, []) and start <= min(path):
                    cycles.append(path)
                continue
            for nxt in adj.get(cur, []):
                if nxt not in sk_set: continue
                if nxt == start:
                    # Close early only if length == target_len
                    continue  # handled in len check above
                if nxt in path_set: continue
                if nxt < start: continue  # canonical: start is min
                stack.append((nxt, path + (nxt,), path_set | {nxt}))
    return cycles


def count_covering(sk, cycles):
    """How many SK nodes are covered by the given cycles?"""
    covered = set()
    for cyc in cycles:
        covered.update(cyc)
    return len(covered)


def main():
    print("=" * 100)
    print("SHADOW CYCLE COUNT IN F|_SK: how many length-L cycles cover SK?")
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
                L = len(cycle)
                print(f"\n  ms={ms} L={L} cycle#{ci}  |SK|={len(sk)}")
                t0 = time.time()
                if L > 17:
                    print(f"    skipping — L={L} too large for enumeration")
                    continue
                shadows = enumerate_simple_cycles_at_length(sk, adj, L)
                tt = time.time() - t0
                covered = count_covering(sk, shadows)
                # Need ≥ 2^(n-1)/L shadows to cover bound
                bound_cycles = math.ceil(bound / L)
                print(f"    #shadow cycles of length={L}: {len(shadows)}  [search {tt:.1f}s]")
                print(f"    SK nodes covered by shadows: {covered}/{len(sk)}")
                print(f"    shadows needed for 2^(n-1): ⌈{bound}/{L}⌉ = {bound_cycles}")
                print(f"    shadow count vs bound-cycles: {len(shadows)} vs {bound_cycles}  "
                      f"({'OK' if len(shadows) >= bound_cycles else 'short'})")
                # Are shadows disjoint?
                all_nodes = []
                for s in shadows:
                    all_nodes.extend(s)
                node_counts = Counter(all_nodes)
                disjoint = all(v == 1 for v in node_counts.values())
                max_ct = max(node_counts.values()) if node_counts else 0
                print(f"    shadows disjoint? {disjoint}  max node overlap = {max_ct}")


if __name__ == "__main__":
    main()
