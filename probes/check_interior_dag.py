#!/usr/bin/env python3
"""Within constant-FutureFc and constant 6-tuple, is the interior subgraph a DAG?
This is the key claim (3B) from the paper proof.
If yes, we just need to handle the boundary 6-tuple changes."""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from itertools import product as cartesian
from collections import defaultdict

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j+1)%n])

def fire(ms, fs, c, n, i):
    L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
    out = fs[i](L, S, R)
    if out == S: return None
    lst = list(c); lst[i] = out
    return tuple(lst)

def get_6tuple(c, n):
    return (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])

for n in range(5, 13):
    ms, fs = build_system(n)
    all_configs = list(cartesian(*(range(m) for m in ms)))

    good_set = set()
    cur = list(tuple([0]*n))
    good_set.add(tuple(cur))
    for phase in range(3):
        rng = range(n) if phase % 2 == 0 else range(n-1, -1, -1)
        for i in rng:
            new = fire(ms, fs, tuple(cur), n, i)
            if new is not None:
                cur = list(new)
                good_set.add(tuple(cur))

    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    # Compute FutureFc
    all_adj = defaultdict(list)
    for c in bad_list:
        for i in range(n):
            new = fire(ms, fs, c, n, i)
            if new is not None and new in bad_set:
                all_adj[c].append((new, i))

    ff = {c: fc(c, n) for c in bad_list}
    for _ in range(len(bad_list) + 1):
        changed = False
        for c in bad_list:
            for s, _ in all_adj[c]:
                if ff[s] > ff[c]: ff[c] = ff[s]; changed = True
        if not changed: break

    # Group by (FutureFc, 6-tuple). Within each group, check for cycles.
    # Only consider INTERIOR fires (positions 3..n-4 for n≥7, or non-boundary)
    groups = defaultdict(lambda: defaultdict(list))  # (ff, 6t) -> adj list

    for c in bad_list:
        for s, i in all_adj[c]:
            if ff[s] != ff[c]: continue  # not CF
            if i <= 2 or i >= n-3: continue  # boundary fire
            s6c = get_6tuple(c, n)
            s6s = get_6tuple(s, n)
            if s6c != s6s: continue  # 6-tuple changed (shouldn't happen for interior fire)
            key = (ff[c], s6c)
            groups[key][c].append(s)

    # Check each group for cycles via DFS
    total_groups = len(groups)
    cycle_groups = 0
    max_group_size = 0
    total_interior_edges = 0

    for key, adj in groups.items():
        nodes = set(adj.keys())
        for c in adj:
            for s in adj[c]:
                nodes.add(s)
        if len(nodes) > max_group_size:
            max_group_size = len(nodes)
        edge_count = sum(len(adj[c]) for c in adj)
        total_interior_edges += edge_count

        # Cycle check
        WHITE, GRAY, BLACK = 0, 1, 2
        color = {c: WHITE for c in nodes}
        has_cycle = False
        for start in nodes:
            if color[start] != WHITE: continue
            stack = [(start, iter(adj.get(start, [])))]
            color[start] = GRAY
            while stack:
                node, children = stack[-1]
                try:
                    child = next(children)
                    if color[child] == GRAY:
                        has_cycle = True; break
                    if color[child] == WHITE:
                        color[child] = GRAY
                        stack.append((child, iter(adj.get(child, []))))
                except StopIteration:
                    color[node] = BLACK; stack.pop()
            if has_cycle: break
        if has_cycle:
            cycle_groups += 1

    print(f"n={n}: {total_groups} (ff,6t) groups, {total_interior_edges} interior CF edges, "
          f"max group size {max_group_size}, CYCLES: {cycle_groups}")

    # Also check: across ALL 6-tuples, is the interior CF subgraph a DAG?
    # (ignoring 6-tuple grouping, just ff-preserving interior steps)
    all_int_adj = defaultdict(list)
    all_int_nodes = set()
    for c in bad_list:
        for s, i in all_adj[c]:
            if ff[s] != ff[c]: continue
            if i <= 2 or i >= n-3: continue
            if get_6tuple(c, n) != get_6tuple(s, n): continue
            all_int_adj[c].append(s)
            all_int_nodes.add(c)
            all_int_nodes.add(s)

    if all_int_nodes:
        WHITE, GRAY, BLACK = 0, 1, 2
        color = {c: WHITE for c in all_int_nodes}
        has_cycle = False
        for start in all_int_nodes:
            if color[start] != WHITE: continue
            stack = [(start, iter(all_int_adj.get(start, [])))]
            color[start] = GRAY
            while stack:
                node, children = stack[-1]
                try:
                    child = next(children)
                    if color[child] == GRAY:
                        has_cycle = True; break
                    if color[child] == WHITE:
                        color[child] = GRAY
                        stack.append((child, iter(all_int_adj.get(child, []))))
                except StopIteration:
                    color[node] = BLACK; stack.pop()
            if has_cycle: break
        print(f"  All interior CF (6t-unchanged): {len(all_int_nodes)} nodes, cycle: {'YES' if has_cycle else 'NO'}")
