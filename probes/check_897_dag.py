#!/usr/bin/env python3
"""Check if the 897-edge FutureFc-based CF boundary 6-tuple graph has cycles.
Also check the 720-edge phi-based subset.
Compute DAG ranks if applicable."""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from itertools import product as cartesian
from collections import defaultdict, deque

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j+1)%n])

def fire(ms, fs, c, n, i):
    L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
    out = fs[i](L, S, R)
    if out == S: return None
    lst = list(c); lst[i] = out
    return tuple(lst)

def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)
def exp2_count(c, n):
    s = 0
    for j in range(2, n - 2):
        if c[j] == 2 and c[(j+1)%n] != 2: s += 1
    return s
def exp2_weight(c, n):
    s = 0
    for j in range(2, n - 2):
        if c[j] == 2 and c[(j+1)%n] != 2: s += j
    return s

def find_sccs(adj_list, nodes):
    index_counter = [0]
    stack = []; lowlink = {}; index = {}; on_stack = {}; sccs = []
    def strongconnect(v):
        index[v] = index_counter[0]; lowlink[v] = index_counter[0]
        index_counter[0] += 1; stack.append(v); on_stack[v] = True
        for w in adj_list.get(v, []):
            if w not in index:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif on_stack.get(w, False):
                lowlink[v] = min(lowlink[v], index[w])
        if lowlink[v] == index[v]:
            scc = []
            while True:
                w = stack.pop(); on_stack[w] = False; scc.append(w)
                if w == v: break
            sccs.append(scc)
    for v in nodes:
        if v not in index: strongconnect(v)
    return sccs

sys.setrecursionlimit(10000)

for n in [9, 10, 11]:
    ms, fs = build_system(n)
    all_configs = list(cartesian(*(range(m) for m in ms)))

    # Build good set using verify_system approach
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
    adj = defaultdict(list)
    for c in bad_list:
        for i in range(n):
            new = fire(ms, fs, c, n, i)
            if new is not None and new in bad_set:
                adj[c].append(new)

    ff = {c: fc(c, n) for c in bad_list}
    for _ in range(len(bad_list) + 1):
        changed = False
        for c in bad_list:
            for s in adj[c]:
                if ff[s] > ff[c]:
                    ff[c] = ff[s]
                    changed = True
        if not changed: break

    # Compute TP-based phi
    tp_fwd = defaultdict(list)
    for c in bad_list:
        e2c = exp2_count(c, n); i21c = int_21(c, n); ewc = exp2_weight(c, n)
        for i in range(n):
            new = fire(ms, fs, c, n, i)
            if new is not None and new in bad_set:
                if exp2_count(new, n) == e2c and int_21(new, n) == i21c and exp2_weight(new, n) == ewc:
                    tp_fwd[c].append((new, fc(new, n) - fc(c, n)))

    g = {c: 0 for c in bad_list}
    for _ in range(2 * n + 5):
        changed = False
        for c in bad_list:
            for s, dfc in tp_fwd.get(c, []):
                new_g = dfc + g[s]
                if new_g > g[c]: g[c] = new_g; changed = True
        if not changed: break
    phi = {c: fc(c, n) + g[c] for c in bad_list}

    # CF boundary 6-tuple edges under FutureFc
    ff_edges = set()
    phi_edges = set()
    for c in bad_list:
        for i in range(n):
            new = fire(ms, fs, c, n, i)
            if new is None or new not in bad_set: continue
            if not (i <= 2 or i >= n-3): continue
            s6c = (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])
            s6s = (new[0], new[1], new[2], new[n-3], new[n-2], new[n-1])
            if s6c == s6s: continue
            if ff[new] == ff[c]: ff_edges.add((s6c, s6s))
            if phi[new] == phi[c]: phi_edges.add((s6c, s6s))

    # Check both for cycles
    for label, edges in [("FutureFc (897?)", ff_edges), ("phi (720?)", phi_edges)]:
        adj_6 = defaultdict(list)
        nodes_6 = set()
        for a, b in edges:
            adj_6[a].append(b); nodes_6.add(a); nodes_6.add(b)
        for v in nodes_6: adj_6.setdefault(v, [])
        sccs = find_sccs(adj_6, list(nodes_6))
        nontrivial = [s for s in sccs if len(s) > 1]
        print(f"n={n} {label}: {len(edges)} edges, {len(nodes_6)} nodes, {len(nontrivial)} non-trivial SCCs")
        if nontrivial:
            for s in nontrivial[:3]:
                print(f"  SCC size {len(s)}: {sorted(s)[:3]}...")
        else:
            # Compute DAG rank
            in_deg = {v: 0 for v in nodes_6}
            for v in nodes_6:
                for w in adj_6[v]:
                    if w in in_deg: in_deg[w] += 1
            queue = deque([v for v in nodes_6 if in_deg[v] == 0])
            rank = {v: 0 for v in nodes_6}
            while queue:
                v = queue.popleft()
                for w in adj_6[v]:
                    rank[w] = max(rank[w], rank[v] + 1)
                    in_deg[w] -= 1
                    if in_deg[w] == 0: queue.append(w)
            print(f"  DAG! Max rank: {max(rank.values()) if rank else 0}")

    # Also check: full CF graph (including interior) for DAG
    cf_full_adj = defaultdict(list)
    cf_full_nodes = set()
    for c in bad_list:
        for i in range(n):
            new = fire(ms, fs, c, n, i)
            if new is None or new not in bad_set: continue
            if ff[new] != ff[c]: continue
            cf_full_adj[c].append(new)
            cf_full_nodes.add(c); cf_full_nodes.add(new)
    for v in cf_full_nodes: cf_full_adj.setdefault(v, [])
    # Check for cycles via DFS
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {c: WHITE for c in cf_full_nodes}
    has_cycle = False
    for start in cf_full_nodes:
        if color[start] != WHITE: continue
        stack = [(start, iter(cf_full_adj.get(start, [])))]
        color[start] = GRAY
        while stack:
            node, children = stack[-1]
            try:
                child = next(children)
                if color[child] == GRAY:
                    has_cycle = True; break
                if color[child] == WHITE:
                    color[child] = GRAY
                    stack.append((child, iter(cf_full_adj.get(child, []))))
            except StopIteration:
                color[node] = BLACK; stack.pop()
        if has_cycle: break
    print(f"n={n} Full CF graph: {len(cf_full_nodes)} nodes, cycle: {'YES' if has_cycle else 'NO'}")
    print()
