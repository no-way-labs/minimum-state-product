#!/usr/bin/env python3
"""Recompute the CΦ 6-tuple DAG edges with correctly-converged Φ_full."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import build_system
from collections import defaultdict, deque

n = 9; ms, fs = build_system(n); N = 1
for m in ms: N *= m

def idx_to_config(idx):
    c = []
    for m in reversed(ms):
        c.append(idx % m); idx //= m
    return tuple(reversed(c))
def config_to_idx(c):
    idx = 0
    for j in range(n): idx = idx * ms[j] + c[j]
    return idx
def move(c, pos):
    L = c[(pos-1)%n]; S = c[pos]; R = c[(pos+1)%n]
    c2 = list(c); c2[pos] = fs[pos](L, S, R); return tuple(c2)
def fc(c): return sum(1 for j in range(n) if c[j] != c[(j+1)%n])
def tp(c):
    e = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
    i21 = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n]==1)
    w = sum(j for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
    return (e, i21, w)
def boundary6(c): return ((((c[0]*3+c[1])*3+c[2])*3+c[n-3])*3+c[n-2])*2+c[n-1]

all_configs = [idx_to_config(i) for i in range(N)]
bad_set = set()
tp_adj = {}
for i in range(N):
    c = all_configs[i]
    if fc(c) > 0:
        bad_set.add(i)
        tp_adj[i] = []
for i in bad_set:
    c = all_configs[i]
    t = tp(c)
    for p in range(n):
        c2 = move(c, p)
        if c2 == c: continue
        j = config_to_idx(c2)
        if j in bad_set and tp(c2) == t:
            tp_adj[i].append(j)

# Correctly-converged Φ_full
phi_full = {i: fc(all_configs[i]) for i in bad_set}
tp_rev = {i: [] for i in bad_set}
for i in bad_set:
    for j in tp_adj[i]: tp_rev[j].append(i)
changed = True
iters = 0
while changed:
    changed = False; iters += 1
    for j in bad_set:
        for i in tp_rev[j]:
            if phi_full[j] > phi_full[i]:
                phi_full[i] = phi_full[j]; changed = True
print(f"Φ_full converged in {iters} iterations")

# FutureFc
future_fc = {i: fc(all_configs[i]) for i in bad_set}
all_adj = {i: [] for i in bad_set}
for i in bad_set:
    c = all_configs[i]
    for p in range(n):
        c2 = move(c, p)
        if c2 == c: continue
        j = config_to_idx(c2)
        if j in bad_set: all_adj[i].append(j)
all_rev = {i: [] for i in bad_set}
for i in bad_set:
    for j in all_adj[i]: all_rev[j].append(i)
changed = True
while changed:
    changed = False
    for j in bad_set:
        for i in all_rev[j]:
            if future_fc[j] > future_fc[i]:
                future_fc[i] = future_fc[j]; changed = True

# Compute CΦ 6-tuple edges
cphi_edges = set()
for i in bad_set:
    c = all_configs[i]
    for j in tp_adj[i]:
        c2 = all_configs[j]
        if future_fc[j] == future_fc[i] and phi_full[j] == phi_full[i]:
            b1, b2 = boundary6(c), boundary6(c2)
            if b1 != b2:
                cphi_edges.add((b1, b2))

print(f"CΦ 6-tuple edges: {len(cphi_edges)}")

# Check DAG
adj = defaultdict(set)
nodes = set()
for a, b in cphi_edges:
    adj[a].add(b); nodes.add(a); nodes.add(b)

WHITE, GRAY, BLACK = 0, 1, 2
color = {c: WHITE for c in nodes}
is_dag = True
for start in nodes:
    if color[start] != WHITE: continue
    stack = [(start, iter(adj.get(start, set())))]
    color[start] = GRAY
    while stack:
        node, children = stack[-1]
        try:
            child = next(children)
            if child not in nodes: continue
            if color[child] == GRAY:
                is_dag = False; break
            if color[child] == WHITE:
                color[child] = GRAY
                stack.append((child, iter(adj.get(child, set()))))
        except StopIteration:
            color[node] = BLACK
            stack.pop()
    if not is_dag: break

print(f"Is DAG: {is_dag}")

if is_dag:
    # Compute rank (longest path)
    out_deg = {c: len(adj.get(c, set())) for c in nodes}
    sinks = [c for c in nodes if out_deg.get(c, 0) == 0]
    rank = {c: 0 for c in sinks}
    radj = defaultdict(list)
    for c in nodes:
        for s in adj.get(c, set()):
            if s in nodes: radj[s].append(c)
    q = deque(sinks)
    while q:
        s = q.popleft()
        for c in radj.get(s, []):
            new_r = rank[s] + 1
            if c not in rank or new_r > rank[c]:
                rank[c] = new_r; q.append(c)
    max_rank = max(rank.values())
    print(f"Max rank: {max_rank}")

    # Compute rank for all 324 states
    all_ranks = [0] * 324
    for s in range(324):
        if s in rank:
            all_ranks[s] = rank[s]

    # Output edge list and rank values for Lean
    sorted_edges = sorted(cphi_edges)
    print(f"\n-- Edge list ({len(sorted_edges)} edges)")
    edge_strs = [f"({a}, {b})" for a, b in sorted_edges]
    for i in range(0, len(edge_strs), 20):
        print("    " + ", ".join(edge_strs[i:i+20]) + ",")

    print(f"\n-- Rank values ({max_rank} max)")
    for i in range(0, 324, 18):
        chunk = all_ranks[i:i+18]
        print("  " + ", ".join(str(v) for v in chunk) + ",")

print("\nDONE")
