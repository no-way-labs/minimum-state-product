#!/usr/bin/env python3
"""Check if full-config CΦ subgraph is still a DAG with correct Φ_full."""
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

bad_set = set()
tp_adj = {}
for i in range(N):
    if fc(idx_to_config(i)) > 0:
        bad_set.add(i); tp_adj[i] = []
for i in bad_set:
    c = idx_to_config(i); t = tp(c)
    for p in range(n):
        c2 = move(c, p)
        if c2 == c: continue
        j = config_to_idx(c2)
        if j in bad_set and tp(c2) == t: tp_adj[i].append(j)

phi_full = {i: fc(idx_to_config(i)) for i in bad_set}
tp_rev = {i: [] for i in bad_set}
for i in bad_set:
    for j in tp_adj[i]: tp_rev[j].append(i)
changed = True
while changed:
    changed = False
    for j in bad_set:
        for i in tp_rev[j]:
            if phi_full[j] > phi_full[i]:
                phi_full[i] = phi_full[j]; changed = True

future_fc = {i: fc(idx_to_config(i)) for i in bad_set}
all_adj = {i: [] for i in bad_set}
for i in bad_set:
    c = idx_to_config(i)
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

# Full-config CΦ subgraph
cphi_adj = defaultdict(list)
cphi_nodes = set()
cphi_edges = 0
for i in bad_set:
    for j in tp_adj[i]:
        if future_fc[j] == future_fc[i] and phi_full[j] == phi_full[i]:
            cphi_adj[i].append(j); cphi_nodes.add(i); cphi_nodes.add(j)
            cphi_edges += 1

print(f"Full CΦ: {len(cphi_nodes)} nodes, {cphi_edges} edges")

# DAG check
WHITE, GRAY, BLACK = 0, 1, 2
color = {c: WHITE for c in cphi_nodes}
is_dag = True
cycle_node = None
for start in cphi_nodes:
    if color[start] != WHITE: continue
    stack = [(start, iter(cphi_adj.get(start, [])))]
    color[start] = GRAY
    while stack:
        node, children = stack[-1]
        try:
            child = next(children)
            if child not in cphi_nodes: continue
            if color[child] == GRAY:
                is_dag = False; cycle_node = child; break
            if color[child] == WHITE:
                color[child] = GRAY
                stack.append((child, iter(cphi_adj.get(child, []))))
        except StopIteration:
            color[node] = BLACK; stack.pop()
    if not is_dag: break

print(f"Full CΦ is DAG: {is_dag}")

if not is_dag:
    print(f"Cycle found near config {cycle_node}: {idx_to_config(cycle_node)}")
    # Find the actual cycle via BFS
    visited = {cycle_node}; parent = {cycle_node: None}
    q = deque([cycle_node])
    while q:
        u = q.popleft()
        for v in cphi_adj.get(u, []):
            if v == cycle_node and u != cycle_node:
                # Found cycle back
                path = [cycle_node, u]
                p = parent[u]
                while p and p != cycle_node:
                    path.append(p); p = parent[p]
                path.reverse()
                print(f"  Cycle length: {len(path)}")
                for x in path[:5]:
                    print(f"    {idx_to_config(x)} fc={fc(idx_to_config(x))} phi={phi_full[x]}")
                break
            if v not in visited and v in cphi_nodes:
                visited.add(v); parent[v] = u; q.append(v)

if is_dag:
    # Compute rank
    out_deg = {c: len(cphi_adj.get(c, [])) for c in cphi_nodes}
    sinks = [c for c in cphi_nodes if out_deg.get(c, 0) == 0]
    rank = {c: 0 for c in sinks}
    radj = defaultdict(list)
    for c in cphi_nodes:
        for s in cphi_adj.get(c, []):
            if s in cphi_nodes: radj[s].append(c)
    q = deque(sinks)
    while q:
        s = q.popleft()
        for c in radj.get(s, []):
            new_r = rank[s] + 1
            if c not in rank or new_r > rank[c]:
                rank[c] = new_r; q.append(c)
    print(f"Max rank: {max(rank.values())}")

print("DONE")
