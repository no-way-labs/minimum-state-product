#!/usr/bin/env python3
"""Check if the full boundary transition graph has cycles."""
import sys
sys.setrecursionlimit(2000)

# Import tables from check_rank.py
exec(open('check_rank.py').read().split('ok = 0')[0])

from collections import defaultdict
G = defaultdict(set)
for i in range(324):
    a,b,c,d,e,f = dec(i)
    o2 = TBot(f,a,b)
    if o2 != a:
        G[i].add(enc(o2,b,c,d,e,f))
    o2 = TLow(a,b,c)
    if o2 != b:
        G[i].add(enc(a,o2,c,d,e,f))
    for x in range(3):
        o2 = TMid(b,c,x)
        if o2 != c:
            G[i].add(enc(a,b,o2,d,e,f))
    for x in range(3):
        o2 = TMid(x,d,e)
        if o2 != d:
            G[i].add(enc(a,b,c,o2,e,f))
    o2 = THigh(d,e,f)
    if o2 != e:
        G[i].add(enc(a,b,c,d,o2,f))
    o2 = TTop(e,f,a)
    if o2 != f:
        G[i].add(enc(a,b,c,d,e,o2))

# Tarjan SCC
idx_ctr = [0]
stk = []
low = {}
ix = {}
on_stk = set()
sccs = []

def sc(v):
    ix[v] = low[v] = idx_ctr[0]
    idx_ctr[0] += 1
    stk.append(v)
    on_stk.add(v)
    for w in G[v]:
        if w not in ix:
            sc(w)
            low[v] = min(low[v], low[w])
        elif w in on_stk:
            low[v] = min(low[v], ix[w])
    if low[v] == ix[v]:
        s = []
        while True:
            w = stk.pop()
            on_stk.discard(w)
            s.append(w)
            if w == v:
                break
        sccs.append(s)

for v in range(324):
    if v not in ix:
        sc(v)

nt = [s for s in sccs if len(s) > 1]
print(f"Total SCCs: {len(sccs)}, nontrivial (cycles): {len(nt)}")
if nt:
    for s in nt[:5]:
        print(f"  Cycle of size {len(s)}: {s[:8]}...")
else:
    print("The full boundary transition graph is a DAG!")
    # Compute DAG rank
    from collections import deque
    in_deg = defaultdict(int)
    all_nodes = set(range(324))
    for u in all_nodes:
        for v in G[u]:
            in_deg[v] += 1
    rank = [0] * 324
    q = deque([v for v in all_nodes if in_deg[v] == 0 and len(G[v]) == 0])
    # Actually compute longest path (DAG rank = longest path to sink)
    # Reverse topological order
    topo = []
    visited = set()
    def topo_dfs(v):
        visited.add(v)
        for w in G[v]:
            if w not in visited:
                topo_dfs(w)
        topo.append(v)
    for v in range(324):
        if v not in visited:
            topo_dfs(v)
    # topo is in reverse topological order
    dist = [0] * 324
    for v in topo:
        for w in G[v]:
            if dist[w] + 1 > dist[v]:
                dist[v] = dist[w] + 1
    print(f"Max DAG rank (longest path): {max(dist)}")
    print(f"Rank distribution: {sorted(set(dist))}")
