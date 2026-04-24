#!/usr/bin/env python3
"""Check if all privileged boundary transitions form an acyclic graph."""
import re, os
from collections import defaultdict, deque

def encode(c0, c1, c2, cN3, cN2, cN1):
    return ((((c0 * 3 + c1) * 3 + c2) * 3 + cN3) * 3 + cN2) * 2 + cN1

path = os.path.join(os.path.dirname(__file__), '..', 'lean', 'LeanMn', 'Convergence', 'SixTuple.lean')
with open(path) as f:
    content = f.read()
m = re.search(r'def sixTupleEdgeVals.*?\[(.*?)\]', content, re.DOTALL)
pairs = re.findall(r'\((\d+),\s*(\d+)\)', m.group(1))
edges = set((int(a), int(b)) for a, b in pairs)
b4_edges = {(4,5),(10,11),(16,17),(22,23),(28,29),(34,35),(40,41),(46,47),(52,53),(148,149),(154,155),(160,161)}
edges |= b4_edges

def TBotVal(L,S,R):
    t={(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    return t.get((L,S,R),0)
def TLowVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    return t.get((L,S,R),0)
def TMidVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L,S,R),0)
def THighVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    return t.get((L,S,R),0)
def TTopVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    return t.get((L,S,R),0)

all_trans = set()
for c0 in range(2):
 for c1 in range(3):
  for c2 in range(3):
   for cN3 in range(3):
    for cN2 in range(3):
     for cN1 in range(2):
      se = encode(c0,c1,c2,cN3,cN2,cN1)
      nc0=TBotVal(cN1,c0,c1)
      if nc0!=c0: all_trans.add((se, encode(nc0,c1,c2,cN3,cN2,cN1)))
      nc1=TLowVal(c0,c1,c2)
      if nc1!=c1: all_trans.add((se, encode(c0,nc1,c2,cN3,cN2,cN1)))
      for c3 in range(3):
        nc2=TMidVal(c1,c2,c3)
        if nc2!=c2: all_trans.add((se, encode(c0,c1,nc2,cN3,cN2,cN1)))
      for cn4 in range(3):
        ncN3=TMidVal(cn4,cN3,cN2)
        if ncN3!=cN3: all_trans.add((se, encode(c0,c1,c2,ncN3,cN2,cN1)))
      ncN2=THighVal(cN3,cN2,cN1)
      if ncN2!=cN2: all_trans.add((se, encode(c0,c1,c2,cN3,ncN2,cN1)))
      ncN1=TTopVal(cN2,cN1,c0)
      if ncN1!=cN1: all_trans.add((se, encode(c0,c1,c2,cN3,cN2,ncN1)))

print(f'Total unique transitions: {len(all_trans)}')
print(f'In extended edge list: {len(all_trans & edges)}')
print(f'Not in edge list: {len(all_trans - edges)}')

# Check acyclicity
adj = defaultdict(set)
nodes = set()
for s, sp in all_trans:
    adj[s].add(sp)
    nodes.add(s); nodes.add(sp)
indeg = {n: 0 for n in nodes}
for s, sp in all_trans:
    indeg[sp] += 1

q = deque([n for n in nodes if indeg[n] == 0])
order = []
while q:
    u = q.popleft()
    order.append(u)
    for v in adj[u]:
        indeg[v] -= 1
        if indeg[v] == 0: q.append(v)
if len(order) == len(nodes):
    print('ACYCLIC')
    rank = {}
    for u in reversed(order):
        rank[u] = max((rank[v]+1 for v in adj[u]), default=0)
    max_rank = max(rank.values())
    print(f'Max rank: {max_rank}')
    rank_list = [rank.get(i, 0) for i in range(324)]
    print(f'Rank list (for Lean): {rank_list}')
else:
    print(f'HAS CYCLE - sorted {len(order)} of {len(nodes)}')
    remaining = nodes - set(order)
    # Find cycle
    visited = set()
    for start in remaining:
        if start in visited: continue
        path = [start]
        seen = {start}
        cur = start
        while True:
            nxt = None
            for v in adj[cur]:
                if v in remaining:
                    nxt = v
                    break
            if nxt is None: break
            if nxt in seen:
                idx = path.index(nxt)
                cycle = path[idx:]
                print(f'Cycle: {cycle}')
                break
            path.append(nxt)
            seen.add(nxt)
            visited.add(nxt)
            cur = nxt
        else:
            continue
        break
