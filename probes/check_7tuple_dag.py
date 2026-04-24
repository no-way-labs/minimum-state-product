#!/usr/bin/env python3
"""Check if augmenting the 6-tuple with local fc gives a DAG for all transitions."""

def TBotVal(L,S,R):
    t={(0,0,0):1,(0,0,1):0,(0,0,2):0,(0,1,0):1,(0,1,1):0,(0,1,2):1,(1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):0,(1,1,1):0,(1,1,2):0}
    return t.get((L,S,R),S)
def TLowVal(L,S,R):
    t={(0,0,0):0,(0,0,1):2,(0,0,2):0,(0,1,0):2,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):2,(1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0,(1,2,0):0,(1,2,1):0,(1,2,2):2}
    return t.get((L,S,R),S)
def TMidVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,0,2):2,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):1,(0,2,1):2,(0,2,2):2,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):2,(1,2,0):1,(1,2,1):2,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):0,(2,1,0):0,(2,1,1):1,(2,1,2):0,(2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L,S,R),S)
def THighVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):0,(0,2,2):2,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):2,(1,1,2):0,(1,2,0):1,(1,2,1):0,(1,2,2):2,(2,0,0):0,(2,0,1):1,(2,0,2):0,(2,1,0):2,(2,1,1):2,(2,1,2):0,(2,2,0):1,(2,2,1):0,(2,2,2):2}
    return t.get((L,S,R),S)
def TTopVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):0,(1,1,1):0,(2,0,0):1,(2,0,1):1,(2,1,0):0,(2,1,1):0}
    return t.get((L,S,R),S)

def frontierBit(a, b):
    return 0 if a == b else 1

def enc6(c0,c1,c2,cN3,cN2,cN1):
    return ((((c0*3+c1)*3+c2)*3+cN3)*3+cN2)*2+cN1

# Define boundary fc: sum of frontier bits at positions 0, 1, N-2, N-1 (those fully determined by boundary)
# fc_boundary = fb(cN1,c0) + fb(c0,c1) + fb(cN3,cN2) + fb(cN2,cN1)
# But we also have fb(c1,c2) and fb(c2,cN3) from the boundary
# Total boundary fc = all 6 pairs: fb(cN1,c0) + fb(c0,c1) + fb(c1,c2) + ... + fb(cN2,cN1)
# For the ring: fb(cN1,c0) + fb(c0,c1) + fb(c1,c2) + fb(c2,cN3) + fb(cN3,cN2) + fb(cN2,cN1)

def boundary_fc(c0,c1,c2,cN3,cN2,cN1):
    return (frontierBit(cN1,c0) + frontierBit(c0,c1) + frontierBit(c1,c2) +
            frontierBit(c2,cN3) + frontierBit(cN3,cN2) + frontierBit(cN2,cN1))

# 7-tuple state: (6-tuple-encoding, boundary_fc)
# boundary_fc ranges 0..6, so 324 * 7 = 2268 states
def enc7(c0,c1,c2,cN3,cN2,cN1):
    return enc6(c0,c1,c2,cN3,cN2,cN1) * 7 + boundary_fc(c0,c1,c2,cN3,cN2,cN1)

# Collect ALL boundary-changing transitions on 7-tuple
trans7 = set()
for c0 in range(2):
 for c1 in range(3):
  for c2 in range(3):
   for cN3 in range(3):
    for cN2 in range(3):
     for cN1 in range(2):
      src7 = enc7(c0,c1,c2,cN3,cN2,cN1)
      # Pos 0
      v = TBotVal(cN1, c0, c1)
      if v != c0 and v < 2:
          trans7.add((src7, enc7(v,c1,c2,cN3,cN2,cN1)))
      # Pos 1
      v = TLowVal(c0, c1, c2)
      if v != c1 and v < 3:
          trans7.add((src7, enc7(c0,v,c2,cN3,cN2,cN1)))
      # Pos 2 (all R)
      for R in range(3):
          v = TMidVal(c1, c2, R)
          if v != c2 and v < 3:
              trans7.add((src7, enc7(c0,c1,v,cN3,cN2,cN1)))
      # Pos N-3 (all L)
      for L in range(3):
          v = TMidVal(L, cN3, cN2)
          if v != cN3 and v < 3:
              trans7.add((src7, enc7(c0,c1,c2,v,cN2,cN1)))
      # Pos N-2
      v = THighVal(cN3, cN2, cN1)
      if v != cN2 and v < 3:
          trans7.add((src7, enc7(c0,c1,c2,cN3,v,cN1)))
      # Pos N-1
      v = TTopVal(cN2, cN1, c0)
      if v != cN1 and v < 2:
          trans7.add((src7, enc7(c0,c1,c2,cN3,cN2,v)))

print(f"Total 7-tuple boundary transitions: {len(trans7)}")

# Check DAG
from collections import defaultdict, deque
adj = defaultdict(list)
nodes = set()
for s, t in trans7:
    adj[s].append(t)
    nodes.add(s)
    nodes.add(t)

# Get all reachable nodes
all_nodes = set(range(324 * 7))

in_degree = defaultdict(int)
for s, t in trans7:
    in_degree[t] += 1
for v in all_nodes:
    if v not in in_degree:
        in_degree[v] = 0

queue = deque([v for v in all_nodes if in_degree[v] == 0])
topo_order = []
while queue:
    v = queue.popleft()
    topo_order.append(v)
    for w in adj[v]:
        in_degree[w] -= 1
        if in_degree[w] == 0:
            queue.append(w)

if len(topo_order) == len(all_nodes):
    print("7-tuple transitions form a DAG!")
    rank = defaultdict(int)
    for v in reversed(topo_order):
        for w in adj[v]:
            rank[v] = max(rank[v], rank[w] + 1)
    print(f"Max rank: {max(rank.values()) if rank else 0}")
else:
    print(f"NOT a DAG ({len(topo_order)}/{len(all_nodes)} sorted)")

    # Find SCCs
    import sys
    sys.setrecursionlimit(100000)
    index_counter = [0]
    stack = []
    lowlink = {}
    index_map = {}
    on_stack = {}
    sccs = []

    def strongconnect(v):
        index_map[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack[v] = True
        for w in adj[v]:
            if w not in index_map:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif on_stack.get(w, False):
                lowlink[v] = min(lowlink[v], index_map[w])
        if lowlink[v] == index_map[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack[w] = False
                scc.append(w)
                if w == v:
                    break
            if len(scc) > 1:
                sccs.append(scc)

    for v in nodes:  # Only check nodes that actually appear
        if v not in index_map:
            strongconnect(v)

    print(f"Non-trivial SCCs: {len(sccs)}")
    for scc in sccs[:5]:
        print(f"  SCC size {len(scc)}: {[s//7 for s in scc[:10]]}... (fc values: {[s%7 for s in scc[:10]]})")
