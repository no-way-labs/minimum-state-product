#!/usr/bin/env python3
"""Find a rank function for ALL privileged boundary-changing transitions."""

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

def enc(c0,c1,c2,cN3,cN2,cN1):
    return ((((c0*3+c1)*3+c2)*3+cN3)*3+cN2)*2+cN1

# Collect ALL boundary-changing privileged transitions
trans = set()
for c0 in range(2):
 for c1 in range(3):
  for c2 in range(3):
   for cN3 in range(3):
    for cN2 in range(3):
     for cN1 in range(2):
      src = enc(c0,c1,c2,cN3,cN2,cN1)
      # Pos 0
      v = TBotVal(cN1, c0, c1)
      if v != c0 and v < 2:
          trans.add((src, enc(v,c1,c2,cN3,cN2,cN1)))
      # Pos 1
      v = TLowVal(c0, c1, c2)
      if v != c1 and v < 3:
          trans.add((src, enc(c0,v,c2,cN3,cN2,cN1)))
      # Pos 2 (R is interior)
      for R in range(3):
          v = TMidVal(c1, c2, R)
          if v != c2 and v < 3:
              trans.add((src, enc(c0,c1,v,cN3,cN2,cN1)))
      # Pos N-3 (L is interior)
      for L in range(3):
          v = TMidVal(L, cN3, cN2)
          if v != cN3 and v < 3:
              trans.add((src, enc(c0,c1,c2,v,cN2,cN1)))
      # Pos N-2
      v = THighVal(cN3, cN2, cN1)
      if v != cN2 and v < 3:
          trans.add((src, enc(c0,c1,c2,cN3,v,cN1)))
      # Pos N-1
      v = TTopVal(cN2, cN1, c0)
      if v != cN1 and v < 2:
          trans.add((src, enc(c0,c1,c2,cN3,cN2,v)))

print(f"Total boundary-changing transitions: {len(trans)}")

# Check for cycles using Tarjan's SCC
from collections import defaultdict
adj = defaultdict(list)
for s, t in trans:
    adj[s].append(t)

# Tarjan's SCC
index_counter = [0]
stack = []
lowlink = {}
index = {}
on_stack = {}
sccs = []

def strongconnect(v):
    index[v] = index_counter[0]
    lowlink[v] = index_counter[0]
    index_counter[0] += 1
    stack.append(v)
    on_stack[v] = True

    for w in adj[v]:
        if w not in index:
            strongconnect(w)
            lowlink[v] = min(lowlink[v], lowlink[w])
        elif on_stack.get(w, False):
            lowlink[v] = min(lowlink[v], index[w])

    if lowlink[v] == index[v]:
        scc = []
        while True:
            w = stack.pop()
            on_stack[w] = False
            scc.append(w)
            if w == v:
                break
        if len(scc) > 1:
            sccs.append(scc)

import sys
sys.setrecursionlimit(10000)
for v in range(324):
    if v not in index:
        strongconnect(v)

print(f"Non-trivial SCCs: {len(sccs)}")
for scc in sccs[:5]:
    print(f"  SCC size {len(scc)}: {scc[:10]}...")

# Also check for self-loops
self_loops = [(s,t) for s,t in trans if s == t]
print(f"Self-loops: {len(self_loops)}")
