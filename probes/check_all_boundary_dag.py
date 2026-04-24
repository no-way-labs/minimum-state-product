#!/usr/bin/env python3
"""
Check: is the FULL set of all possible boundary transitions (at ALL positions,
for ALL privilege conditions) a DAG on 324 states?

If so, we can use this as the edge set instead of the 617+12 edges,
and the axiom becomes trivially true (every boundary-changing step is an edge).
"""

# LEAN TABLES
def TBotVal(L,S,R):
    t = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,
         (1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    return t.get((L,S,R), 0)
def TLowVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,
         (0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
         (1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    return t.get((L,S,R), 0)
def TMidVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,
         (0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
         (1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,
         (2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,
         (2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L,S,R), 0)
def THighVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,
         (1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,
         (2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    return t.get((L,S,R), 0)
def TTopVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,
         (1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,
         (2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    return t.get((L,S,R), 0)

def enc(c0,c1,c2,cN3,cN2,cN1):
    return ((((c0*3+c1)*3+c2)*3+cN3)*3+cN2)*2+cN1

# Generate ALL possible boundary transitions for ANY boundary move
# A boundary move changes one of: c[0], c[1], c[2], c[n-3], c[n-2], c[n-1]
# The transition table determines the new value based on (L, S, R)

all_edges = set()

for c0 in range(2):
 for c1 in range(3):
  for c2 in range(3):
   for cN3 in range(3):
    for cN2 in range(3):
     for cN1 in range(2):
      src = enc(c0,c1,c2,cN3,cN2,cN1)

      # Position 0 (TBot): L=c[n-1], S=c[0], R=c[1]
      v = TBotVal(cN1, c0, c1)
      if v != c0:
          dst = enc(v,c1,c2,cN3,cN2,cN1)
          if src != dst:
              all_edges.add((src, dst))

      # Position 1 (TLow): L=c[0], S=c[1], R=c[2]
      v = TLowVal(c0, c1, c2)
      if v != c1:
          dst = enc(c0,v,c2,cN3,cN2,cN1)
          if src != dst:
              all_edges.add((src, dst))

      # Position 2 (TMid): L=c[1], S=c[2], R=c[3]
      # c[3] is NOT in the 6-tuple for n>=9 (it's interior), so R ranges over {0,1,2}
      for R in range(3):
          v = TMidVal(c1, c2, R)
          if v != c2:
              dst = enc(c0,c1,v,cN3,cN2,cN1)
              if src != dst:
                  all_edges.add((src, dst))

      # Position n-3 (TMid): L=c[n-4], S=c[n-3], R=c[n-2]
      # c[n-4] is NOT in 6-tuple for n>=9, so L ranges over {0,1,2}
      for L in range(3):
          v = TMidVal(L, cN3, cN2)
          if v != cN3:
              dst = enc(c0,c1,c2,v,cN2,cN1)
              if src != dst:
                  all_edges.add((src, dst))

      # Position n-2 (THigh): L=c[n-3], S=c[n-2], R=c[n-1]
      v = THighVal(cN3, cN2, cN1)
      if v != cN2:
          dst = enc(c0,c1,c2,cN3,v,cN1)
          if src != dst:
              all_edges.add((src, dst))

      # Position n-1 (TTop): L=c[n-2], S=c[n-1], R=c[0]
      v = TTopVal(cN2, cN1, c0)
      if v != cN1:
          dst = enc(c0,c1,c2,cN3,cN2,v)
          if src != dst:
              all_edges.add((src, dst))

print(f"Total unique boundary transition edges: {len(all_edges)}")

# Check for cycles
from collections import defaultdict
adj = defaultdict(list)
for s, d in all_edges:
    adj[s].append(d)

# Gather all nodes
nodes = set()
for s, d in all_edges:
    nodes.add(s)
    nodes.add(d)

# DFS cycle detection
WHITE, GRAY, BLACK = 0, 1, 2
color = {n: WHITE for n in range(324)}
has_cycle = False
cycle_node = None

for start in range(324):
    if color[start] != WHITE:
        continue
    stack = [(start, iter(adj.get(start, [])))]
    color[start] = GRAY
    while stack:
        v, ch = stack[-1]
        try:
            w = next(ch)
            if color[w] == GRAY:
                has_cycle = True
                cycle_node = w
                break
            elif color[w] == WHITE:
                color[w] = GRAY
                stack.append((w, iter(adj.get(w, []))))
        except StopIteration:
            stack.pop()
            color[v] = BLACK
    if has_cycle:
        break

print(f"Full boundary transition graph is DAG: {not has_cycle}")
if has_cycle:
    print(f"  Cycle detected at node {cycle_node}")

    # Find a short cycle from cycle_node
    from collections import deque
    visited = {cycle_node}
    parent = {cycle_node: None}
    queue = deque([cycle_node])
    found_cycle = False
    while queue and not found_cycle:
        v = queue.popleft()
        for w in adj.get(v, []):
            if w == cycle_node:
                # Found cycle back to start
                path = [cycle_node]
                cur = v
                while cur != cycle_node:
                    path.append(cur)
                    cur = parent[cur]
                path.append(cycle_node)
                path.reverse()
                print(f"  Cycle: {path}")
                found_cycle = True
                break
            if w not in visited:
                visited.add(w)
                parent[w] = v
                queue.append(w)

    # Also check: what positions can cause transitions between the cycle nodes?
    # Decode a 6-tuple from int
    def decode(x):
        cN1 = x % 2; x //= 2
        cN2 = x % 3; x //= 3
        cN3 = x % 3; x //= 3
        c2 = x % 3; x //= 3
        c1 = x % 3; x //= 3
        c0 = x
        return (c0, c1, c2, cN3, cN2, cN1)

    if found_cycle:
        print("\n  Cycle node values:")
        for p in path:
            print(f"    {p} -> {decode(p)}")
