#!/usr/bin/env python3
"""Check if all fc-PRESERVING boundary transitions are in extendedBoundaryEdge.
fc = sum of localFc values. A transition preserves fc if localFcAfter = localFcBefore at position i,
AND the rest of fc is unchanged (which is true since only position i changes)."""
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

# localFcBefore(L, S, R) = number of frontier edges
# frontier = (L != S) + (S != R)  (for interior positions)
# For boundary: P0 has L=cN1, S=c0, R=c1; P1 has L=c0, S=c1, R=c2; etc.
def localFcBefore(L, S, R):
    return (1 if L != S else 0) + (1 if S != R else 0)

def localFcAfter(L, S_new, R):
    return (1 if L != S_new else 0) + (1 if S_new != R else 0)

# But fc change also depends on what the LEFT neighbor sees (with this position as R)
# and what the RIGHT neighbor sees (with this position as L).
# Full delta_fc = localFcAfter_here - localFcBefore_here
#   + change at left neighbor (R changes from S to S_new)
#   + change at right neighbor (L changes from S to S_new)
# Actually: fc = sum over all edges. Edge (i, i+1) contributes 1 if c[i] != c[i+1].
# When c[i] changes from S to S_new:
# - Edge (i-1, i): was (L != S), becomes (L != S_new)
# - Edge (i, i+1): was (S != R), becomes (S_new != R)
# Delta = (L != S_new) - (L != S) + (S_new != R) - (S != R)
# fc preserved iff delta = 0

def delta_fc(L, S, R, S_new):
    return ((1 if L != S_new else 0) - (1 if L != S else 0) +
            (1 if S_new != R else 0) - (1 if S != R else 0))

# Check: fc-preserving and fc-nondecreasing boundary transitions
fc_preserving_trans = set()
fc_nondec_trans = set()  # delta_fc >= 0

for c0 in range(2):
 for c1 in range(3):
  for c2 in range(3):
   for cN3 in range(3):
    for cN2 in range(3):
     for cN1 in range(2):
      se = encode(c0,c1,c2,cN3,cN2,cN1)

      # P0: L=cN1, S=c0, R=c1
      nc0=TBotVal(cN1,c0,c1)
      if nc0!=c0:
        d = delta_fc(cN1, c0, c1, nc0)
        se2=encode(nc0,c1,c2,cN3,cN2,cN1)
        if d == 0: fc_preserving_trans.add((se, se2))
        if d >= 0: fc_nondec_trans.add((se, se2))

      # P1: L=c0, S=c1, R=c2
      nc1=TLowVal(c0,c1,c2)
      if nc1!=c1:
        d = delta_fc(c0, c1, c2, nc1)
        se2=encode(c0,nc1,c2,cN3,cN2,cN1)
        if d == 0: fc_preserving_trans.add((se, se2))
        if d >= 0: fc_nondec_trans.add((se, se2))

      # P2: L=c1, S=c2, R=c3
      for c3 in range(3):
        nc2=TMidVal(c1,c2,c3)
        if nc2!=c2:
          d = delta_fc(c1, c2, c3, nc2)
          se2=encode(c0,c1,nc2,cN3,cN2,cN1)
          if d == 0: fc_preserving_trans.add((se, se2))
          if d >= 0: fc_nondec_trans.add((se, se2))

      # PN3: L=cn4, S=cN3, R=cN2
      for cn4 in range(3):
        ncN3=TMidVal(cn4,cN3,cN2)
        if ncN3!=cN3:
          d = delta_fc(cn4, cN3, cN2, ncN3)
          se2=encode(c0,c1,c2,ncN3,cN2,cN1)
          if d == 0: fc_preserving_trans.add((se, se2))
          if d >= 0: fc_nondec_trans.add((se, se2))

      # PN2: L=cN3, S=cN2, R=cN1
      ncN2=THighVal(cN3,cN2,cN1)
      if ncN2!=cN2:
        d = delta_fc(cN3, cN2, cN1, ncN2)
        se2=encode(c0,c1,c2,cN3,ncN2,cN1)
        if d == 0: fc_preserving_trans.add((se, se2))
        if d >= 0: fc_nondec_trans.add((se, se2))

      # PN1: L=cN2, S=cN1, R=c0
      ncN1=TTopVal(cN2,cN1,c0)
      if ncN1!=cN1:
        d = delta_fc(cN2, cN1, c0, ncN1)
        se2=encode(c0,c1,c2,cN3,cN2,ncN1)
        if d == 0: fc_preserving_trans.add((se, se2))
        if d >= 0: fc_nondec_trans.add((se, se2))

print(f'Fc-preserving transitions: {len(fc_preserving_trans)}')
print(f'In extended edge list: {len(fc_preserving_trans & edges)}')
print(f'Missing: {len(fc_preserving_trans - edges)}')
if fc_preserving_trans - edges:
    for t in sorted(fc_preserving_trans - edges)[:20]:
        print(f'  {t}')

print(f'\nFc-nondecreasing transitions: {len(fc_nondec_trans)}')
print(f'In extended edge list: {len(fc_nondec_trans & edges)}')
print(f'Missing: {len(fc_nondec_trans - edges)}')

# Check acyclicity of fc-nondecreasing
adj = defaultdict(set)
nodes = set()
for s, sp in fc_nondec_trans:
    adj[s].add(sp); nodes.add(s); nodes.add(sp)
indeg = {n: 0 for n in nodes}
for s, sp in fc_nondec_trans:
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
    print('Fc-nondec transitions: ACYCLIC')
    rank = {}
    for u in reversed(order):
        rank[u] = max((rank[v]+1 for v in adj[u]), default=0)
    print(f'Max rank: {max(rank.values())}')
else:
    print(f'Fc-nondec transitions: HAS CYCLE')
