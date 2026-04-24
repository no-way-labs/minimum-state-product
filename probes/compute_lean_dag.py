#!/usr/bin/env python3
"""Compute the fc-nondec boundary DAG using LEAN's TMidVal (2,1,1)=2.
Also compute the rank function and the full transition set."""
from collections import defaultdict, deque

def encode(c0, c1, c2, cN3, cN2, cN1):
    return ((((c0 * 3 + c1) * 3 + c2) * 3 + cN3) * 3 + cN2) * 2 + cN1

def delta_fc(L, S, R, S_new):
    return ((1 if L != S_new else 0) - (1 if L != S else 0) +
            (1 if S_new != R else 0) - (1 if S != R else 0))

# LEAN's tables (TMidVal(2,1,1)=2, NOT 0)
def TBotVal(L,S,R):
    t={(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    return t.get((L,S,R),0)
def TLowVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    return t.get((L,S,R),0)
def TMidVal(L,S,R):
    # THIS IS LEAN's VERSION: (2,1,1)=2
    t={(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,
       (1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,
       (2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L,S,R),0)
def THighVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    return t.get((L,S,R),0)
def TTopVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    return t.get((L,S,R),0)

# Compute ALL boundary transitions (not just fc-nondec)
all_trans = set()
fc_nondec_trans = set()
for c0 in range(2):
 for c1 in range(3):
  for c2 in range(3):
   for cN3 in range(3):
    for cN2 in range(3):
     for cN1 in range(2):
      se = encode(c0,c1,c2,cN3,cN2,cN1)
      # P0
      nc0=TBotVal(cN1,c0,c1)
      if nc0!=c0:
        se2 = encode(nc0,c1,c2,cN3,cN2,cN1)
        all_trans.add((se, se2))
        if delta_fc(cN1,c0,c1,nc0)>=0: fc_nondec_trans.add((se, se2))
      # P1
      nc1=TLowVal(c0,c1,c2)
      if nc1!=c1:
        se2 = encode(c0,nc1,c2,cN3,cN2,cN1)
        all_trans.add((se, se2))
        if delta_fc(c0,c1,c2,nc1)>=0: fc_nondec_trans.add((se, se2))
      # P2
      for c3 in range(3):
        nc2=TMidVal(c1,c2,c3)
        if nc2!=c2:
          se2 = encode(c0,c1,nc2,cN3,cN2,cN1)
          all_trans.add((se, se2))
          if delta_fc(c1,c2,c3,nc2)>=0: fc_nondec_trans.add((se, se2))
      # PN3
      for cn4 in range(3):
        ncN3=TMidVal(cn4,cN3,cN2)
        if ncN3!=cN3:
          se2 = encode(c0,c1,c2,ncN3,cN2,cN1)
          all_trans.add((se, se2))
          if delta_fc(cn4,cN3,cN2,ncN3)>=0: fc_nondec_trans.add((se, se2))
      # PN2
      ncN2=THighVal(cN3,cN2,cN1)
      if ncN2!=cN2:
        se2 = encode(c0,c1,c2,cN3,ncN2,cN1)
        all_trans.add((se, se2))
        if delta_fc(cN3,cN2,cN1,ncN2)>=0: fc_nondec_trans.add((se, se2))
      # PN1
      ncN1=TTopVal(cN2,cN1,c0)
      if ncN1!=cN1:
        se2 = encode(c0,c1,c2,cN3,cN2,ncN1)
        all_trans.add((se, se2))
        if delta_fc(cN2,cN1,c0,ncN1)>=0: fc_nondec_trans.add((se, se2))

print(f'All transitions: {len(all_trans)}')
print(f'Fc-nondec transitions: {len(fc_nondec_trans)}')

# Check acyclicity of fc-nondec
adj = defaultdict(set)
nodes = set(range(324))
for s, sp in fc_nondec_trans:
    adj[s].add(sp)
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

if len(order) == 324:
    print('Fc-nondec: ACYCLIC')
    rank = {}
    for u in reversed(order):
        rank[u] = max((rank[v]+1 for v in adj[u]), default=0)
    rank_list = [rank[i] for i in range(324)]
    print(f'Max rank: {max(rank_list)}')
    print(f'Rank list for Lean:')
    print(f'  [{", ".join(str(r) for r in rank_list)}]')
    print(f'\nEdge list (source, target) [{len(fc_nondec_trans)} edges]:')
    sorted_edges = sorted(fc_nondec_trans)
    print(f'  [{", ".join(f"({s}, {t})" for s,t in sorted_edges)}]')
else:
    print(f'Fc-nondec: HAS CYCLE - sorted {len(order)} of 324')

# Check acyclicity of ALL transitions
adj_all = defaultdict(set)
for s, sp in all_trans:
    adj_all[s].add(sp)
indeg_all = {n: 0 for n in range(324)}
for s, sp in all_trans:
    indeg_all[sp] += 1
q_all = deque([n for n in range(324) if indeg_all[n] == 0])
order_all = []
while q_all:
    u = q_all.popleft()
    order_all.append(u)
    for v in adj_all[u]:
        indeg_all[v] -= 1
        if indeg_all[v] == 0: q_all.append(v)
if len(order_all) == 324:
    print(f'\nAll transitions: ACYCLIC')
    rank_all = {}
    for u in reversed(order_all):
        rank_all[u] = max((rank_all[v]+1 for v in adj_all[u]), default=0)
    print(f'Max rank: {max(rank_all.values())}')
else:
    print(f'\nAll transitions: HAS CYCLE - sorted {len(order_all)} of 324')
