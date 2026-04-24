#!/usr/bin/env python3
"""Check if (fc-non-increasing ∪ B1-B4) boundary transitions form a DAG."""

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
def enc(c0,c1,c2,cN3,cN2,cN1):
    return ((((c0*3+c1)*3+c2)*3+cN3)*3+cN2)*2+cN1
def localFcBefore(L,S,R):
    return frontierBit(L,S) + frontierBit(S,R)
def localFcAfter(L,S,R,out):
    return frontierBit(L,out) + frontierBit(out,R)

# B1-B4 transitions (fc-increasing at boundary)
b1b4_trans = set()
# B1: pos 0, L=0, S=0, R=0, out=1
# B2: pos 0, L=1, S=1, R=2, out=0
# B3: pos N-2, L=1, S=1, R=1, out=2
# B4: pos N-1, L=2, S=0, R=0, out=1

for c0 in range(2):
 for c1 in range(3):
  for c2 in range(3):
   for cN3 in range(3):
    for cN2 in range(3):
     for cN1 in range(2):
      src = enc(c0,c1,c2,cN3,cN2,cN1)
      # B1: cN1=0, c0=0, c1=0 -> c0 becomes 1
      if cN1==0 and c0==0 and c1==0:
          b1b4_trans.add((src, enc(1,c1,c2,cN3,cN2,cN1)))
      # B2: cN1=1, c0=1, c1=2 -> c0 becomes 0
      if cN1==1 and c0==1 and c1==2:
          b1b4_trans.add((src, enc(0,c1,c2,cN3,cN2,cN1)))
      # B3: cN3=1, cN2=1, cN1=1 -> cN2 becomes 2
      if cN3==1 and cN2==1 and cN1==1:
          b1b4_trans.add((src, enc(c0,c1,c2,cN3,2,cN1)))
      # B4: cN2=2, cN1=0, c0=0 -> cN1 becomes 1
      if cN2==2 and cN1==0 and c0==0:
          b1b4_trans.add((src, enc(c0,c1,c2,cN3,cN2,1)))

# fc-non-increasing boundary transitions
fc_noninc_trans = set()
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
          d = localFcAfter(cN1,c0,c1,v) - localFcBefore(cN1,c0,c1)
          if d <= 0: fc_noninc_trans.add((src, enc(v,c1,c2,cN3,cN2,cN1)))
      # Pos 1
      v = TLowVal(c0, c1, c2)
      if v != c1 and v < 3:
          d = localFcAfter(c0,c1,c2,v) - localFcBefore(c0,c1,c2)
          if d <= 0: fc_noninc_trans.add((src, enc(c0,v,c2,cN3,cN2,cN1)))
      # Pos 2 (all R)
      for R in range(3):
          v = TMidVal(c1, c2, R)
          if v != c2 and v < 3:
              d = localFcAfter(c1,c2,R,v) - localFcBefore(c1,c2,R)
              if d <= 0: fc_noninc_trans.add((src, enc(c0,c1,v,cN3,cN2,cN1)))
      # Pos N-3 (all L)
      for L in range(3):
          v = TMidVal(L, cN3, cN2)
          if v != cN3 and v < 3:
              d = localFcAfter(L,cN3,cN2,v) - localFcBefore(L,cN3,cN2)
              if d <= 0: fc_noninc_trans.add((src, enc(c0,c1,c2,v,cN2,cN1)))
      # Pos N-2
      v = THighVal(cN3, cN2, cN1)
      if v != cN2 and v < 3:
          d = localFcAfter(cN3,cN2,cN1,v) - localFcBefore(cN3,cN2,cN1)
          if d <= 0: fc_noninc_trans.add((src, enc(c0,c1,c2,cN3,v,cN1)))
      # Pos N-1
      v = TTopVal(cN2, cN1, c0)
      if v != cN1 and v < 2:
          d = localFcAfter(cN2,cN1,c0,v) - localFcBefore(cN2,cN1,c0)
          if d <= 0: fc_noninc_trans.add((src, enc(c0,c1,c2,cN3,cN2,v)))

combined = fc_noninc_trans | b1b4_trans
print(f"B1-B4 transitions: {len(b1b4_trans)}")
print(f"fc-non-increasing transitions: {len(fc_noninc_trans)}")
print(f"Combined (fc-noninc ∪ B1-B4): {len(combined)}")

# Check for cycles
from collections import defaultdict, deque
adj = defaultdict(list)
for s, t in combined:
    adj[s].append(t)

in_degree = defaultdict(int)
for s, t in combined:
    in_degree[t] += 1

# Ensure all nodes
for v in range(324):
    if v not in in_degree:
        in_degree[v] = 0

queue = deque([v for v in range(324) if in_degree[v] == 0])
topo_order = []
while queue:
    v = queue.popleft()
    topo_order.append(v)
    for w in adj[v]:
        in_degree[w] -= 1
        if in_degree[w] == 0:
            queue.append(w)

if len(topo_order) == 324:
    print("RESULT: (fc-noninc ∪ B1-B4) is a DAG!")
    # Compute rank
    rank = [0] * 324
    for v in reversed(topo_order):
        for w in adj[v]:
            rank[v] = max(rank[v], rank[w] + 1)
    print(f"Max rank: {max(rank)}")
    print(f"Rank values: {rank}")

    # Verify: ALL edges have strictly decreasing rank
    fail = 0
    for s, t in combined:
        if rank[t] >= rank[s]:
            fail += 1
            print(f"  RANK FAIL: {s} -> {t}: rank {rank[s]} -> {rank[t]}")
    print(f"Rank decrease failures: {fail}")
else:
    print(f"RESULT: NOT a DAG ({len(topo_order)}/324 sorted)")

    # Find SCCs
    import sys
    sys.setrecursionlimit(10000)
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

    for v in range(324):
        if v not in index_map:
            strongconnect(v)

    print(f"Non-trivial SCCs: {len(sccs)}")
    for scc in sccs[:10]:
        print(f"  SCC size {len(scc)}: {scc}")
