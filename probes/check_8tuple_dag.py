#!/usr/bin/env python3
"""Check if 8-tuple boundary (positions 0,1,2,3,N-4,N-3,N-2,N-1) transitions form a DAG.
State space: 2*3*3*3*3*3*3*2 = 2916"""

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

def enc8(c0,c1,c2,c3,cN4,cN3,cN2,cN1):
    return ((((((c0*3+c1)*3+c2)*3+c3)*3+cN4)*3+cN3)*3+cN2)*2+cN1

# Collect ALL boundary-changing transitions on 8-tuple
# Positions: 0(TBot), 1(TLow), 2(TMid), 3(TMid), N-4(TMid), N-3(TMid), N-2(THigh), N-1(TTop)
# For n>=9: position 3 has left=2(boundary), right=4(interior for 6-tuple, but position 4 might not be in 8-tuple)
# Wait, for position 3: left=2 (in boundary), right=4. Position 4 is NOT in the 8-tuple if n>=10.
# For position N-4: left=N-5 (not in boundary), right=N-3 (in boundary)
# So positions 3 and N-4 STILL have one interior neighbor!

# For n=9:
# Positions: 0,1,2,3,4=N-5,5=N-4,6=N-3,7=N-2,8=N-1
# Position 3: left=2(boundary), right=4=N-5(boundary if included)
# Position 5=N-4: left=4=N-5(boundary), right=6=N-3(boundary)
# At n=9, positions 0,1,2,3,5,6,7,8 would cover everything EXCEPT position 4.
# Position 3's right neighbor is position 4 (interior).
# Position 5's left neighbor is position 4 (interior).

# So even with 8 positions, position 3 and N-4 have one interior neighbor each (position 4 for n=9).
# Unless we go to 10 positions... but then for n=10, the same problem at positions 4 and 5.

# Actually for n>=10:
# 8 boundary positions: 0,1,2,3 and N-4,N-3,N-2,N-1
# Position 3: right=4 (interior, NOT in boundary since 4 < N-4 for n>=10)
# Position N-4: left=N-5 (interior)
# So STILL two interior-dependent positions!

# For n=9:
# 8 boundary = 0,1,2,3,5,6,7,8 (all except 4)
# Position 3: right=4 (the ONLY interior position)
# Position 5: left=4 (same)
# So BOTH positions 3 and 5 depend on position 4.

# For 8-tuple to work, I need position 3's right and position N-4's left to be in the boundary.
# Position 3's right = position 4. For this to be in the boundary: 4 >= N-4, i.e., N <= 8.
# But we need n >= 9!

# So 8-tuple doesn't help for n>=10 (still has interior neighbors).
# For n=9 specifically, we'd need a 9-tuple (all positions), making it a full config check.

print("8-tuple approach doesn't work for general n>=9.")
print("Positions 3 and N-4 still have interior neighbors for n>=10.")
print()
print("However, for n=9 specifically, only position 4 is interior.")
print("Let's check if the 8-tuple DAG works for n=9 (where 3's right and 5's left are both pos 4).")
print()

# For n=9: 8 boundary positions = {0,1,2,3,5,6,7,8}
# Position 4 is the only interior position
# Position 3 uses TMid with L=c2, S=c3, R=c4 (c4 is interior)
# Position 5 uses TMid with L=c4 (interior), S=c5=cN4, R=c6=cN3

# Transitions at each position (for n=9):
# Pos 0: TBot(c8, c0, c1) - fully boundary
# Pos 1: TLow(c0, c1, c2) - fully boundary
# Pos 2: TMid(c1, c2, c3) - fully boundary (c3 is in 8-tuple)
# Pos 3: TMid(c2, c3, c4) - c4 is interior!
# Pos 5: TMid(c4, c5, c6) - c4 is interior!
# Pos 6: TMid(c5, c6, c7) - fully boundary (for 8-tuple)
# Pos 7: THigh(c6, c7, c8) - fully boundary
# Pos 8: TTop(c7, c8, c0) - fully boundary

# So for positions 3 and 5, we need to enumerate over c4 ∈ {0,1,2}

# State: (c0,c1,c2,c3,c5,c6,c7,c8) = 2*3*3*3*3*3*3*2 = 2916
trans8 = set()
for c0 in range(2):
 for c1 in range(3):
  for c2 in range(3):
   for c3 in range(3):
    for c5 in range(3):  # N-4
     for c6 in range(3):  # N-3
      for c7 in range(3):  # N-2
       for c8 in range(2):  # N-1
        src = enc8(c0,c1,c2,c3,c5,c6,c7,c8)
        # Pos 0: TBot(c8, c0, c1)
        v = TBotVal(c8, c0, c1)
        if v != c0 and v < 2:
            trans8.add((src, enc8(v,c1,c2,c3,c5,c6,c7,c8)))
        # Pos 1: TLow(c0, c1, c2)
        v = TLowVal(c0, c1, c2)
        if v != c1 and v < 3:
            trans8.add((src, enc8(c0,v,c2,c3,c5,c6,c7,c8)))
        # Pos 2: TMid(c1, c2, c3)
        v = TMidVal(c1, c2, c3)
        if v != c2 and v < 3:
            trans8.add((src, enc8(c0,c1,v,c3,c5,c6,c7,c8)))
        # Pos 3: TMid(c2, c3, c4) for all c4
        for c4 in range(3):
            v = TMidVal(c2, c3, c4)
            if v != c3 and v < 3:
                trans8.add((src, enc8(c0,c1,c2,v,c5,c6,c7,c8)))
        # Pos 5: TMid(c4, c5, c6) for all c4
        for c4 in range(3):
            v = TMidVal(c4, c5, c6)
            if v != c5 and v < 3:
                trans8.add((src, enc8(c0,c1,c2,c3,v,c6,c7,c8)))
        # Pos 6: TMid(c5, c6, c7)
        v = TMidVal(c5, c6, c7)
        if v != c6 and v < 3:
            trans8.add((src, enc8(c0,c1,c2,c3,c5,v,c7,c8)))
        # Pos 7: THigh(c6, c7, c8)
        v = THighVal(c6, c7, c8)
        if v != c7 and v < 3:
            trans8.add((src, enc8(c0,c1,c2,c3,c5,c6,v,c8)))
        # Pos 8: TTop(c7, c8, c0)
        v = TTopVal(c7, c8, c0)
        if v != c8 and v < 2:
            trans8.add((src, enc8(c0,c1,c2,c3,c5,c6,c7,v)))

print(f"Total 8-tuple transitions (n=9): {len(trans8)}")

# Check DAG
from collections import defaultdict, deque
adj = defaultdict(list)
for s, t in trans8:
    adj[s].append(t)

all_nodes = set(range(2916))
in_degree = defaultdict(int)
for s, t in trans8:
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
    print("8-tuple transitions form a DAG (n=9 specific)!")
    rank = defaultdict(int)
    for v in reversed(topo_order):
        for w in adj[v]:
            rank[v] = max(rank[v], rank[w] + 1)
    print(f"Max rank: {max(rank.values()) if rank else 0}")
else:
    print(f"NOT a DAG ({len(topo_order)}/{len(all_nodes)} sorted)")
