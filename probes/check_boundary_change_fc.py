#!/usr/bin/env python3
"""
Check: do boundary-changing bad steps at constant FutureFc always decrease fc?
If so, the segment measure is just fc.

Also check: do boundary-changing const-future steps always have fc(c') < fc(c)?
Or fc(c') <= fc(c)?
"""

from itertools import product as cartesian
from collections import defaultdict, Counter

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

n = 9; ms = [2] + [3]*(n-2) + [2]
def get_table(i):
    if i == 0: return TBotVal
    elif i == 1: return TLowVal
    elif i + 1 == n: return TTopVal
    elif i + 2 == n: return THighVal
    else: return TMidVal
def fc(c): return sum(1 for j in range(n) if c[j] != c[(j+1)%n])
def enc6(c): return (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])
def step(c, i):
    L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]; out = get_table(i)(L,S,R)
    if out != S: new_c = list(c); new_c[i] = out; return tuple(new_c)
    return None

all_configs = list(cartesian(*(range(m) for m in ms)))
all_succ = defaultdict(list)
for c in all_configs:
    for i in range(n):
        succ = step(c, i)
        if succ is not None: all_succ[c].append(succ)

def tarjan(nodes, adj):
    idx=[0];stack=[];ll={};im={};ons=set();sccs=[]
    for s in nodes:
        if s in im: continue
        cs=[(s,iter(adj.get(s,[])))]; im[s]=ll[s]=idx[0]; idx[0]+=1
        stack.append(s); ons.add(s)
        while cs:
            v,ch=cs[-1]
            try:
                w=next(ch)
                if w not in im:
                    im[w]=ll[w]=idx[0]; idx[0]+=1; stack.append(w); ons.add(w)
                    cs.append((w,iter(adj.get(w,[]))))
                elif w in ons: ll[v]=min(ll[v],im[w])
            except StopIteration:
                cs.pop()
                if cs: ll[cs[-1][0]]=min(ll[cs[-1][0]],ll[v])
                if ll[v]==im[v]:
                    scc=[]
                    while True:
                        w=stack.pop(); ons.discard(w); scc.append(w)
                        if w==v: break
                    sccs.append(scc)
    return sccs

sccs = tarjan(all_configs, all_succ)
terminal = []
for i, scc in enumerate(sccs):
    ss = set(scc)
    if not any(w not in ss for v in scc for w in all_succ.get(v,[])): terminal.append(i)
good_set = set(sccs[terminal[0]])
bad_configs = [c for c in all_configs if c not in good_set]
bad_set = set(bad_configs)
bad_adj = defaultdict(list)
for c in bad_configs:
    for succ in all_succ.get(c, []):
        if succ in bad_set: bad_adj[c].append(succ)

fc_cache = {c: fc(c) for c in bad_configs}
future_fc = {}
for c in bad_configs:
    visited = {c}; queue = [c]; max_fc = fc_cache[c]; qi = 0
    while qi < len(queue):
        v = queue[qi]; qi += 1
        for w in bad_adj.get(v, []):
            if w not in visited:
                visited.add(w); queue.append(w)
                if fc_cache[w] > max_fc: max_fc = fc_cache[w]
    future_fc[c] = max_fc

# For SEGMENTS (not individual steps):
# fixedBoundary chain (boundary preserved) + boundary-changing step
# Does the segment decrease FutureFc?

# Build fixedBoundary adjacency (const future + same boundary)
fixedbd_adj = defaultdict(list)
bdchange_adj = defaultdict(list)
for c in bad_configs:
    for succ in bad_adj.get(c, []):
        if future_fc[c] == future_fc[succ]:
            if enc6(c) == enc6(succ):
                fixedbd_adj[c].append(succ)
            else:
                bdchange_adj[c].append(succ)

# Segment: x ->fixedbd^* z ->bdchange y
# Check: does FutureFc(y) < FutureFc(x)?
# Since all steps are const-future, FutureFc(z) = FutureFc(x).
# The bdchange step z->y: also const-future, so FutureFc(y) = FutureFc(z) = FutureFc(x).
# So FutureFc does NOT decrease across the segment!

# Instead, does fc decrease? Check: fc(y) < fc(x)?
# Or better: does the BOUNDARY RANK decrease?

# Since we can't use boundary rank (cycles), let's check fc.
# x ->fixedbd^* z: boundary preserved, fc could change
# z ->bdchange y: boundary changed

# What about: does the segment decrease (n-fc)?
# fixedBoundary chain preserves boundary and has fc <= (from fixedBoundary_fc_le)
# So fc(z) <= fc(x), meaning n-fc(z) >= n-fc(x).
# bdchange step: fc(y) vs fc(z)? Could be anything.

# Let me just check computationally: does SOME measure decrease across segments?
segment_fc_change = Counter()
total_segments = 0

for x in bad_configs:
    # Find all z reachable from x via fixedBoundary
    visited = {x}
    queue = [x]
    qi = 0
    while qi < len(queue):
        v = queue[qi]; qi += 1
        for w in fixedbd_adj.get(v, []):
            if w not in visited:
                visited.add(w)
                queue.append(w)

    for z in visited:
        for y in bdchange_adj.get(z, []):
            total_segments += 1
            delta_fc = fc_cache[y] - fc_cache[x]
            segment_fc_change[delta_fc] += 1

print(f"Total boundary segments: {total_segments}")
print(f"fc change distribution (fc(y) - fc(x)):")
for k in sorted(segment_fc_change.keys()):
    print(f"  {k:+d}: {segment_fc_change[k]}")

# Check if ANY segment increases fc
positive = sum(v for k,v in segment_fc_change.items() if k > 0)
zero = segment_fc_change.get(0, 0)
negative = sum(v for k,v in segment_fc_change.items() if k < 0)
print(f"\nfc(y) > fc(x): {positive}")
print(f"fc(y) = fc(x): {zero}")
print(f"fc(y) < fc(x): {negative}")

if positive == 0:
    print("\n*** ALL segments have fc(y) <= fc(x)! ***")
    if zero == 0:
        print("*** ALL segments STRICTLY decrease fc! ***")
        print("*** Segment WF via InvImage on fc! ***")
    else:
        print("Some segments have fc(y) = fc(x).")
        print("Need fc < fc_x OR (fc equal and something else decreases)")
