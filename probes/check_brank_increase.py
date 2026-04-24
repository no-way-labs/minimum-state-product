#!/usr/bin/env python3
"""
Check: does sixStateRank (boundary rank) ever INCREASE on a bad step?
If boundary rank is non-increasing on all bad steps, then no cycle can have
any B1-B4 step (since those strictly decrease boundary rank), and all steps
in a hypothetical cycle would be fc-nonpositive, leading to contradiction.
"""

from itertools import product as cartesian
from collections import defaultdict, Counter

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

# SixStateRank from SixTuple.lean
sixStateRankVals = [24,23,0,22,0,0,21,20,0,19,0,0,18,17,0,0,0,0,16,15,0,14,0,0,13,12,0,11,0,0,10,9,0,0,0,0,8,7,6,5,4,0,3,2,1,0,0,0,0,0,0,0,0,0,24,23,0,22,0,0,21,20,0,19,18,17,16,0,0,0,0,0,15,14,0,13,12,11,10,9,8,7,6,5,4,0,0,0,0,0,3,2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,23,0,22,0,0,21,20,0,19,18,17,0,0,0,0,0,0,16,15,14,13,12,11,10,9,8,7,6,5,4,0,0,0,0,0,3,2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,23,22,21,20,0,19,18,17,16,15,14,13,12,0,0,0,0,11,10,9,8,0,0,0,7,6,5,4,0,0,3,0,0,2,0,0,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,0,0,0,0,0,0,0,0,0,0,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,0,0,0,0,0,0,0,0,0,0,0,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,0,0,0,0,0,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,0,0]

n = 9; ms = [2]+[3]*(n-2)+[2]
def get_table(i):
    if i==0: return TBotVal
    elif i==1: return TLowVal
    elif i+1==n: return TTopVal
    elif i+2==n: return THighVal
    else: return TMidVal
def fc(c): return sum(1 for j in range(n) if c[j]!=c[(j+1)%n])
def enc6(c): return (c[0],c[1],c[2],c[n-3],c[n-2],c[n-1])
def enc6_to_int(t):
    c0,c1,c2,cN3,cN2,cN1 = t
    return ((((c0*3+c1)*3+c2)*3+cN3)*3+cN2)*2+cN1
def brank(c): return sixStateRankVals[enc6_to_int(enc6(c))]
def step(c,i):
    L=c[(i-1)%n]; S=c[i]; R=c[(i+1)%n]; out=get_table(i)(L,S,R)
    if out!=S: nc=list(c); nc[i]=out; return tuple(nc)
    return None

all_configs = list(cartesian(*(range(m) for m in ms)))
all_succ = defaultdict(list)
for c in all_configs:
    for i in range(n):
        s = step(c,i)
        if s: all_succ[c].append(s)

def tarjan(nodes,adj):
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
for i,scc in enumerate(sccs):
    ss = set(scc)
    if not any(w not in ss for v in scc for w in all_succ.get(v,[])): terminal.append(i)
good_set = set(sccs[terminal[0]])
bad_set = set(c for c in all_configs if c not in good_set)

# Check boundary rank changes on ALL bad steps
brank_changes = Counter()
brank_increase_count = 0
total = 0
examples = []

for c in bad_set:
    for s in all_succ.get(c, []):
        if s in bad_set:
            total += 1
            br_c = brank(c)
            br_s = brank(s)
            delta = br_s - br_c
            brank_changes[delta] += 1
            if br_s > br_c:
                brank_increase_count += 1
                if len(examples) < 5:
                    examples.append((c, s, br_c, br_s))

print(f"Total bad steps: {total}")
print(f"Boundary rank increases: {brank_increase_count}")
print(f"Boundary rank changes:")
for k in sorted(brank_changes.keys()):
    print(f"  {k:+d}: {brank_changes[k]}")

if brank_increase_count == 0:
    print("\n*** Boundary rank NEVER increases on bad steps! ***")
    print("*** This means sixStateRank is a non-increasing quantity! ***")
else:
    print(f"\nExamples of boundary rank increase:")
    for c, s, bc, bs in examples:
        print(f"  c={c}, s={s}: brank {bc} -> {bs}")
        print(f"    boundary: {enc6(c)} -> {enc6(s)}")
        print(f"    fc: {fc(c)} -> {fc(s)}")
