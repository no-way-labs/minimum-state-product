#!/usr/bin/env python3
"""Check: are neg const-future steps always boundary-PRESERVING or always boundary-CHANGING?"""

from itertools import product as cartesian
from collections import defaultdict

def TBotVal(L,S,R):
    t = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    return t.get((L,S,R), 0)
def TLowVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    return t.get((L,S,R), 0)
def TMidVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L,S,R), 0)
def THighVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    return t.get((L,S,R), 0)
def TTopVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    return t.get((L,S,R), 0)

n = 9
ms=[2]+[3]*(n-2)+[2]
def get_table(i):
    if i==0: return TBotVal
    elif i==1: return TLowVal
    elif i+1==n: return TTopVal
    elif i+2==n: return THighVal
    else: return TMidVal
def fc(c): return sum(1 for j in range(n) if c[j]!=c[(j+1)%n])
def enc6(c): return (c[0],c[1],c[2],c[n-3],c[n-2],c[n-1])
def step(c,i):
    L=c[(i-1)%n]; S=c[i]; R=c[(i+1)%n]; out=get_table(i)(L,S,R)
    if out!=S: nc=list(c); nc[i]=out; return tuple(nc)
    return None

all_configs = list(cartesian(*(range(m) for m in ms)))
all_succ = defaultdict(list)
for c in all_configs:
    for i in range(n):
        s = step(c,i)
        if s: all_succ[c].append((s,i))

# Find bad set
adj = defaultdict(list)
for c in all_configs:
    for s,_ in all_succ[c]: adj[c].append(s)
idx_c=[0];stack=[];ll={};im={};ons=set();sccs=[]
for s in all_configs:
    if s in im: continue
    cs_t=[(s,iter(adj.get(s,[])))]; im[s]=ll[s]=idx_c[0]; idx_c[0]+=1
    stack.append(s); ons.add(s)
    while cs_t:
        v,ch=cs_t[-1]
        try:
            w=next(ch)
            if w not in im:
                im[w]=ll[w]=idx_c[0]; idx_c[0]+=1; stack.append(w); ons.add(w)
                cs_t.append((w,iter(adj.get(w,[]))))
            elif w in ons: ll[v]=min(ll[v],im[w])
        except StopIteration:
            cs_t.pop()
            if cs_t: ll[cs_t[-1][0]]=min(ll[cs_t[-1][0]],ll[v])
            if ll[v]==im[v]:
                scc=[]
                while True:
                    w=stack.pop(); ons.discard(w); scc.append(w)
                    if w==v: break
                sccs.append(scc)
terminal = []
for i,scc in enumerate(sccs):
    ss = set(scc)
    if not any(w not in ss for v in scc for w in adj.get(v,[])): terminal.append(i)
good_set = set(sccs[terminal[0]])
bad_set = set(c for c in all_configs if c not in good_set)
bad_adj = defaultdict(list)
for c in bad_set:
    for s,i in all_succ.get(c,[]):
        if s in bad_set: bad_adj[c].append((s,i))

fc_cache = {c:fc(c) for c in bad_set}
future_fc = {}
for c in bad_set:
    visited={c}; queue=[c]; mf=fc_cache[c]; qi=0
    while qi<len(queue):
        v=queue[qi]; qi+=1
        for w,_ in bad_adj.get(v,[]):
            if w not in visited:
                visited.add(w); queue.append(w)
                if fc_cache[w]>mf: mf=fc_cache[w]
    future_fc[c] = mf

neg_cf_bdchange = 0
neg_cf_bdpreserve = 0
neg_cf_positions = defaultdict(int)
for c in bad_set:
    for s, i in bad_adj.get(c,[]):
        if future_fc[s] == future_fc[c] and fc_cache[s] < fc_cache[c]:
            # neg const-future step at position i
            if enc6(s) != enc6(c):
                neg_cf_bdchange += 1
            else:
                neg_cf_bdpreserve += 1
            neg_cf_positions[i] += 1

print(f'Neg const-future steps: boundary-change={neg_cf_bdchange}, boundary-preserve={neg_cf_bdpreserve}')
print(f'Neg CF by position: {dict(sorted(neg_cf_positions.items()))}')
# Positions 0,1,2 and n-3,n-2,n-1 are boundary; 3..n-4 are interior
boundary_neg = sum(v for k,v in neg_cf_positions.items() if k <= 2 or k >= n-3)
interior_neg = sum(v for k,v in neg_cf_positions.items() if 3 <= k <= n-4)
print(f'Boundary position neg CF: {boundary_neg}, Interior position neg CF: {interior_neg}')
