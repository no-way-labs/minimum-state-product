#!/usr/bin/env python3
"""
Check if the constant-FutureFc DAG rank is a function of (FutureFc, n-fc, psi) somehow.
"""

from itertools import product as cartesian
from collections import defaultdict
import sys

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

n=9; ms=[2]+[3]*(n-2)+[2]
def get_table(i):
    if i==0: return TBotVal
    elif i==1: return TLowVal
    elif i+1==n: return TTopVal
    elif i+2==n: return THighVal
    else: return TMidVal
def fc(c): return sum(1 for j in range(n) if c[j]!=c[(j+1)%n])
def psi_term(c,j): return 1 if c[j]!=c[(j+1)%n] and c[j]!=c[(j-1)%n] else 0
def psi(c): return sum(psi_term(c,j) for j in range(n))
def step(c,i):
    L=c[(i-1)%n]; S=c[i]; R=c[(i+1)%n]; out=get_table(i)(L,S,R)
    if out!=S: nc=list(c); nc[i]=out; return tuple(nc)
    return None

all_configs=list(cartesian(*(range(m) for m in ms)))
all_succ=defaultdict(list)
for c in all_configs:
    for i in range(n):
        s=step(c,i)
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

sccs=tarjan(all_configs,all_succ)
terminal=[]
for i,scc in enumerate(sccs):
    ss=set(scc)
    if not any(w not in ss for v in scc for w in all_succ.get(v,[])): terminal.append(i)
good_set=set(sccs[terminal[0]])
bad_set=set(c for c in all_configs if c not in good_set)
bad_adj=defaultdict(list)
for c in bad_set:
    for s in all_succ.get(c,[]):
        if s in bad_set: bad_adj[c].append(s)

fc_cache={c:fc(c) for c in bad_set}
psi_cache={c:psi(c) for c in bad_set}
future_fc={}
for c in bad_set:
    visited={c}; queue=[c]; mf=fc_cache[c]; qi=0
    while qi<len(queue):
        v=queue[qi]; qi+=1
        for w in bad_adj.get(v,[]):
            if w not in visited:
                visited.add(w); queue.append(w)
                if fc_cache[w]>mf: mf=fc_cache[w]
    future_fc[c]=mf

constfuture_adj=defaultdict(list)
for c in bad_set:
    for s in bad_adj.get(c,[]):
        if future_fc[c]==future_fc[s]:
            constfuture_adj[c].append(s)

sys.setrecursionlimit(20000)
cf_rank={}
def compute_cf_rank(c):
    if c in cf_rank: return cf_rank[c]
    cf_rank[c]=-1
    best=0
    for s in constfuture_adj.get(c,[]):
        r=compute_cf_rank(s); best=max(best,r+1)
    cf_rank[c]=best
    return best
for c in bad_set: compute_cf_rank(c)

# Check if cf_rank = some function of (FutureFc, n-fc, psi)
from collections import Counter
groups = defaultdict(list)
for c in bad_set:
    key = (future_fc[c], n-fc_cache[c], psi_cache[c])
    groups[key].append(cf_rank[c])

print("Groups by (FutureFc, n-fc, psi):")
max_spread = 0
for key in sorted(groups.keys()):
    vals = groups[key]
    mn, mx = min(vals), max(vals)
    spread = mx - mn
    if spread > max_spread:
        max_spread = spread
    if spread > 0:
        print(f"  {key}: ranks {mn}..{mx} (spread {spread}), count {len(vals)}")

print(f"\nMax spread: {max_spread}")
if max_spread == 0:
    print("cf_rank IS a function of (FutureFc, n-fc, psi)!")
    # Print the formula
    formula = {}
    for key in sorted(groups.keys()):
        formula[key] = groups[key][0]
    print("Formula:")
    for key, val in sorted(formula.items()):
        print(f"  {key} -> {val}")
