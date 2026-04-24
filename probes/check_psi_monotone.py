#!/usr/bin/env python3
"""Check if psi is non-increasing on ALL bad steps (or all steps)."""

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

# Check psi changes on ALL steps (not just bad steps)
psi_changes_all = Counter()
psi_changes_bad = Counter()
psi_changes_nonneg = Counter()
psi_changes_neg = Counter()

for c in all_configs:
    for s in all_succ.get(c,[]):
        dp = psi(s) - psi(c)
        psi_changes_all[dp] += 1
        if c in bad_set and s in bad_set:
            psi_changes_bad[dp] += 1
            if fc(s) >= fc(c):
                psi_changes_nonneg[dp] += 1
            else:
                psi_changes_neg[dp] += 1

print("Psi changes on ALL steps:")
for k in sorted(psi_changes_all.keys()):
    print(f"  {k:+d}: {psi_changes_all[k]}")

print("\nPsi changes on BAD steps only:")
for k in sorted(psi_changes_bad.keys()):
    print(f"  {k:+d}: {psi_changes_bad[k]}")

print("\nPsi changes on NONNEG bad steps:")
for k in sorted(psi_changes_nonneg.keys()):
    print(f"  {k:+d}: {psi_changes_nonneg[k]}")

print("\nPsi changes on NEG bad steps:")
for k in sorted(psi_changes_neg.keys()):
    print(f"  {k:+d}: {psi_changes_neg[k]}")
