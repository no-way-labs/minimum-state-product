#!/usr/bin/env python3
"""Check if fc + psi or other combinations decrease on ALL bad steps."""

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
bad_adj = defaultdict(list)
for c in bad_set:
    for s in all_succ.get(c,[]):
        if s in bad_set: bad_adj[c].append(s)

# Check various measures on ALL bad steps
fc_cache = {c:fc(c) for c in bad_set}
psi_cache = {c:psi(c) for c in bad_set}

measures = {
    'fc+psi': lambda c: fc_cache[c] + psi_cache[c],
    'n-fc+psi': lambda c: (n - fc_cache[c]) + psi_cache[c],
    '2*fc+psi': lambda c: 2*fc_cache[c] + psi_cache[c],
    'fc+2*psi': lambda c: fc_cache[c] + 2*psi_cache[c],
    '3*fc+psi': lambda c: 3*fc_cache[c] + psi_cache[c],
    '3*(n-fc)+psi': lambda c: 3*(n - fc_cache[c]) + psi_cache[c],
    'n-fc+2*psi': lambda c: (n-fc_cache[c]) + 2*psi_cache[c],
    'psi': lambda c: psi_cache[c],
    '2*psi-fc': lambda c: 2*psi_cache[c] - fc_cache[c],
    'psi-fc': lambda c: psi_cache[c] - fc_cache[c],
}

total = sum(len(v) for v in bad_adj.values())
for name, mu in measures.items():
    violations = 0
    for c in bad_set:
        for s in bad_adj.get(c,[]):
            if mu(s) >= mu(c):
                violations += 1
    print(f"  {name}: {violations}/{total} violations")

# Try wider search
print("\nSearching a*fc + b*psi for a in -10..10, b in -10..10:")
best = (total, 0, 0)
for a in range(-10, 11):
    for b in range(-10, 11):
        if a == 0 and b == 0: continue
        violations = 0
        for c in bad_set:
            for s in bad_adj.get(c,[]):
                v_c = a * fc_cache[c] + b * psi_cache[c]
                v_s = a * fc_cache[s] + b * psi_cache[s]
                if v_s >= v_c:
                    violations += 1
        if violations < best[0]:
            best = (violations, a, b)
            if violations == 0:
                break
    if best[0] == 0:
        break

print(f"Best: {best[1]}*fc + {best[2]}*psi has {best[0]} violations")
