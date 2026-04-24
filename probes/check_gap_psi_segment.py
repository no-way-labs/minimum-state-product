#!/usr/bin/env python3
"""Check: within constant-FutureFc, does (F-fc, psi) lex strictly decrease
on the SEGMENT relation: ReflTransGen nonneg then one neg step?"""

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

def cup2FrontierTypeVal(a, b):
    if a == b: return 0
    return (b + 3 - a) % 3

def cup2W1(n, j):
    if j + 1 == n: return 0
    elif j + 2 == n: return 1
    else: return j + 1

def cup2W2(n, j):
    if j + 1 == n: return 0
    elif j == 0: return n - 1
    else: return n - 1 - j

def cup2PsiWeightVal(n, j, a, b):
    if a == b: return 0
    if cup2FrontierTypeVal(a, b) == 1:
        return cup2W1(n, j)
    else:
        return cup2W2(n, j)

def cup2Psi(c, n):
    total = 0
    for j in range(n):
        jnext = (j + 1) % n
        total += cup2PsiWeightVal(n, j, c[j], c[jnext])
    return total

n = 9
ms=[2]+[3]*(n-2)+[2]
def get_table(i):
    if i==0: return TBotVal
    elif i==1: return TLowVal
    elif i+1==n: return TTopVal
    elif i+2==n: return THighVal
    else: return TMidVal
def fc(c): return sum(1 for j in range(n) if c[j]!=c[(j+1)%n])
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

# Tarjan SCC
adj = defaultdict(list)
for c in all_configs:
    for s in all_succ[c]:
        adj[c].append(s)

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
    for s in all_succ.get(c,[]):
        if s in bad_set: bad_adj[c].append(s)

fc_cache = {c:fc(c) for c in bad_set}
wpsi_cache = {c:cup2Psi(c,n) for c in bad_set}

# Compute FutureFc
future_fc = {}
for c in bad_set:
    visited = {c}; queue = [c]; mf = fc_cache[c]; qi = 0
    while qi < len(queue):
        v = queue[qi]; qi += 1
        for w in bad_adj.get(v,[]):
            if w not in visited:
                visited.add(w); queue.append(w)
                if fc_cache[w] > mf: mf = fc_cache[w]
    future_fc[c] = mf

# Within constant-FutureFc, check (F-fc, wpsi) lex on ALL const-future steps
cf_violations = 0
cf_total = 0
for c in bad_set:
    F = future_fc[c]
    for s in bad_adj.get(c,[]):
        if future_fc[s] != F: continue  # not const-future
        cf_total += 1
        gap_c = F - fc_cache[c]
        gap_s = F - fc_cache[s]
        wpsi_c = wpsi_cache[c]
        wpsi_s = wpsi_cache[s]
        # Want (gap_s, wpsi_s) <lex (gap_c, wpsi_c)
        # i.e., gap_s < gap_c, OR gap_s = gap_c and wpsi_s < wpsi_c
        if gap_s < gap_c:
            pass
        elif gap_s == gap_c and wpsi_s < wpsi_c:
            pass
        else:
            cf_violations += 1

print(f'(F-fc, wpsi) lex on const-future steps: {cf_violations}/{cf_total} violations')

# Also check (F-fc, n-fc, wpsi) triple lex
cf_violations2 = 0
for c in bad_set:
    F = future_fc[c]
    for s in bad_adj.get(c,[]):
        if future_fc[s] != F: continue
        gap_c = F - fc_cache[c]
        gap_s = F - fc_cache[s]
        nfc_c = n - fc_cache[c]
        nfc_s = n - fc_cache[s]
        wpsi_c = wpsi_cache[c]
        wpsi_s = wpsi_cache[s]
        # (gap, nfc, wpsi) lex
        if gap_s < gap_c: pass
        elif gap_s == gap_c and nfc_s < nfc_c: pass
        elif gap_s == gap_c and nfc_s == nfc_c and wpsi_s < wpsi_c: pass
        else: cf_violations2 += 1

print(f'(F-fc, n-fc, wpsi) lex on const-future steps: {cf_violations2}/{cf_total} violations')

# Check (n-fc, wpsi) lex on const-future steps
cf_violations3 = 0
for c in bad_set:
    F = future_fc[c]
    for s in bad_adj.get(c,[]):
        if future_fc[s] != F: continue
        nfc_c = n - fc_cache[c]
        nfc_s = n - fc_cache[s]
        wpsi_c = wpsi_cache[c]
        wpsi_s = wpsi_cache[s]
        if nfc_s < nfc_c: pass
        elif nfc_s == nfc_c and wpsi_s < wpsi_c: pass
        else: cf_violations3 += 1

print(f'(n-fc, wpsi) lex on const-future steps: {cf_violations3}/{cf_total} violations')
