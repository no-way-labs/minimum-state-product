#!/usr/bin/env python3
"""
Check if (boundary_rank, n-fc, psi) lex works for constant-FutureFc steps.
boundary_rank = rank in the 617+12 edge DAG (max 24).
If boundary doesn't change, boundary_rank stays same, fall through to (n-fc, psi).
If boundary changes, boundary_rank MIGHT decrease...

But boundary_rank only decreases if the edge is in the 617+12 set.
For edges NOT in the 617+12 set, boundary_rank could increase!

Let me check what happens.
"""

from itertools import product as cartesian
from collections import defaultdict
import time

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

n = 9
ms = [2] + [3]*(n-2) + [2]

def get_table(i):
    if i == 0: return TBotVal
    elif i == 1: return TLowVal
    elif i + 1 == n: return TTopVal
    elif i + 2 == n: return THighVal
    else: return TMidVal

def fc(c):
    return sum(1 for j in range(n) if c[j] != c[(j+1)%n])

def psi_term(c, j):
    return 1 if c[j] != c[(j+1)%n] and c[j] != c[(j-1)%n] else 0

def psi(c):
    return sum(psi_term(c, j) for j in range(n))

def enc6(c):
    return (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])

def enc6_to_int(t):
    c0,c1,c2,cN3,cN2,cN1 = t
    return ((((c0*3+c1)*3+c2)*3+cN3)*3+cN2)*2+cN1

def step(c, i):
    L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
    out = get_table(i)(L, S, R)
    if out != S:
        new_c = list(c); new_c[i] = out; return tuple(new_c)
    return None

all_configs = list(cartesian(*(range(m) for m in ms)))
all_succ = defaultdict(list)
for c in all_configs:
    for i in range(n):
        succ = step(c, i)
        if succ is not None:
            all_succ[c].append(succ)

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
        if succ in bad_set:
            bad_adj[c].append(succ)

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

# Boundary rank from SixTuple.lean
sixStateRankVals = [24,23,0,22,0,0,21,20,0,19,0,0,18,17,0,0,0,0,16,15,0,14,0,0,13,12,0,11,0,0,10,9,0,0,0,0,8,7,6,5,4,0,3,2,1,0,0,0,0,0,0,0,0,0,24,23,0,22,0,0,21,20,0,19,18,17,16,0,0,0,0,0,15,14,0,13,12,11,10,9,8,7,6,5,4,0,0,0,0,0,3,2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,23,0,22,0,0,21,20,0,19,18,17,0,0,0,0,0,0,16,15,14,13,12,11,10,9,8,7,6,5,4,0,0,0,0,0,3,2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,23,22,21,20,0,19,18,17,16,15,14,13,12,0,0,0,0,11,10,9,8,0,0,0,7,6,5,4,0,0,3,0,0,2,0,0,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,0,0,0,0,0,0,0,0,0,0,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,0,0,0,0,0,0,0,0,0,0,0,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,0,0,0,0,0,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,0,0]

def boundary_rank(c):
    b6 = enc6_to_int(enc6(c))
    return sixStateRankVals[b6]

psi_cache = {c: psi(c) for c in bad_configs}

# Check measure: (boundary_rank, n-fc, psi) lex for constant-FutureFc steps
violations = 0
total = 0
violation_examples = []
for c in bad_configs:
    for succ in bad_adj.get(c, []):
        if future_fc[c] == future_fc[succ]:
            total += 1
            m_c = (boundary_rank(c), n - fc_cache[c], psi_cache[c])
            m_s = (boundary_rank(succ), n - fc_cache[succ], psi_cache[succ])
            if not (m_s < m_c):
                violations += 1
                if len(violation_examples) < 5:
                    violation_examples.append((c, succ, m_c, m_s))

print(f"Measure (boundary_rank, n-fc, psi) lex:")
print(f"  Total constant-FutureFc steps: {total}")
print(f"  Violations: {violations}")
for c, s, mc, ms_ in violation_examples:
    print(f"  c={c}, s={s}")
    print(f"    (brank, n-fc, psi): {mc} -> {ms_}")

# Try (n-fc, boundary_rank, psi) lex
violations2 = 0
for c in bad_configs:
    for succ in bad_adj.get(c, []):
        if future_fc[c] == future_fc[succ]:
            m_c = (n - fc_cache[c], boundary_rank(c), psi_cache[c])
            m_s = (n - fc_cache[succ], boundary_rank(succ), psi_cache[succ])
            if not (m_s < m_c):
                violations2 += 1

print(f"\nMeasure (n-fc, boundary_rank, psi) lex:")
print(f"  Violations: {violations2}")

# Try (n-fc, psi, boundary_rank) lex - same as adding boundary_rank to nonneg_measure
violations3 = 0
for c in bad_configs:
    for succ in bad_adj.get(c, []):
        if future_fc[c] == future_fc[succ]:
            m_c = (n - fc_cache[c], psi_cache[c], boundary_rank(c))
            m_s = (n - fc_cache[succ], psi_cache[succ], boundary_rank(succ))
            if not (m_s < m_c):
                violations3 += 1

print(f"\nMeasure (n-fc, psi, boundary_rank) lex:")
print(f"  Violations: {violations3}")

# Now try: for ALL bad steps (not just constant FutureFc)
# Does (FutureFc, n-fc, psi) lex work?
violations4 = 0
for c in bad_configs:
    for succ in bad_adj.get(c, []):
        m_c = (future_fc[c], n - fc_cache[c], psi_cache[c])
        m_s = (future_fc[succ], n - fc_cache[succ], psi_cache[succ])
        if not (m_s < m_c):
            violations4 += 1

print(f"\nMeasure (FutureFc, n-fc, psi) lex for ALL bad steps:")
print(f"  Total bad steps: {sum(len(v) for v in bad_adj.values())}")
print(f"  Violations: {violations4}")

# Try (FutureFc, boundary_rank, n-fc, psi) lex
violations5 = 0
for c in bad_configs:
    for succ in bad_adj.get(c, []):
        m_c = (future_fc[c], boundary_rank(c), n - fc_cache[c], psi_cache[c])
        m_s = (future_fc[succ], boundary_rank(succ), n - fc_cache[succ], psi_cache[succ])
        if not (m_s < m_c):
            violations5 += 1

print(f"\nMeasure (FutureFc, boundary_rank, n-fc, psi) lex for ALL bad steps:")
print(f"  Violations: {violations5}")
