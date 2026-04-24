#!/usr/bin/env python3
"""Find actual cycles in the constant-FutureFc bad step graph (at config level, not boundary level)."""

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

# Find good cycle
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

# Compute FutureFc
t0 = time.time()
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
print(f"FutureFc computed in {time.time()-t0:.1f}s")

# Build constant-FutureFc subgraph
constfuture_adj = defaultdict(list)
for c in bad_configs:
    for succ in bad_adj.get(c, []):
        if future_fc[c] == future_fc[succ]:
            constfuture_adj[c].append(succ)

# Check for cycles in constant-FutureFc config-level graph
print("Checking constant-FutureFc config graph for cycles...")
sccs_cf = tarjan(bad_configs, constfuture_adj)
nontrivial_sccs = [scc for scc in sccs_cf if len(scc) > 1]
self_loops = sum(1 for scc in sccs_cf if len(scc) == 1 and scc[0] in constfuture_adj.get(scc[0], []))

print(f"Total SCCs: {len(sccs_cf)}")
print(f"Non-trivial SCCs (size > 1): {len(nontrivial_sccs)}")
print(f"Self-loops: {self_loops}")

if nontrivial_sccs:
    print("\nNon-trivial SCC sizes:", sorted([len(scc) for scc in nontrivial_sccs]))
else:
    print("\nConstant-FutureFc config graph IS a DAG! (no cycles)")
    print("This means cup2BadConstFutureStep_wf can be proved via DAG rank on configs.")
    print("But 8723 configs is too many for a lookup table in Lean.")
