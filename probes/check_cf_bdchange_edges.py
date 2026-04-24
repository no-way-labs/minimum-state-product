#!/usr/bin/env python3
"""Check: what boundary transitions actually occur on const-future boundary-changing steps?
And do they form a DAG on the 324 6-tuple states?"""

from itertools import product as cartesian
from collections import defaultdict

def TBotVal(L,S,R):
    t = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    return t.get((L,S,R), 0)
def TLowVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    return t.get((L,S,R), 0)
def THighVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    return t.get((L,S,R), 0)
def TTopVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    return t.get((L,S,R), 0)
TMidVal_dict = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
def TMidVal(L,S,R): return TMidVal_dict.get((L,S,R), 0)

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

def boundary6(c):
    return (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])

all_configs = list(cartesian(*(range(m) for m in ms)))
all_succ = defaultdict(list)
for c in all_configs:
    for i in range(n):
        s = step(c,i)
        if s: all_succ[c].append((s,i))

# SCC
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

# Collect all boundary transitions on CF boundary-changing steps
bd_edges = set()
bd_edges_nonneg = set()
bd_edges_neg = set()
for c in bad_set:
    F = future_fc[c]
    for s,i in bad_adj.get(c,[]):
        if future_fc[s] != F: continue
        b_c = boundary6(c)
        b_s = boundary6(s)
        if b_c != b_s:
            bd_edges.add((b_s, b_c))
            if fc_cache[s] < fc_cache[c]:
                bd_edges_neg.add((b_s, b_c))
            else:
                bd_edges_nonneg.add((b_s, b_c))

print(f'Total CF boundary-changing edges (on 6-tuples): {len(bd_edges)}')
print(f'  nonneg CF bdchange: {len(bd_edges_nonneg)}')
print(f'  neg CF bdchange: {len(bd_edges_neg)}')

# Check if these edges form a DAG on boundary states
all_bd_states = set()
bd_adj = defaultdict(set)
for (s, c) in bd_edges:
    bd_adj[c].add(s)
    all_bd_states.add(s)
    all_bd_states.add(c)

# SCC on boundary graph
idx_c3=[0];stack3=[];ll3={};im3={};ons3=set();sccs3=[]
for s in all_bd_states:
    if s in im3: continue
    cs_t=[(s,iter(bd_adj.get(s,set())))]; im3[s]=ll3[s]=idx_c3[0]; idx_c3[0]+=1
    stack3.append(s); ons3.add(s)
    while cs_t:
        v,ch=cs_t[-1]
        try:
            w=next(ch)
            if w not in im3:
                im3[w]=ll3[w]=idx_c3[0]; idx_c3[0]+=1; stack3.append(w); ons3.add(w)
                cs_t.append((w,iter(bd_adj.get(w,set()))))
            elif w in ons3: ll3[v]=min(ll3[v],im3[w])
        except StopIteration:
            cs_t.pop()
            if cs_t: ll3[cs_t[-1][0]]=min(ll3[cs_t[-1][0]],ll3[v])
            if ll3[v]==im3[v]:
                scc=[]
                while True:
                    w=stack3.pop(); ons3.discard(w); scc.append(w)
                    if w==v: break
                sccs3.append(scc)

nontrivial3 = [scc for scc in sccs3 if len(scc) > 1]
self_loops3 = sum(1 for scc in sccs3 if len(scc) == 1 and list(scc)[0] in bd_adj.get(list(scc)[0], set()))

print(f'Boundary graph: {len(all_bd_states)} states, {len(nontrivial3)} nontrivial SCCs, {self_loops3} self-loops')
if nontrivial3:
    for scc in nontrivial3[:5]:
        print(f'  SCC size={len(scc)}: {scc[:3]}...')

# Check: does the EXTENDED boundary edge set (617+12) cover all nonneg CF bdchange?
# The false axiom claimed ALL CF bdchange edges are extended edges.
# Check how many of the actual edges are NOT in the extended set.

# Load extended edges from SixTuple.lean
# ... too complex. Instead just check if the boundary graph is a DAG with the NONNEG edges only
bd_adj_nn = defaultdict(set)
for (s, c) in bd_edges_nonneg:
    bd_adj_nn[c].add(s)

# Check nonneg-only boundary graph
all_nn_states = set()
for (s,c) in bd_edges_nonneg:
    all_nn_states.add(s); all_nn_states.add(c)

idx_c4=[0];stack4=[];ll4={};im4={};ons4=set();sccs4=[]
for s in all_nn_states:
    if s in im4: continue
    cs_t=[(s,iter(bd_adj_nn.get(s,set())))]; im4[s]=ll4[s]=idx_c4[0]; idx_c4[0]+=1
    stack4.append(s); ons4.add(s)
    while cs_t:
        v,ch=cs_t[-1]
        try:
            w=next(ch)
            if w not in im4:
                im4[w]=ll4[w]=idx_c4[0]; idx_c4[0]+=1; stack4.append(w); ons4.add(w)
                cs_t.append((w,iter(bd_adj_nn.get(w,set()))))
            elif w in ons4: ll4[v]=min(ll4[v],im4[w])
        except StopIteration:
            cs_t.pop()
            if cs_t: ll4[cs_t[-1][0]]=min(ll4[cs_t[-1][0]],ll4[v])
            if ll4[v]==im4[v]:
                scc=[]
                while True:
                    w=stack4.pop(); ons4.discard(w); scc.append(w)
                    if w==v: break
                sccs4.append(scc)

nontrivial4 = [scc for scc in sccs4 if len(scc) > 1]
print(f'\nNonneg-only boundary graph: {len(all_nn_states)} states, {len(nontrivial4)} nontrivial SCCs')
if not nontrivial4:
    # DAG rank
    in_deg = defaultdict(int)
    for c in all_nn_states:
        for s in bd_adj_nn.get(c, set()):
            in_deg[s] += 1
    q = [c for c in all_nn_states if in_deg[c] == 0]
    rnk = {}; qi = 0
    while qi < len(q):
        c = q[qi]; qi += 1
        if c not in rnk: rnk[c] = 0
        for s in bd_adj_nn.get(c, set()):
            rnk[s] = max(rnk.get(s,0), rnk[c]+1)
            in_deg[s] -= 1
            if in_deg[s] == 0: q.append(s)
    print(f'  Nonneg-only boundary DAG max_rank={max(rnk.values()) if rnk else 0}')
