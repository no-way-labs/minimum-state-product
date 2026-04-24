#!/usr/bin/env python3
"""Check if the const-future subgraph is a DAG and compute its rank."""

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
    if cup2FrontierTypeVal(a, b) == 1: return cup2W1(n, j)
    else: return cup2W2(n, j)
def cup2Psi(c, n):
    total = 0
    for j in range(n):
        total += cup2PsiWeightVal(n, j, c[j], c[(j+1)%n])
    return total

for n in [5,6,7,8,9]:
    ms=[2]+[3]*(n-2)+[2]
    def get_table(i, n=n):
        if i==0: return TBotVal
        elif i==1: return TLowVal
        elif i+1==n: return TTopVal
        elif i+2==n: return THighVal
        else: return TMidVal
    def fc(c, n=n): return sum(1 for j in range(n) if c[j]!=c[(j+1)%n])
    def step(c,i,n=n):
        L=c[(i-1)%n]; S=c[i]; R=c[(i+1)%n]; out=get_table(i,n)(L,S,R)
        if out!=S: nc=list(c); nc[i]=out; return tuple(nc)
        return None

    all_configs = list(cartesian(*(range(m) for m in ms)))
    all_succ = defaultdict(list)
    for c in all_configs:
        for i in range(n):
            s = step(c,i,n)
            if s: all_succ[c].append(s)

    # SCC for bad set
    adj = defaultdict(list)
    for c in all_configs:
        for s in all_succ[c]: adj[c].append(s)
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

    fc_cache = {c:fc(c,n) for c in bad_set}
    psi_cache = {c:cup2Psi(c,n) for c in bad_set}

    # Compute FutureFc
    future_fc = {}
    for c in bad_set:
        visited={c}; queue=[c]; mf=fc_cache[c]; qi=0
        while qi<len(queue):
            v=queue[qi]; qi+=1
            for w in bad_adj.get(v,[]):
                if w not in visited:
                    visited.add(w); queue.append(w)
                    if fc_cache[w]>mf: mf=fc_cache[w]
        future_fc[c] = mf

    # Build const-future subgraph
    cf_adj = defaultdict(list)
    cf_nodes = set()
    for c in bad_set:
        F = future_fc[c]
        for s in bad_adj.get(c,[]):
            if future_fc[s] == F:
                cf_adj[c].append(s)
                cf_nodes.add(c)
                cf_nodes.add(s)

    # Check if const-future is a DAG (no cycles)
    # Tarjan SCC on const-future subgraph
    idx_c2=[0];stack2=[];ll2={};im2={};ons2=set();sccs2=[]
    for s in cf_nodes:
        if s in im2: continue
        cs_t=[(s,iter(cf_adj.get(s,[])))]; im2[s]=ll2[s]=idx_c2[0]; idx_c2[0]+=1
        stack2.append(s); ons2.add(s)
        while cs_t:
            v,ch=cs_t[-1]
            try:
                w=next(ch)
                if w not in im2:
                    im2[w]=ll2[w]=idx_c2[0]; idx_c2[0]+=1; stack2.append(w); ons2.add(w)
                    cs_t.append((w,iter(cf_adj.get(w,[]))))
                elif w in ons2: ll2[v]=min(ll2[v],im2[w])
            except StopIteration:
                cs_t.pop()
                if cs_t: ll2[cs_t[-1][0]]=min(ll2[cs_t[-1][0]],ll2[v])
                if ll2[v]==im2[v]:
                    scc=[]
                    while True:
                        w=stack2.pop(); ons2.discard(w); scc.append(w)
                        if w==v: break
                    sccs2.append(scc)

    nontrivial_sccs = [scc for scc in sccs2 if len(scc) > 1]
    self_loops = sum(1 for scc in sccs2 if len(scc) == 1 and scc[0] in cf_adj.get(scc[0],[]))

    # Compute DAG rank (longest path)
    if not nontrivial_sccs and self_loops == 0:
        # It IS a DAG! Compute ranks
        # Topological sort first
        in_degree = defaultdict(int)
        for c in cf_nodes:
            for s in cf_adj.get(c,[]):
                in_degree[s] += 1
        queue = [c for c in cf_nodes if in_degree[c] == 0]
        rank = {}
        qi = 0
        while qi < len(queue):
            c = queue[qi]; qi += 1
            if c not in rank: rank[c] = 0
            for s in cf_adj.get(c,[]):
                rank[s] = max(rank.get(s, 0), rank[c] + 1)
                in_degree[s] -= 1
                if in_degree[s] == 0:
                    queue.append(s)
        max_rank = max(rank.values()) if rank else 0
        print(f'n={n}: const-future IS DAG, {len(cf_nodes)} nodes, max_rank={max_rank}')
    else:
        print(f'n={n}: const-future has {len(nontrivial_sccs)} nontrivial SCCs, {self_loops} self-loops')
        for scc in nontrivial_sccs[:3]:
            print(f'  SCC size: {len(scc)}')

    # Also check the FULL bad step graph
    # For reference: check if badStep is DAG
    bad_nontrivial = [scc for scc in sccs if len(scc) > 1 and set(scc) & bad_set]
    print(f'  bad set size: {len(bad_set)}, bad SCCs with >1 element: {len(bad_nontrivial)}')
    print()
