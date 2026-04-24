#!/usr/bin/env python3
"""Check: for nonneg-CF-then-neg-CF segments, does nonneg_measure(y) < nonneg_measure(x)?

Segment: x -> nonneg_CF ... -> nonneg_CF z -> neg_CF y
Check: (n-fc(y), psi(y)) <lex (n-fc(x), psi(x))

Also check: does fc ALWAYS drop? fc(y) < fc(x)?
"""
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

    # Build nonneg_CF and neg_CF adjacency
    # nonneg_CF: cf step with fc(succ) >= fc(pred)
    # neg_CF: cf step with fc(succ) < fc(pred)
    nonneg_cf = defaultdict(list)
    neg_cf = defaultdict(list)
    for c in bad_set:
        F = future_fc[c]
        for s in bad_adj.get(c,[]):
            if future_fc[s] == F:
                if fc_cache[s] >= fc_cache[c]:
                    nonneg_cf[c].append(s)
                else:
                    neg_cf[c].append(s)

    # For each neg CF step z->y, find all x that can reach z via nonneg CF (backward BFS)
    # Then check: (n-fc(y), psi(y)) <lex (n-fc(x), psi(x))
    rev_nonneg = defaultdict(list)
    for c in bad_set:
        for s in nonneg_cf.get(c,[]):
            rev_nonneg[s].append(c)

    violations_lex = 0
    violations_fc = 0
    total_segments = 0
    for z in bad_set:
        for y in neg_cf.get(z,[]):
            # Find all x reachable from z backward via nonneg_cf
            # (x is the START of the nonneg chain, z is the END)
            visited = {z}
            queue = [z]
            qi = 0
            while qi < len(queue):
                v = queue[qi]; qi += 1
                for w in rev_nonneg.get(v,[]):
                    if w not in visited and w in bad_set and future_fc.get(w) == future_fc.get(z):
                        visited.add(w)
                        queue.append(w)
            for x in visited:
                total_segments += 1
                nm_y = (n - fc_cache[y], psi_cache[y])
                nm_x = (n - fc_cache[x], psi_cache[x])
                if nm_y >= nm_x:  # NOT strictly less
                    violations_lex += 1
                if fc_cache[y] >= fc_cache[x]:
                    violations_fc += 1

    print(f'n={n}: segments={total_segments}, lex_violations={violations_lex}, fc_violations={violations_fc}')
