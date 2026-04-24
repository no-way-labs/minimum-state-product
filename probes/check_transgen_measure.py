#!/usr/bin/env python3
"""Check: for any TransGen CF path from a to b (b leads to a in execution),
is nm(b) < nm(a) always?

If yes, then TransGen CF c c implies nm(c) < nm(c), contradiction.

nm = (n - fc, psi) lex.

Also check: is there ANY TransGen path where nm doesn't strictly decrease?
i.e., is there a -> b in TransGen CF with nm(a) >= nm(b)?
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

for n in [5,6,7,8]:
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

    # Build CF adjacency (execution direction)
    cf_succ = defaultdict(list)  # c -> list of successors (in execution)
    for c in bad_set:
        F = future_fc[c]
        for s in bad_adj.get(c,[]):
            if future_fc[s] == F:
                cf_succ[c].append(s)  # execution: c -> s

    # Compute transitive closure and check nm
    # TransGen r a b means b leads to a. In execution: b -> ... -> a.
    # We want: for all (a,b) with TransGen r a b, is nm(a) < nm(b)?
    # In our execution-direction graph: b -> ... -> a.
    # nm should decrease along execution? Let's check.
    # Actually TransGen r a b means b is "above" a in WF, so nm(a) < nm(b) would be nice.
    # But r a b = cf a b = execution b -> a. TransGen r a b = chain of r steps from a to b.
    # Each r(xi, xi+1) = execution xi+1 -> xi. So execution: b -> ... -> a.
    # For WF: a is below b.

    # Let's just check: for all reachable pairs (a, b) in TransGen CF,
    # does nm(a) < nm(b)? (a = destination in WF sense, b = source)
    # In execution: b leads to a.
    # nm(a) should be < nm(b) for acyclicity to follow.

    # Actually for acyclicity we only need: no (a,a) pair.
    # For the induction approach, we need: for single-step r a b (execution b->a),
    # on nonneg steps: nm(a) < nm(b) YES (proved).
    # on neg steps: nm(a) > nm(b) in first component.
    # So TransGen r a b does NOT imply nm(a) < nm(b).

    # What we can check: for TransGen r paths, is there a DIFFERENT measure that always decreases?
    # The DAG rank! The CF subgraph is a DAG, so there's a DAG rank.

    # Compute DAG rank of CF subgraph
    # CF edges in execution: c -> s means cf s c (r s c)
    # For DAG rank in the WF direction: r a b (a below b).
    # So in the "WF graph" (edges from b to a where r a b = execution b->a),
    # we want the longest path.
    # In execution graph: edges c -> s. DAG rank in execution: longest path.

    # Actually just compute topological order of the CF execution graph
    in_deg = defaultdict(int)
    cf_nodes = set()
    for c in bad_set:
        if cf_succ[c]:
            cf_nodes.add(c)
            for s in cf_succ[c]:
                cf_nodes.add(s)
                in_deg[s] += 1

    queue = [c for c in cf_nodes if in_deg[c] == 0]
    rank = {}
    qi = 0
    while qi < len(queue):
        c = queue[qi]; qi += 1
        if c not in rank: rank[c] = 0
        for s in cf_succ[c]:
            rank[s] = max(rank.get(s, 0), rank[c] + 1)
            in_deg[s] -= 1
            if in_deg[s] == 0:
                queue.append(s)
    max_rank = max(rank.values()) if rank else 0

    # Check: does DAG rank ALWAYS increase along execution?
    # i.e., for every cf edge c -> s, rank(s) > rank(c)?
    rank_violations = 0
    for c in bad_set:
        for s in cf_succ[c]:
            if rank.get(s, 0) <= rank.get(c, 0):
                rank_violations += 1

    print(f'n={n}: cf_nodes={len(cf_nodes)}, max_rank={max_rank}, rank_violations={rank_violations}')

    # Check: can we express the DAG rank as a function of (fc, psi, boundary)?
    # Check: correlation between DAG rank and various measures
    # For each node, print (rank, fc, n-fc, psi, boundary) for a few
    if n == 5:
        for c in sorted(list(cf_nodes)[:20], key=lambda c: rank.get(c, 0)):
            r = rank.get(c, 0)
            f = fc_cache[c]
            p = psi_cache[c]
            print(f'  config={c}, rank={r}, fc={f}, n-fc={n-f}, psi={p}')
