#!/usr/bin/env python3
"""
Check reverse decomposition: copy=neg (fc-decreasing), anom=nonneg (fc-nondecreasing).
Segment: x ->neg^* z ->nonneg y
Need: some measure m(y) < m(x) for WF.

For neg chain x -> ... -> z: fc strictly drops at each step, so fc(z) < fc(x).
For nonneg step z -> y: fc(y) >= fc(z).
So fc(y) >= fc(z) but fc(z) < fc(x), meaning fc(y) < fc(x) doesn't follow.

But what about nonneg_measure(y) vs nonneg_measure(x)?
For nonneg step: nonneg_measure(y) < nonneg_measure(z) [strictly by WF proof].
For neg chain: nonneg_measure could change in any direction.

Let me check: does nonneg_measure(y) < nonneg_measure(x)?
"""

from itertools import product as cartesian
from collections import defaultdict

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

def make_system(n):
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
    bad_edges = [(c,s) for c in bad_configs for s in all_succ.get(c,[]) if s in bad_set]
    return bad_configs, bad_set, bad_edges, fc, psi, n

for test_n in [5, 6, 7]:
    bad_configs, bad_set, bad_edges, fc_fn, psi_fn, n = make_system(test_n)
    print(f"\n=== n={test_n}: {len(bad_configs)} bad, {len(bad_edges)} edges ===")

    nonneg_edges = [(c,s) for c,s in bad_edges if fc_fn(s) >= fc_fn(c)]
    neg_edges = [(c,s) for c,s in bad_edges if fc_fn(s) < fc_fn(c)]

    # copy=neg, anom=nonneg
    neg_adj = defaultdict(list)
    for c, s in neg_edges:
        neg_adj[c].append(s)

    nonneg_adj = defaultdict(list)
    for c, s in nonneg_edges:
        nonneg_adj[c].append(s)

    PSIMAX = n * n
    def nonneg_measure(c):
        return (n - fc_fn(c)) * (PSIMAX + 1) + psi_fn(c)

    # Segment: x ->neg^* z ->nonneg y
    # Check: nonneg_measure(y) < nonneg_measure(x)?
    segment_violations = 0
    total_segments = 0

    for x in bad_configs:
        # Find all z reachable via neg from x
        visited = {x}
        queue = [x]
        qi = 0
        while qi < len(queue):
            v = queue[qi]; qi += 1
            for w in neg_adj.get(v, []):
                if w not in visited:
                    visited.add(w)
                    queue.append(w)

        for z in visited:
            for y in nonneg_adj.get(z, []):
                total_segments += 1
                if nonneg_measure(y) >= nonneg_measure(x):
                    segment_violations += 1

    print(f"  Segments: {total_segments}, nonneg_measure violations: {segment_violations}")

    # Also check: fc(y) < fc(x)?
    segment_violations_fc = 0
    for x in bad_configs:
        visited = {x}
        queue = [x]
        qi = 0
        while qi < len(queue):
            v = queue[qi]; qi += 1
            for w in neg_adj.get(v, []):
                if w not in visited:
                    visited.add(w)
                    queue.append(w)
        for z in visited:
            for y in nonneg_adj.get(z, []):
                if fc_fn(y) >= fc_fn(x):
                    segment_violations_fc += 1

    print(f"  fc violations: {segment_violations_fc}")
