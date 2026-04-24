#!/usr/bin/env python3
"""
Check: at constant FutureFc, do boundary-changing steps form a DAG on 324 states?
This is what we actually need for the proof.
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

import sys, time

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

# Bad adjacency
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

# Collect ALL boundary edges that occur at constant FutureFc
constfuture_boundary_edges = set()
for c in bad_configs:
    for succ in bad_adj.get(c, []):
        if future_fc[c] == future_fc[succ]:
            b6c = enc6_to_int(enc6(c))
            b6s = enc6_to_int(enc6(succ))
            if b6c != b6s:
                constfuture_boundary_edges.add((b6c, b6s))

print(f"Distinct boundary edges at constant FutureFc: {len(constfuture_boundary_edges)}")

# Check if this forms a DAG on 324 states
adj324 = defaultdict(list)
for s, d in constfuture_boundary_edges:
    adj324[s].append(d)

WHITE, GRAY, BLACK = 0, 1, 2
color = {i: WHITE for i in range(324)}
has_cycle = False
for start in range(324):
    if color[start] != WHITE: continue
    stk = [(start, iter(adj324.get(start, [])))]
    color[start] = GRAY
    while stk:
        v, ch = stk[-1]
        try:
            w = next(ch)
            if color[w] == GRAY:
                has_cycle = True; break
            elif color[w] == WHITE:
                color[w] = GRAY; stk.append((w, iter(adj324.get(w, []))))
        except StopIteration:
            stk.pop(); color[v] = BLACK
    if has_cycle: break

print(f"Constant-FutureFc boundary graph is DAG: {not has_cycle}")

if not has_cycle:
    # Compute rank
    memo = {}
    def rank(v):
        if v in memo: return memo[v]
        memo[v] = -1
        best = 0
        for w in adj324.get(v, []):
            best = max(best, 1 + rank(w))
        memo[v] = best
        return best
    for v in range(324):
        rank(v)
    max_rank = max(memo[v] for v in range(324))
    print(f"Max rank: {max_rank}")

    # How many edges are NOT in the 617+12 set?
    edge_617 = set([
        (0,6),(0,162),(1,0),(1,7),(2,164),(3,1),(3,9),(4,166),
        (6,8),(6,168),(7,6),(7,9),(8,170),(9,11),(10,16),(10,172),
        (11,17),(12,174),(13,12),(14,176),(16,4),(16,178),(17,5),
        (18,24),(18,180),(19,18),(19,25),(20,182),(21,19),(21,27),
        (22,184),(24,26),(24,186),(25,24),(25,27),(26,188),(27,29),
        (28,34),(28,190),(29,35),(30,192),(31,30),(32,194),(34,22),
        (34,196),(35,23),(36,0),(36,42),(36,198),(37,1),(37,36),
        (37,43),(38,2),(38,200),(39,3),(39,37),(39,45),(40,4),
        (40,202),(41,5),(42,6),(42,44),(42,204),(43,7),(43,42),
        (43,45),(44,8),(44,206),(45,9),(45,47),(46,10),(46,52),
        (46,208),(47,11),(47,53),(48,12),(48,210),(49,13),(49,48),
        (50,14),(50,212),(51,15),(52,16),(52,40),(52,214),(53,17),
        (53,41),
    ])
    b4 = set([(4,5),(10,11),(16,17),(22,23),(28,29),(34,35),
              (40,41),(46,47),(52,53),(148,149),(154,155),(160,161)])
    # extended = edge_617 | b4  # partial, let me count properly
    new_edges = constfuture_boundary_edges - set([
        # I'll just count
    ])
    print(f"Total new edges (not checking overlap with 617+12): {len(constfuture_boundary_edges)}")

    # Print the rank values for all 324 states
    print("\nRank values for use in Lean:")
    rank_list = [memo[v] for v in range(324)]
    print(f"  Max rank: {max(rank_list)}")
    print(f"  Ranks: {rank_list}")
else:
    print("HAS CYCLE - cannot use as DAG")
    # Find the cycle
    color2 = {i: WHITE for i in range(324)}
    for start in range(324):
        if color2[start] != WHITE: continue
        parent = {}
        stk = [(start, iter(adj324.get(start, [])))]
        color2[start] = GRAY
        while stk:
            v, ch = stk[-1]
            try:
                w = next(ch)
                if color2[w] == GRAY:
                    # Found cycle
                    path = [w, v]
                    cur = v
                    while cur != w:
                        found = False
                        for sv, _ in stk:
                            if sv == cur:
                                found = True
                                break
                        if not found: break
                        # find parent
                        for sv, _ in reversed(stk):
                            if sv != cur:
                                cur = sv
                                path.append(cur)
                                break
                            break
                    print(f"  Cycle involving nodes: {w}")
                    # Just print the edge
                    print(f"  Edge creating cycle: {v} -> {w}")
                    break
                elif color2[w] == WHITE:
                    color2[w] = GRAY
                    parent[w] = v
                    stk.append((w, iter(adj324.get(w, []))))
            except StopIteration:
                stk.pop()
                color2[v] = BLACK
        if has_cycle: break
