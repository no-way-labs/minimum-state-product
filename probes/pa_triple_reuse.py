"""Key test: does there exist a bad cycle using ONLY gc mover-triples?

For a residual gc:
  (A) Compute the set of mover-triples M = {(p, L, S, R) : gc fires p at step k
      with local context (L,S,R)}
  (B) Build the "determined-only" transition graph: for each non-gc config c
      and each proc p, if (p, c[p-1], c[p], c[p+1]) is in M (and the S'≠S),
      we have an edge c → move_p(c).
  (C) Check: does this graph have a cycle in the non-gc subspace?
"""
import sys
sys.setrecursionlimit(20000)
from itertools import product as iproduct
from collections import Counter

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24

def left(p): return (p - 1) % N
def right(p): return (p + 1) % N

SAMPLE = (0, 8, 7, 6, 5, 4, 3, 2, 1, 0, 8, 7, 8, 7, 6, 5, 4, 5, 4, 3, 2, 1, 2, 1)

def build_configs(word):
    cfg = [0]*N
    configs = [tuple(cfg)]
    for m in word:
        cfg[m] = (cfg[m] + 1) % MS[m]
        configs.append(tuple(cfg))
    return configs[:-1]

gc_configs = build_configs(list(SAMPLE))
gc_set = set(gc_configs)

# Compute mover-triples (p, L, S, R) -> S'
mover_triples = {}  # (p, L, S, R) -> S'
for k, p in enumerate(SAMPLE):
    cfg = gc_configs[k]
    L, S, R = cfg[left(p)], cfg[p], cfg[right(p)]
    S_new = (S + 1) % MS[p]
    key = (p, L, S, R)
    mover_triples[key] = S_new
print(f"Unique gc mover-triples: {len(mover_triples)}")
print(f"(expected: {CL} if all distinct)")

# Also compute non-mover triples: for each proc p, for each gc step k,
# if p != word[k], then (p, L, S, R) at cfg[k] is a non-mover triple.
non_mover_triples = {}  # (p, L, S, R) -> S (stay)
for k, mover in enumerate(SAMPLE):
    cfg = gc_configs[k]
    for p in range(N):
        if p == mover: continue
        L, S, R = cfg[left(p)], cfg[p], cfg[right(p)]
        key = (p, L, S, R)
        if key in non_mover_triples:
            continue
        non_mover_triples[key] = S
print(f"Unique gc non-mover-triples: {len(non_mover_triples)}")

# Check entry conflict: any (p, L, S, R) in both?
conflict = set(mover_triples.keys()) & set(non_mover_triples.keys())
print(f"EC triples: {len(conflict)}")

# Build determined-only transition graph on non-gc configs
# Edge c -> c' if exists proc p such that (p, L, S, R) in mover_triples and applying it doesn't enter gc (but we actually want all non-gc edges).
# But there may be multiple privileged procs at c — we want to find SOME chain.
# For each non-gc config, enumerate possible "move" transitions via gc-determined movers.

all_configs = list(iproduct(*[range(m) for m in MS]))
non_gc = [c for c in all_configs if c not in gc_set]
print(f"non_gc configs: {len(non_gc)}")

# edges[c] = list of (c', p) where p's triple at c is a gc mover triple
edges = {}
for c in non_gc:
    lst = []
    for p in range(N):
        L, S, R = c[left(p)], c[p], c[right(p)]
        key = (p, L, S, R)
        if key in mover_triples:
            Snew = mover_triples[key]
            if Snew != S:
                new_c = list(c)
                new_c[p] = Snew
                new_c = tuple(new_c)
                lst.append((new_c, p))
    edges[c] = lst

# count configs with any move
have_move = sum(1 for c, lst in edges.items() if lst)
print(f"non-gc configs with at least one gc-determined move: {have_move}/{len(non_gc)}")

# Now find a cycle in this multigraph restricted to non-gc (note edges can go into gc too)
def has_non_gc_cycle():
    # Find any cycle in the subgraph induced by non-gc configs
    # using edges that stay in non-gc
    # Use Tarjan's SCC
    index = {}
    lowlink = {}
    on_stack = {}
    stack = []
    idx_counter = [0]
    sccs = []
    def strongconnect(v, visited=None):
        # iterative
        work = [(v, 0)]
        while work:
            v, pi = work[-1]
            if v not in index:
                index[v] = idx_counter[0]
                lowlink[v] = idx_counter[0]
                idx_counter[0] += 1
                stack.append(v)
                on_stack[v] = True
            neighbors = [c2 for (c2, _) in edges.get(v, []) if c2 not in gc_set]
            if pi < len(neighbors):
                work[-1] = (v, pi+1)
                w = neighbors[pi]
                if w not in index:
                    work.append((w, 0))
                elif on_stack.get(w):
                    lowlink[v] = min(lowlink[v], index[w])
            else:
                if lowlink[v] == index[v]:
                    scc = []
                    while True:
                        w = stack.pop()
                        on_stack[w] = False
                        scc.append(w)
                        if w == v: break
                    sccs.append(scc)
                work.pop()
                if work:
                    u = work[-1][0]
                    lowlink[u] = min(lowlink[u], lowlink[v])
    for c in non_gc:
        if c not in index:
            strongconnect(c)
    nontriv = [s for s in sccs if len(s) > 1 or (len(s)==1 and any(e2 == s[0] for (e2,_) in edges.get(s[0], [])))]
    return nontriv

sccs = has_non_gc_cycle()
print(f"Non-trivial SCCs (cycle containing): {len(sccs)}")
if sccs:
    sccs.sort(key=len, reverse=True)
    print(f"Largest SCC size: {len(sccs[0])}")
    # Show a small cycle
    small = min(sccs, key=len)
    print(f"Smallest cycle SCC ({len(small)} configs):")
    for c in small[:5]:
        print(f"  {c}")
