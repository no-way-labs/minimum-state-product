#!/usr/bin/env python3
"""Debug axiom violations: which positions fire? What are the boundary transitions?"""

import sys
from itertools import product as cartesian
from collections import defaultdict, Counter

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
    L = c[(i-1) % n]
    S = c[i]
    R = c[(i+1) % n]
    table = get_table(i)
    out = table(L, S, R)
    if out != S:
        new_c = list(c)
        new_c[i] = out
        return tuple(new_c)
    return None

# Which position fires to produce c -> succ?
def find_position(c, succ):
    for i in range(n):
        if c[i] != succ[i]:
            return i
    return -1

# Quick: just look at the first violation from the main script
# The first violation: c=(0,0,0,0,0,1,2,1,1), c'=(0,0,0,0,0,1,1,1,1)
# Position that changed: c[6]=2 -> c'[6]=1, so position 6
# n-3 = 6. So this is at the boundary position n-3!
# This IS a boundary position. The 6-tuple includes c[n-3].

# Wait, the question is: what does the axiom ACTUALLY need?
# The axiom says: at constant FutureFc, boundary-changing bad steps produce extended edges.
# The 617+12 edge set is supposed to cover ALL such transitions.
# But there are 1668 violations — so the edge set is INCOMPLETE for these transitions.

# Let me check: are the violations at boundary positions (0,1,2,n-3,n-2,n-1)?
# Or at interior positions that somehow change the 6-tuple (impossible since interior
# positions 3..n-4 don't affect c[0..2] or c[n-3..n-1])?

# For n=9: boundary positions are 0,1,2,6,7,8. Interior = 3,4,5.
# Position 6 = n-3 IS boundary.

# So the issue is: the 617+12 edge set doesn't cover all boundary position moves
# at constant FutureFc. The axiom is WRONG as stated!

# But wait — the Lean code already has proofs that B1-B4 moves produce extended edges.
# Those are the fc-INCREASING moves. The violations are at fc-NON-INCREASING moves
# at boundary positions. Let me check.

print("Analyzing violations by position and fc change...")
all_configs = list(cartesian(*(range(m) for m in ms)))
all_succ = defaultdict(list)
for c in all_configs:
    for i in range(n):
        succ = step(c, i)
        if succ is not None:
            all_succ[c].append((succ, i))

# Find good cycle
def tarjan_iterative(nodes, adj_list):
    index_counter = [0]
    stack = []
    lowlink = {}
    index_map = {}
    on_stack = set()
    sccs = []
    for start in nodes:
        if start in index_map:
            continue
        call_stack = [(start, iter([s for s,_ in adj_list.get(start, [])]), False)]
        index_map[start] = index_counter[0]
        lowlink[start] = index_counter[0]
        index_counter[0] += 1
        stack.append(start)
        on_stack.add(start)
        while call_stack:
            v, children, _ = call_stack[-1]
            try:
                w = next(children)
                if w not in index_map:
                    index_map[w] = index_counter[0]
                    lowlink[w] = index_counter[0]
                    index_counter[0] += 1
                    stack.append(w)
                    on_stack.add(w)
                    call_stack.append((w, iter([s for s,_ in adj_list.get(w, [])]), False))
                elif w in on_stack:
                    lowlink[v] = min(lowlink[v], index_map[w])
            except StopIteration:
                call_stack.pop()
                if call_stack:
                    lowlink[call_stack[-1][0]] = min(lowlink[call_stack[-1][0]], lowlink[v])
                if lowlink[v] == index_map[v]:
                    scc = []
                    while True:
                        w = stack.pop()
                        on_stack.discard(w)
                        scc.append(w)
                        if w == v:
                            break
                    sccs.append(scc)
    return sccs

sccs = tarjan_iterative(all_configs, all_succ)
terminal = []
for i, scc in enumerate(sccs):
    scc_set = set(scc)
    if not any(s not in scc_set for v in scc for s,_ in all_succ.get(v,[])):
        terminal.append(i)

good_set = set(sccs[terminal[0]])
bad_configs = [c for c in all_configs if c not in good_set]
bad_set = set(bad_configs)

# Bad adjacency
bad_adj_with_pos = defaultdict(list)
for c in bad_configs:
    for succ, i in all_succ.get(c, []):
        if succ in bad_set:
            bad_adj_with_pos[c].append((succ, i))

# Compute FutureFc
import time
t0 = time.time()
fc_cache = {c: fc(c) for c in bad_configs}
future_fc = {}
bad_adj_simple = defaultdict(list)
for c in bad_configs:
    for succ, _ in bad_adj_with_pos.get(c, []):
        bad_adj_simple[c].append(succ)

for c in bad_configs:
    visited = {c}
    queue = [c]
    max_fc = fc_cache[c]
    qi = 0
    while qi < len(queue):
        v = queue[qi]; qi += 1
        for w in bad_adj_simple.get(v, []):
            if w not in visited:
                visited.add(w)
                queue.append(w)
                if fc_cache[w] > max_fc:
                    max_fc = fc_cache[w]
    future_fc[c] = max_fc

print(f"FutureFc computed in {time.time()-t0:.1f}s")

# Find violations with position info
pos_counts = Counter()
fc_change_counts = Counter()
violations = []
for c in bad_configs:
    for succ, pos in bad_adj_with_pos.get(c, []):
        b6c = enc6(c)
        b6s = enc6(succ)
        if b6c != b6s and future_fc[c] == future_fc[succ]:
            fc_c = fc_cache[c]
            fc_s = fc_cache[succ]
            pos_counts[pos] += 1
            fc_change_counts[fc_s - fc_c] += 1
            violations.append((c, succ, pos, fc_c, fc_s, future_fc[c]))

print(f"\nTotal violations: {len(violations)}")
print(f"\nBy position: {dict(sorted(pos_counts.items()))}")
print(f"By fc change (fc'-fc): {dict(sorted(fc_change_counts.items()))}")

# Show what boundary transitions are missing
missing_edges = set()
for c, succ, pos, fc_c, fc_s, ff in violations:
    b6c = enc6(c)
    b6s = enc6(succ)
    src = enc6_to_int(b6c)
    dst = enc6_to_int(b6s)
    missing_edges.add((src, dst))

print(f"\nDistinct missing boundary edges: {len(missing_edges)}")
for s,d in sorted(missing_edges)[:20]:
    print(f"  ({s},{d})")
