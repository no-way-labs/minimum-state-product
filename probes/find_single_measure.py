#!/usr/bin/env python3
"""
Find the DAG rank of the bad step graph at n=9.
This is a valid WF measure but we need to characterize it.
Also check if it relates to any simple formula.
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

# Compute DAG rank
print(f"n={n}: {len(bad_configs)} bad configs")
rank = {}
def compute_rank(c):
    if c in rank: return rank[c]
    rank[c] = -1  # sentinel
    best = 0
    for s in bad_adj.get(c, []):
        r = compute_rank(s)
        if r + 1 > best:
            best = r + 1
    rank[c] = best
    return best

import sys
sys.setrecursionlimit(20000)
for c in bad_configs:
    compute_rank(c)

max_rank = max(rank[c] for c in bad_configs)
print(f"Max DAG rank: {max_rank}")

# Check correlation with (n-fc, psi)
PSIMAX = n * n
nonneg_measure = lambda c: (n - fc(c)) * (PSIMAX + 1) + psi(c)

# Does rank correlate with nonneg_measure?
rank_vals = sorted(set(rank[c] for c in bad_configs))
print(f"\nRank values range: 0..{max_rank} ({len(rank_vals)} distinct)")

# For each bad step, check if rank strictly decreases
violations = 0
for c in bad_configs:
    for s in bad_adj.get(c, []):
        if rank[s] >= rank[c]:
            violations += 1
print(f"Rank violations (should be 0): {violations}")

# Check if rank = some function of (fc, psi, boundary)
# Group by (fc, psi) and see spread
from collections import Counter
fp_spread = defaultdict(list)
for c in bad_configs:
    fp_spread[(fc(c), psi(c))].append(rank[c])

print(f"\n(fc, psi) groups: {len(fp_spread)}")
max_spread = 0
for k, v in fp_spread.items():
    spread = max(v) - min(v)
    if spread > max_spread:
        max_spread = spread
        worst_k = k
print(f"Max spread within (fc, psi): {max_spread} at {worst_k}")
print(f"  ranks: {sorted(fp_spread[worst_k])[:20]}")

# Now the KEY question: can cup2BadConstFutureStep_wf be proved
# as a subrelation of cup2BadStepNonneg?
# i.e., at constant FutureFc, is fc always non-decreasing?
# We already know: NO (3221 neg steps).

# Alternative: is there a SIMPLE ANALYTICAL measure that works?
# Check: does (fc, psi) lex (with fc DESCENDING, psi ASCENDING) work?
# i.e., (fc_c > fc_s) or (fc_c == fc_s and psi_c < psi_s)?
lex_violations = 0
for c in bad_configs:
    for s in bad_adj.get(c, []):
        fc_c, fc_s = fc(c), fc(s)
        psi_c, psi_s = psi(c), psi(s)
        # We want: (fc_s, psi_s) < (fc_c, psi_c) in the "right" ordering
        # Try: (n-fc DESC, psi ASC) = standard nonneg measure
        if not (n - fc_s < n - fc_c or (n - fc_s == n - fc_c and psi_s < psi_c)):
            lex_violations += 1

print(f"\n(n-fc, psi) lex violations: {lex_violations}")

# Try adding more components
# (fc, psi, sum_of_values)
def sum_vals(c):
    return sum(c)

lex3_violations = 0
for c in bad_configs:
    for s in bad_adj.get(c, []):
        t1 = (n - fc(c), psi(c), sum_vals(c))
        t2 = (n - fc(s), psi(s), sum_vals(s))
        if not (t2 < t1):
            lex3_violations += 1
print(f"(n-fc, psi, sum) lex violations: {lex3_violations}")

# How about a weighted sum?
# Try mu = A*fc + B*psi for various A, B
best = None
for A in range(-5, 6):
    for B in range(-5, 6):
        if A == 0 and B == 0: continue
        fails = 0
        for c in bad_configs:
            for s in bad_adj.get(c, []):
                mu_c = A * fc(c) + B * psi(c)
                mu_s = A * fc(s) + B * psi(s)
                if mu_s >= mu_c:
                    fails += 1
        if best is None or fails < best[0]:
            best = (fails, A, B)
            if fails == 0:
                print(f"FOUND: mu = {A}*fc + {B}*psi, 0 violations!")
                break
    if best and best[0] == 0:
        break

if best and best[0] > 0:
    print(f"\nBest linear: mu = {best[1]}*fc + {best[2]}*psi, {best[0]} violations")
