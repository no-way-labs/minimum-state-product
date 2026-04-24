#!/usr/bin/env python3
"""Quick debug for the good cycle extraction."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian

T_bot = {(0,0,0): 1,(0,0,1): 1,(0,0,2): 0,(0,1,0): 1,(0,1,1): 1,(0,1,2): 1,
         (1,0,0): 0,(1,0,1): 1,(1,0,2): 0,(1,1,0): 0,(1,1,1): 1,(1,1,2): 0}
T_low = {(0,0,0): 0,(0,0,1): 0,(0,0,2): 0,(0,1,0): 0,(0,1,1): 1,(0,1,2): 0,
         (0,2,0): 0,(0,2,1): 2,(0,2,2): 0,(1,0,0): 1,(1,0,1): 1,(1,0,2): 1,
         (1,1,0): 1,(1,1,1): 1,(1,1,2): 2,(1,2,0): 0,(1,2,1): 1,(1,2,2): 2}
T_mid = {(0,0,0): 0,(0,0,1): 0,(0,0,2): 0,(0,1,0): 0,(0,1,1): 1,(0,1,2): 0,
         (0,2,0): 0,(0,2,1): 2,(0,2,2): 0,(1,0,0): 1,(1,0,1): 1,(1,0,2): 1,
         (1,1,0): 1,(1,1,1): 1,(1,1,2): 2,(1,2,0): 0,(1,2,1): 1,(1,2,2): 2,
         (2,0,0): 0,(2,0,1): 0,(2,0,2): 2,(2,1,0): 1,(2,1,1): 0,(2,1,2): 2,
         (2,2,0): 0,(2,2,1): 2,(2,2,2): 2}
T_high = {(0,0,0): 0,(0,0,1): 0,(0,1,0): 0,(0,1,1): 0,(0,2,0): 0,(0,2,1): 0,
          (1,0,0): 1,(1,0,1): 1,(1,1,0): 1,(1,1,1): 2,(1,2,0): 0,(1,2,1): 2,
          (2,0,0): 0,(2,0,1): 2,(2,1,0): 0,(2,1,1): 2,(2,2,0): 2,(2,2,1): 2}
T_top = {(0,0,0): 0,(0,0,1): 0,(0,1,0): 0,(0,1,1): 0,(1,0,0): 0,(1,0,1): 1,
         (1,1,0): 1,(1,1,1): 1,(2,0,0): 1,(2,0,1): 1,(2,1,0): 1,(2,1,1): 1}

n = 5
ms = [2,3,3,3,2]
def make_f(t):
    return lambda L,S,R, t=t: t[(L,S,R)]
fs = [make_f(T_bot), make_f(T_low), make_f(T_mid), make_f(T_high), make_f(T_top)]

all_cfgs = list(cartesian(*(range(m) for m in ms)))
print(f'{len(all_cfgs)} configs', flush=True)

single = {}
multi = 0
zero = 0
for c in all_cfgs:
    pr = []
    for i in range(n):
        L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
        if fs[i](L,S,R) != S:
            pr.append(i)
    if len(pr) == 0: zero += 1
    elif len(pr) == 1: single[c] = pr[0]
    else: multi += 1
print(f'single={len(single)}, multi={multi}, zero={zero}', flush=True)

succ = {}
for c, p in single.items():
    lst = list(c)
    L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
    lst[p] = fs[p](L,S,R)
    succ[c] = (tuple(lst), p)

good = set(single.keys())
it = 0
while True:
    it += 1
    rm = {c for c in good if succ[c][0] not in good}
    if not rm: break
    good -= rm
    print(f'  iter {it}: removed {len(rm)}, remain {len(good)}', flush=True)
print(f'Good: {len(good)}', flush=True)

start = next(iter(good))
cyc = [start]
cur = succ[start][0]
for _ in range(len(good)+5):
    if cur == start: break
    cyc.append(cur)
    cur = succ[cur][0]
print(f'Cycle: {len(cyc)}', flush=True)

# Quick claim checks
non_good = [c for c in all_cfgs if c not in good]
print(f'Non-good: {len(non_good)}', flush=True)

# Claim 1: dead non-good?
dead = 0
for c in non_good:
    pr = []
    for i in range(n):
        L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
        if fs[i](L,S,R) != S: pr.append(i)
    if not pr: dead += 1
print(f'Claim 1: dead non-good = {dead}', flush=True)

# Claim 2: move non-good -> good?
viol = 0
for c in non_good:
    pr = []
    for i in range(n):
        L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
        if fs[i](L,S,R) != S: pr.append(i)
    for p in pr:
        lst = list(c)
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        lst[p] = fs[p](L,S,R)
        r = tuple(lst)
        if r in good:
            viol += 1
            if viol <= 3:
                print(f'  VIOL: c={c} fire {p} -> {r}', flush=True)
print(f'Claim 2: violations = {viol}', flush=True)

print('DONE n=5', flush=True)
