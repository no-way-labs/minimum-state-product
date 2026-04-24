#!/usr/bin/env python3
"""Check: on neg BAD steps, what's the max weighted psi increase per unit fc decrease?"""

from itertools import product as cartesian
from collections import defaultdict, Counter

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
    if cup2FrontierTypeVal(a, b) == 1:
        return cup2W1(n, j)
    else:
        return cup2W2(n, j)

def cup2Psi(c, n):
    total = 0
    for j in range(n):
        jnext = (j + 1) % n
        total += cup2PsiWeightVal(n, j, c[j], c[jnext])
    return total

for n in [5,6,7,8,9,10,11,12]:
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

    max_wpsi_increase_per_fc_drop = 0
    max_wpsi_total = 0
    # For ALL steps (including non-bad)
    for c in all_configs:
        wpsi_c = cup2Psi(c, n)
        if wpsi_c > max_wpsi_total:
            max_wpsi_total = wpsi_c
        for i in range(n):
            s = step(c, i, n)
            if s:
                dfc = fc(s, n) - fc(c, n)
                if dfc < 0:  # neg step
                    dwpsi = cup2Psi(s, n) - wpsi_c
                    if dwpsi > 0:
                        ratio = dwpsi / (-dfc)
                        if ratio > max_wpsi_increase_per_fc_drop:
                            max_wpsi_increase_per_fc_drop = ratio

    # Also check: on nonneg fc-constant, does wpsi always decrease?
    nonneg_fc0_wpsi_violations = 0
    for c in all_configs:
        wpsi_c = cup2Psi(c, n)
        for i in range(n):
            s = step(c, i, n)
            if s:
                dfc = fc(s, n) - fc(c, n)
                if dfc == 0:
                    dwpsi = cup2Psi(s, n) - wpsi_c
                    if dwpsi >= 0:
                        nonneg_fc0_wpsi_violations += 1

    print(f'n={n}: max_wpsi={max_wpsi_total}, max_psi_inc/fc_drop={max_wpsi_increase_per_fc_drop:.1f}, fc0_wpsi_nodec={nonneg_fc0_wpsi_violations}')

    if n >= 10:
        break
