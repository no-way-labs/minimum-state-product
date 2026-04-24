#!/usr/bin/env python3
"""Check: on pos (fc-increasing) bad steps, what's the max weighted psi increase?
And on neg steps, what's the max weighted psi increase per unit fc decrease?
Can we find A such that A*fc + psi strictly decreases on ALL bad steps?"""

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

for n in [5,6,7,8,9,10,11]:
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

    # For all steps (not just bad), check psi changes by step type
    max_pos_psi_inc = 0  # max psi increase on pos (fc-increasing) steps
    max_neg_psi_inc_ratio = 0  # max psi_increase / fc_decrease on neg steps
    max_psi = 0

    # Also check: for what A does A*fc + psi decrease on ALL steps?
    # Need: A*dfc + dpsi < 0 for ALL nontrivial steps
    # For pos: dfc >= 1, need dpsi < -A
    # For neg: dfc <= -1, need dpsi < A*|dfc| => always true if dpsi < A
    # For fc=0: dfc = 0, need dpsi < 0 (already verified)

    worst_pos_dpsi = -float('inf')  # max dpsi on pos steps
    worst_neg_dpsi_over_negdfc = -float('inf')  # max dpsi/(-dfc) on neg steps

    for c in all_configs:
        wpsi_c = cup2Psi(c, n)
        fc_c = fc(c, n)
        if wpsi_c > max_psi:
            max_psi = wpsi_c
        for i in range(n):
            s = step(c, i, n)
            if s:
                fc_s = fc(s, n)
                wpsi_s = cup2Psi(s, n)
                dfc = fc_s - fc_c
                dpsi = wpsi_s - wpsi_c

                if dfc > 0:  # pos
                    if dpsi > worst_pos_dpsi:
                        worst_pos_dpsi = dpsi
                elif dfc < 0:  # neg
                    ratio = dpsi / (-dfc)
                    if ratio > worst_neg_dpsi_over_negdfc:
                        worst_neg_dpsi_over_negdfc = ratio

    # For A*fc + psi to decrease on ALL steps:
    # pos: A*dfc + dpsi < 0 => for worst case, A + worst_pos_dpsi < 0 => A < -worst_pos_dpsi
    # neg: A*dfc + dpsi < 0 => -A*|dfc| + dpsi < 0 => dpsi < A*|dfc|
    #   worst case: dpsi = worst_neg_dpsi_over_negdfc * (-dfc)
    #   need: worst_neg_dpsi_over_negdfc * (-dfc) < A * (-dfc) => A > worst_neg_dpsi_over_negdfc
    # So need: worst_neg_dpsi_over_negdfc < A < -worst_pos_dpsi

    feasible = worst_neg_dpsi_over_negdfc < -worst_pos_dpsi if worst_pos_dpsi != -float('inf') else None

    print(f'n={n}: max_psi={max_psi}, worst_pos_dpsi={worst_pos_dpsi}, worst_neg_dpsi/(-dfc)={worst_neg_dpsi_over_negdfc:.1f}, feasible={feasible}')

    if n >= 11:
        break
