#!/usr/bin/env python3
"""Check psi behavior on fc-positive (B1-B4) steps."""

from itertools import product as cartesian
from collections import Counter

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

for n in [5,6,7,8,9,10,11,12]:
    ms=[2]+[3]*(n-2)+[2]
    def get_table(i, n=n):
        if i==0: return TBotVal
        elif i==1: return TLowVal
        elif i+1==n: return TTopVal
        elif i+2==n: return THighVal
        else: return TMidVal
    def fc(c, n=n): return sum(1 for j in range(n) if c[j]!=c[(j+1)%n])
    def psi(c, n=n):
        s = 0
        for j in range(n):
            if c[j]!=c[(j+1)%n] and c[j]!=c[(j-1)%n]:
                s += 1
        return s
    def step(c,i,n=n):
        L=c[(i-1)%n]; S=c[i]; R=c[(i+1)%n]; out=get_table(i,n)(L,S,R)
        if out!=S: nc=list(c); nc[i]=out; return tuple(nc)
        return None

    all_configs = list(cartesian(*(range(m) for m in ms)))

    pos_psi = Counter()  # fc-positive steps psi change
    neg_psi = Counter()  # fc-negative steps psi change
    nonneg_fc0_psi = Counter()  # nonneg fc-constant psi change

    for c in all_configs:
        for i in range(n):
            s = step(c,i,n)
            if s:
                dfc = fc(s,n) - fc(c,n)
                dpsi = psi(s,n) - psi(c,n)
                if dfc > 0:
                    pos_psi[dpsi] += 1
                elif dfc < 0:
                    neg_psi[dpsi] += 1
                else:
                    nonneg_fc0_psi[dpsi] += 1

    # Check if psi is bounded on pos steps
    if pos_psi:
        max_pos_psi = max(pos_psi.keys())
    else:
        max_pos_psi = 'N/A'
    if neg_psi:
        max_neg_psi = max(neg_psi.keys())
    else:
        max_neg_psi = 'N/A'

    print(f'n={n}:')
    print(f'  pos(fc+): dpsi in {sorted(pos_psi.keys()) if pos_psi else "empty"}')
    print(f'  neg(fc-): dpsi in {sorted(neg_psi.keys()) if neg_psi else "empty"}')
    print(f'  fc=0:     dpsi in {sorted(nonneg_fc0_psi.keys()) if nonneg_fc0_psi else "empty"}')

    if n >= 10:
        break  # too slow for larger n
