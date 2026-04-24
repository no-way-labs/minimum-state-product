#!/usr/bin/env python3
"""Check weighted psi (cup2Psi) behavior on BAD steps."""

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

for n in [5,6,7,8,9]:
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
    adj = defaultdict(list)
    for c in all_configs:
        for i in range(n):
            s = step(c,i,n)
            if s: adj[c].append(s)

    # Tarjan SCC
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

    neg_wpsi = Counter()
    pos_wpsi = Counter()
    fc0_wpsi = Counter()
    # Also check (n-fc, wpsi) lex on ALL bad steps
    violations = 0
    total = 0

    for c in bad_set:
        for s in adj.get(c,[]):
            if s not in bad_set: continue
            total += 1
            dfc = fc(s,n) - fc(c,n)
            dwpsi = cup2Psi(s,n) - cup2Psi(c,n)
            if dfc > 0:
                pos_wpsi[dwpsi] += 1
            elif dfc < 0:
                neg_wpsi[dwpsi] += 1
            else:
                fc0_wpsi[dwpsi] += 1
            # Check lex
            nfc_c = n - fc(c,n)
            nfc_s = n - fc(s,n)
            wpsi_c = cup2Psi(c,n)
            wpsi_s = cup2Psi(s,n)
            if nfc_s < nfc_c:
                pass
            elif nfc_s == nfc_c and wpsi_s < wpsi_c:
                pass
            else:
                violations += 1

    print(f'n={n} (BAD steps, weighted psi):')
    print(f'  pos(fc+): dwpsi in {sorted(pos_wpsi.keys()) if pos_wpsi else "empty"}')
    print(f'  neg(fc-): dwpsi in {sorted(neg_wpsi.keys()) if neg_wpsi else "empty"}')
    print(f'  fc=0:     dwpsi in {sorted(fc0_wpsi.keys()) if fc0_wpsi else "empty"}')
    print(f'  (n-fc,wpsi) lex violations: {violations}/{total}')
