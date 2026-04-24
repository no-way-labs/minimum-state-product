#!/usr/bin/env python3
"""Check psi behavior on BAD steps only, by fc change category."""

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

for n in [5,6,7,8,9]:
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
    all_succ = defaultdict(list)
    for c in all_configs:
        for i in range(n):
            s = step(c,i,n)
            if s: all_succ[c].append((s, i))

    # Find good set via Tarjan SCC
    adj = defaultdict(list)
    for c in all_configs:
        for s, _ in all_succ[c]:
            adj[c].append(s)

    idx_c=[0];stack=[];ll={};im={};ons=set();sccs=[]
    for s in all_configs:
        if s in im: continue
        cs=[(s,iter(adj.get(s,[])))]; im[s]=ll[s]=idx_c[0]; idx_c[0]+=1
        stack.append(s); ons.add(s)
        while cs:
            v,ch=cs[-1]
            try:
                w=next(ch)
                if w not in im:
                    im[w]=ll[w]=idx_c[0]; idx_c[0]+=1; stack.append(w); ons.add(w)
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

    terminal = []
    for i,scc in enumerate(sccs):
        ss = set(scc)
        if not any(w not in ss for v in scc for w in adj.get(v,[])): terminal.append(i)
    good_set = set(sccs[terminal[0]])
    bad_set = set(c for c in all_configs if c not in good_set)

    pos_psi = Counter()
    neg_psi = Counter()
    fc0_psi = Counter()

    for c in bad_set:
        for s, i in all_succ[c]:
            if s not in bad_set:
                continue  # step exits bad set, skip for now
            # Actually badStep includes steps from bad to bad AND bad to good
            # But for WF we only care about bad configs
            pass
        # Actually badStep c' c requires both c and c' are bad
        for s, i in all_succ[c]:
            dfc = fc(s,n) - fc(c,n)
            dpsi = psi(s,n) - psi(c,n)
            # s is the successor of c (step from c to s)
            # In WF: badStep s c
            # Need s to be bad too? Actually badStep requires:
            # c is not good, s is not good (both bad)
            # And there's a step from c to s
            if s in bad_set:
                if dfc > 0:
                    pos_psi[dpsi] += 1
                elif dfc < 0:
                    neg_psi[dpsi] += 1
                else:
                    fc0_psi[dpsi] += 1

    print(f'n={n} (BAD steps only):')
    print(f'  pos(fc+): dpsi in {sorted(pos_psi.keys()) if pos_psi else "empty"}')
    print(f'  neg(fc-): dpsi in {sorted(neg_psi.keys()) if neg_psi else "empty"}')
    print(f'  fc=0:     dpsi in {sorted(fc0_psi.keys()) if fc0_psi else "empty"}')

    # Check (n-fc, psi) lex on BAD steps only
    violations = 0
    total = sum(pos_psi.values()) + sum(neg_psi.values()) + sum(fc0_psi.values())
    for c in bad_set:
        for s, i in all_succ[c]:
            if s not in bad_set:
                continue
            nfc_c = n - fc(c,n)
            nfc_s = n - fc(s,n)
            psi_c = psi(c,n)
            psi_s = psi(s,n)
            if nfc_s < nfc_c:
                pass
            elif nfc_s == nfc_c and psi_s < psi_c:
                pass
            else:
                violations += 1
    print(f'  (n-fc,psi) lex violations: {violations}/{total}')
