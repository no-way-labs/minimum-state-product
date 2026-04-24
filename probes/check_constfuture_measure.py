#!/usr/bin/env python3
"""Find a measure that works for ALL const-future bad steps.
We know (n-fc, psi) works for nonneg and fc strictly decreases on neg.
For const-future, we need a SINGLE measure that handles both nonneg and neg const-future."""

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
    if cup2FrontierTypeVal(a, b) == 1: return cup2W1(n, j)
    else: return cup2W2(n, j)
def cup2Psi(c, n):
    total = 0
    for j in range(n):
        total += cup2PsiWeightVal(n, j, c[j], c[(j+1)%n])
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
    all_succ_full = defaultdict(list)  # (successor, position)
    for c in all_configs:
        for i in range(n):
            s = step(c,i,n)
            if s: all_succ_full[c].append((s,i))

    # Compute SCC to find bad set
    adj = defaultdict(list)
    for c in all_configs:
        for s,_ in all_succ_full[c]: adj[c].append(s)
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
    bad_adj = defaultdict(list)  # bad successors
    for c in bad_set:
        for s,i in all_succ_full.get(c,[]):
            if s in bad_set: bad_adj[c].append((s,i))

    fc_cache = {c:fc(c,n) for c in bad_set}
    psi_cache = {c:cup2Psi(c,n) for c in bad_set}

    # Compute FutureFc
    future_fc = {}
    for c in bad_set:
        visited={c}; queue=[c]; mf=fc_cache[c]; qi=0
        while qi<len(queue):
            v=queue[qi]; qi+=1
            for w,_ in bad_adj.get(v,[]):
                if w not in visited:
                    visited.add(w); queue.append(w)
                    if fc_cache[w]>mf: mf=fc_cache[w]
        future_fc[c] = mf

    # Within constant-FutureFc, check various measures
    # Measure 1: (F-fc, psi) lex — KNOWN to fail
    # Measure 2: (F-fc, n*n - psi) lex — inverted psi
    # Measure 3: F*n - fc — single Nat combining gap and fc
    # Measure 4: (gap, gap*n + (n-fc)) lex — emphasize gap

    # Check: does simple (F - fc) strictly decrease on ALL const-future?
    gap_violations = 0
    gap_total = 0

    # Check: on neg const-future, does gap increase? On nonneg const-future, what?
    neg_cf_gap_up = 0
    neg_cf_gap_same = 0
    neg_cf_gap_down = 0
    nonneg_cf_gap_up = 0
    nonneg_cf_gap_same = 0
    nonneg_cf_gap_down = 0

    for c in bad_set:
        F = future_fc[c]
        for s,i in bad_adj.get(c,[]):
            if future_fc[s] != F: continue
            gap_total += 1
            gap_c = F - fc_cache[c]
            gap_s = F - fc_cache[s]
            if gap_s >= gap_c:
                gap_violations += 1

            if fc_cache[s] < fc_cache[c]:  # neg
                if gap_s > gap_c: neg_cf_gap_up += 1
                elif gap_s == gap_c: neg_cf_gap_same += 1
                else: neg_cf_gap_down += 1
            else:  # nonneg
                if gap_s > gap_c: nonneg_cf_gap_up += 1
                elif gap_s == gap_c: nonneg_cf_gap_same += 1
                else: nonneg_cf_gap_down += 1

    print(f'n={n}: gap_violations={gap_violations}/{gap_total}')
    print(f'  neg CF: gap_up={neg_cf_gap_up}, same={neg_cf_gap_same}, down={neg_cf_gap_down}')
    print(f'  nonneg CF: gap_up={nonneg_cf_gap_up}, same={nonneg_cf_gap_same}, down={nonneg_cf_gap_down}')

    # On neg CF: gap = F - fc. After neg: fc drops, so gap increases.
    # On nonneg CF: fc non-decreasing, so gap non-increasing.
    # → gap strictly decreases on nonneg CF where fc increases (pos CF),
    #   and stays same on nonneg fc-constant CF.

    # So: (gap, psi) lex should work for nonneg CF (gap drops or stays same + psi drops)
    # But on neg CF, gap INCREASES. So (gap, psi) lex fails.

    # What about (gap, psi) where on neg CF, gap goes up but we use wf_of_copy_segment_wf?
    # copy = nonneg_CF, anom = neg_CF
    # segment: ReflTransGen nonneg_CF z x ∧ neg_CF y z
    # Along nonneg_CF chain: (gap, psi) lex decreases
    # gap(z) ≤ gap(x), gap is F - fc
    # If gap(z) < gap(x): pos step in chain, fc increased
    # If gap(z) = gap(x): fc constant, psi decreased
    # neg_CF step z→y: gap(y) = F - fc(y) > F - fc(z) = gap(z). So gap increases.
    # Segment measure = gap(x)? gap(y) > gap(z) ≤ gap(x). So gap(y) vs gap(x) unknown.
    # Same problem as before.

    # NEW IDEA: check if (gap, psi) lex works as segment measure
    # i.e., (gap(y), psi(y)) <lex (gap(x), psi(x))
    # We need gap(y) < gap(x) or (gap(y) = gap(x) and psi(y) < psi(x))

    # From the chain: (gap(z), psi(z)) <lex (gap(x), psi(x)) or z = x
    # neg step: gap(y) > gap(z), psi(y) = ?
    #
    # Case z = x (empty chain): neg_CF from x to y directly
    #   gap(y) > gap(x) — first component INCREASES. Bad!
    # So this doesn't work.

    # What about copy = gap-constant nonneg CF, anom = gap-changing CF?
    # copy: fc constant (since gap = F-fc constant means fc constant), psi drops → WF
    # anom: fc changes. If pos: gap drops. If neg: gap increases. Both possible.
    # Use gap as segment measure? Along copy chain: gap constant.
    # anom: if pos, gap drops → good. If neg, gap increases → bad.
    # Need TWO levels:
    # Level 1: copy = gap-constant nonneg CF (= fc-constant CF), anom = pos CF
    #   segment: chain of fc-constant then pos. gap(y) < gap(x) from pos.
    #   But along fc-constant chain, gap is constant. After pos: gap drops by ≥ 1.
    #   Segment measure = gap → WF! ✓
    #   Result: WF of (fc-constant CF ∨ pos CF) = nonneg CF
    # Level 2: copy = nonneg CF (WF from level 1), anom = neg CF
    #   segment: chain of nonneg CF then neg.
    #   Along nonneg CF: gap non-increasing. After neg: gap increases.
    #   Segment measure = ???
    #   Same problem.

    # WAIT. For Level 2, along the nonneg CF chain: gap = F - fc.
    # nonneg: fc non-decreasing → gap non-increasing.
    # neg: fc drops → gap increases.
    # After chain: gap(z) ≤ gap(x). After neg: gap(y) > gap(z).
    # Need gap(y) < gap(x)?
    # gap(y) = gap(z) + Δgap_neg where Δgap_neg ≥ 1
    # gap(z) ≤ gap(x) - Δgap_nonneg where Δgap_nonneg ≥ 0 (total gap decrease from nonneg chain)
    # gap(y) ≤ gap(x) - Δgap_nonneg + Δgap_neg
    # Need gap(y) < gap(x): Δgap_neg < Δgap_nonneg
    # But Δgap_neg ≥ 1 and Δgap_nonneg could be 0 (if all nonneg steps are fc-constant).
    # So gap(y) could exceed gap(x). DOESN'T WORK.

    print()
