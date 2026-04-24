#!/usr/bin/env python3
"""Compare both tables' CΦ 6-tuple graphs and find SCCs."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import T_bot, T_low, T_high, T_top, T_mid as T_mid_new
from collections import defaultdict, deque

T_mid_old = dict(T_mid_new)
T_mid_old[(2,1,1)] = 2  # Revert liveness fix

def analyze(n, T_mid, label):
    ms = [2] + [3]*(n-2) + [2]
    def mf(t): return lambda L,S,R: t[(L,S,R)]
    fs = [mf(T_bot), mf(T_low)] + [mf(T_mid)]*(n-4) + [mf(T_high), mf(T_top)]
    N = 1
    for m in ms: N *= m

    def idc(idx):
        c = []
        for m in reversed(ms): c.append(idx % m); idx //= m
        return tuple(reversed(c))
    def cdi(c):
        idx = 0
        for j in range(n): idx = idx * ms[j] + c[j]
        return idx
    def mv(c, pos):
        L = c[(pos-1)%n]; S = c[pos]; R = c[(pos+1)%n]
        c2 = list(c); c2[pos] = fs[pos](L, S, R); return tuple(c2)
    def fcc(c): return sum(1 for j in range(n) if c[j] != c[(j+1)%n])
    def tpp(c):
        e = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
        i21 = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n]==1)
        w = sum(j for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
        return (e, i21, w)
    def b6(c): return ((((c[0]*3+c[1])*3+c[2])*3+c[n-3])*3+c[n-2])*2+c[n-1]

    bad = set(); tpa = {}
    for i in range(N):
        if fcc(idc(i)) > 0: bad.add(i); tpa[i] = []
    for i in bad:
        c = idc(i); t = tpp(c)
        for p in range(n):
            c2 = mv(c, p); j = cdi(c2)
            if c2 != c and j in bad and tpp(c2) == t: tpa[i].append(j)

    pf = {i: fcc(idc(i)) for i in bad}
    rev = {i: [] for i in bad}
    for i in bad:
        for j in tpa[i]: rev[j].append(i)
    ch = True; iters = 0
    while ch:
        ch = False; iters += 1
        for j in bad:
            for i in rev[j]:
                if pf[j] > pf[i]: pf[i] = pf[j]; ch = True

    ff = {i: fcc(idc(i)) for i in bad}
    aa = {i: [] for i in bad}
    for i in bad:
        c = idc(i)
        for p in range(n):
            c2 = mv(c, p); j = cdi(c2)
            if c2 != c and j in bad: aa[i].append(j)
    ar = {i: [] for i in bad}
    for i in bad:
        for j in aa[i]: ar[j].append(i)
    ch = True
    while ch:
        ch = False
        for j in bad:
            for i in ar[j]:
                if ff[j] > ff[i]: ff[i] = ff[j]; ch = True

    cphi = set()
    for i in bad:
        for j in tpa[i]:
            if ff[j] == ff[i] and pf[j] == pf[i]:
                c, c2 = idc(i), idc(j)
                b1, b2 = b6(c), b6(c2)
                if b1 != b2: cphi.add((b1, b2))

    adj = defaultdict(set); nodes = set()
    for a, b in cphi: adj[a].add(b); nodes.add(a); nodes.add(b)

    # Tarjan's
    idx_c = [0]; stk = []; ll = {}; ix = {}; ons = set(); sccs = []
    def sc(v):
        ix[v] = idx_c[0]; ll[v] = idx_c[0]; idx_c[0] += 1
        stk.append(v); ons.add(v)
        for w in adj.get(v, set()):
            if w not in ix: sc(w); ll[v] = min(ll[v], ll[w])
            elif w in ons: ll[v] = min(ll[v], ix[w])
        if ll[v] == ix[v]:
            s = []
            while True:
                w = stk.pop(); ons.discard(w); s.append(w)
                if w == v: break
            if len(s) > 1: sccs.append(s)
    sys.setrecursionlimit(10000)
    for v in nodes:
        if v not in ix: sc(v)

    print(f"{label} n={n}: {len(cphi)} edges, Φ_full iters={iters}, SCCs={len(sccs)}")
    for scc in sccs:
        print(f"  SCC: {sorted(scc)}")

    # Also check with UNDER-converged Φ_full (23 iterations like the original bug)
    pf_under = {i: fcc(idc(i)) for i in bad}
    for _ in range(23):
        for j in bad:
            for i in rev[j]:
                if pf_under[j] > pf_under[i]: pf_under[i] = pf_under[j]

    cphi_under = set()
    for i in bad:
        for j in tpa[i]:
            if ff[j] == ff[i] and pf_under[j] == pf_under[i]:
                c, c2 = idc(i), idc(j)
                b1, b2 = b6(c), b6(c2)
                if b1 != b2: cphi_under.add((b1, b2))

    adj2 = defaultdict(set)
    for a, b in cphi_under: adj2[a].add(b)
    nodes2 = set()
    for a, b in cphi_under: nodes2.add(a); nodes2.add(b)
    ic2 = [0]; sk2 = []; l2 = {}; i2 = {}; o2 = set(); s2 = []
    def sc2(v):
        i2[v] = ic2[0]; l2[v] = ic2[0]; ic2[0] += 1
        sk2.append(v); o2.add(v)
        for w in adj2.get(v, set()):
            if w not in i2: sc2(w); l2[v] = min(l2[v], l2[w])
            elif w in o2: l2[v] = min(l2[v], i2[w])
        if l2[v] == i2[v]:
            s = []
            while True:
                w = sk2.pop(); o2.discard(w); s.append(w)
                if w == v: break
            if len(s) > 1: s2.append(s)
    for v in nodes2:
        if v not in i2: sc2(v)

    print(f"  Under-converged (23 iters): {len(cphi_under)} edges, SCCs={len(s2)}")

for n in [9]:
    analyze(n, T_mid_old, "OLD (2,1,1)=2")
    analyze(n, T_mid_new, "NEW (2,1,1)=0")

print("\nDONE")
