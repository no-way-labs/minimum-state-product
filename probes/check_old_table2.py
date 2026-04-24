#!/usr/bin/env python3
"""Verify old table (TMidVal(2,1,1)=2) has working 6-tuple DAG."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import T_bot, T_low, T_high, T_top
from collections import defaultdict, deque

T_mid_old = {
    (0,0,0): 0,  (0,0,1): 0,  (0,0,2): 0,
    (0,1,0): 0,  (0,1,1): 1,  (0,1,2): 0,
    (0,2,0): 0,  (0,2,1): 2,  (0,2,2): 0,
    (1,0,0): 1,  (1,0,1): 1,  (1,0,2): 1,
    (1,1,0): 1,  (1,1,1): 1,  (1,1,2): 2,
    (1,2,0): 0,  (1,2,1): 1,  (1,2,2): 2,
    (2,0,0): 0,  (2,0,1): 0,  (2,0,2): 2,
    (2,1,0): 1,  (2,1,1): 2,  (2,1,2): 2,  # OLD value
    (2,2,0): 0,  (2,2,1): 2,  (2,2,2): 2,
}

def build_old(n):
    ms = [2] + [3]*(n-2) + [2]
    def mf(t):
        return lambda L,S,R: t[(L,S,R)]
    if n == 4:
        fs = [mf(T_bot), mf(T_low), mf(T_high), mf(T_top)]
    elif n == 5:
        fs = [mf(T_bot), mf(T_low), mf(T_mid_old), mf(T_high), mf(T_top)]
    else:
        fs = [mf(T_bot), mf(T_low)] + [mf(T_mid_old)]*(n-4) + [mf(T_high), mf(T_top)]
    return ms, fs

for nn in [9, 10, 11, 12]:
    ms, fs = build_old(nn); N = 1
    for m in ms: N *= m

    def idc(idx, ms=ms, n=nn):
        c = []
        for m in reversed(ms):
            c.append(idx % m); idx //= m
        return tuple(reversed(c))
    def cdi(c, ms=ms, n=nn):
        idx = 0
        for j in range(n): idx = idx * ms[j] + c[j]
        return idx
    def mv(c, pos, fs=fs, n=nn):
        L = c[(pos-1)%n]; S = c[pos]; R = c[(pos+1)%n]
        c2 = list(c); c2[pos] = fs[pos](L, S, R); return tuple(c2)
    def fcc(c, n=nn): return sum(1 for j in range(n) if c[j] != c[(j+1)%n])
    def tpp(c, n=nn):
        e = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
        i21 = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n]==1)
        w = sum(j for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
        return (e, i21, w)
    def b6(c, n=nn): return ((((c[0]*3+c[1])*3+c[2])*3+c[n-3])*3+c[n-2])*2+c[n-1]

    bad = set(); tpa = {}
    for i in range(N):
        if fcc(idc(i)) > 0: bad.add(i); tpa[i] = []
    for i in bad:
        c = idc(i); t = tpp(c)
        for p in range(nn):
            c2 = mv(c, p); j = cdi(c2)
            if c2 != c and j in bad and tpp(c2) == t: tpa[i].append(j)

    pf = {i: fcc(idc(i)) for i in bad}
    rev = {i: [] for i in bad}
    for i in bad:
        for j in tpa[i]: rev[j].append(i)
    ch = True
    while ch:
        ch = False
        for j in bad:
            for i in rev[j]:
                if pf[j] > pf[i]: pf[i] = pf[j]; ch = True

    ff = {i: fcc(idc(i)) for i in bad}
    aa = {i: [] for i in bad}
    for i in bad:
        c = idc(i)
        for p in range(nn):
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

    cphi_edges = set()
    for i in bad:
        for j in tpa[i]:
            if ff[j] == ff[i] and pf[j] == pf[i]:
                c, c2 = idc(i), idc(j)
                b1, b2 = b6(c), b6(c2)
                if b1 != b2: cphi_edges.add((b1, b2))

    # Check DAG
    adj = defaultdict(set); nodes = set()
    for a, b in cphi_edges: adj[a].add(b); nodes.add(a); nodes.add(b)

    # Tarjan's SCC
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

    is_dag = len(sccs) == 0
    max_rank = 0
    if is_dag and nodes:
        out_deg = {c: len(adj.get(c, set())) for c in nodes}
        sinks = [c for c in nodes if out_deg.get(c, 0) == 0]
        rank = {c: 0 for c in sinks}
        radj = defaultdict(list)
        for c in nodes:
            for s in adj.get(c, set()):
                if s in nodes: radj[s].append(c)
        q = deque(sinks)
        while q:
            s = q.popleft()
            for c in radj.get(s, []):
                new_r = rank[s] + 1
                if c not in rank or new_r > rank[c]:
                    rank[c] = new_r; q.append(c)
        max_rank = max(rank.values()) if rank else 0

    print(f"n={nn}: {len(cphi_edges)} CΦ 6-tuple edges, DAG={is_dag}, max_rank={max_rank}, SCCs={len(sccs)}")

# Also compare edge sets
print("\nN-independence check (old table):")
edges_9 = None
for nn in [9, 10, 11, 12]:
    ms, fs = build_old(nn); N = 1
    for m in ms: N *= m
    # (recompute - simplified)
    bad = set(); tpa = {}
    for i in range(N):
        c = []
        idx = i
        for m in reversed(ms):
            c.append(idx % m); idx //= m
        c = tuple(reversed(c))
        fc_val = sum(1 for j in range(nn) if c[j] != c[(j+1)%nn])
        if fc_val > 0: bad.add(i); tpa[i] = []
    for i in bad:
        c = []
        idx = i
        for m in reversed(ms):
            c.append(idx % m); idx //= m
        c = tuple(reversed(c))
        t = tpp(c)
        for p in range(nn):
            c2 = mv(c, p)
            j = cdi(c2)
            if c2 != c and j in bad and tpp(c2) == t: tpa[i].append(j)

    pf = {}
    for i in bad: pf[i] = fcc(idc(i))
    rev = {i: [] for i in bad}
    for i in bad:
        for j in tpa[i]: rev[j].append(i)
    ch = True
    while ch:
        ch = False
        for j in bad:
            for i in rev[j]:
                if pf[j] > pf[i]: pf[i] = pf[j]; ch = True

    ff = {}
    for i in bad: ff[i] = fcc(idc(i))
    aa = {i: [] for i in bad}
    for i in bad:
        c = idc(i)
        for p in range(nn):
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

    cphi_edges = set()
    for i in bad:
        for j in tpa[i]:
            if ff[j] == ff[i] and pf[j] == pf[i]:
                c, c2 = idc(i), idc(j)
                b1, b2 = b6(c), b6(c2)
                if b1 != b2: cphi_edges.add((b1, b2))

    if edges_9 is None:
        edges_9 = cphi_edges
    else:
        print(f"  n={nn} edges match n=9: {cphi_edges == edges_9}")

print("\nDONE")
