#!/usr/bin/env python3
"""
Check 8-tuple (c[0..3], c[n-4..n-1]) CΦ boundary-changing DAG.
State space: 2 * 3^6 * 2 = 2916 (for n >= 10).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import build_system
from collections import defaultdict, deque

def analyze_8tuple(nn):
    ms, fs = build_system(nn); N = 1
    for m in ms: N *= m

    def idc(idx):
        c = []
        for m in reversed(ms):
            c.append(idx % m); idx //= m
        return tuple(reversed(c))
    def cdi(c):
        idx = 0
        for j in range(nn): idx = idx * ms[j] + c[j]
        return idx
    def mv(c, pos):
        L = c[(pos-1)%nn]; S = c[pos]; R = c[(pos+1)%nn]
        c2 = list(c); c2[pos] = fs[pos](L, S, R); return tuple(c2)
    def fcc(c): return sum(1 for j in range(nn) if c[j] != c[(j+1)%nn])
    def tpp(c):
        e = sum(1 for j in range(2,nn-2) if c[j]==2 and c[(j+1)%nn] in (0,1))
        i21 = sum(1 for j in range(2,nn-2) if c[j]==2 and c[(j+1)%nn]==1)
        w = sum(j for j in range(2,nn-2) if c[j]==2 and c[(j+1)%nn] in (0,1))
        return (e, i21, w)
    def b8(c):
        # 8-tuple: c[0], c[1], c[2], c[3], c[n-4], c[n-3], c[n-2], c[n-1]
        # Encode: ((((((c[0]*3+c[1])*3+c[2])*3+c[3])*3+c[n-4])*3+c[n-3])*3+c[n-2])*2+c[n-1]
        return ((((((c[0]*3+c[1])*3+c[2])*3+c[3])*3+c[nn-4])*3+c[nn-3])*3+c[nn-2])*2+c[nn-1]
    def b6(c):
        return ((((c[0]*3+c[1])*3+c[2])*3+c[nn-3])*3+c[nn-2])*2+c[nn-1]

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

    # 8-tuple and 6-tuple CΦ boundary-changing edges
    edges_8 = set()
    edges_6 = set()
    for i in bad:
        for j in tpa[i]:
            if ff[j] == ff[i] and pf[j] == pf[i]:
                c, c2 = idc(i), idc(j)
                b8_src, b8_dst = b8(c), b8(c2)
                b6_src, b6_dst = b6(c), b6(c2)
                if b8_src != b8_dst:
                    edges_8.add((b8_src, b8_dst))
                if b6_src != b6_dst:
                    edges_6.add((b6_src, b6_dst))

    # Check DAG for 8-tuple
    adj = defaultdict(set); nodes = set()
    for a, b in edges_8: adj[a].add(b); nodes.add(a); nodes.add(b)

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
    sys.setrecursionlimit(50000)
    for v in nodes:
        if v not in ix: sc(v)

    is_dag = len(sccs) == 0
    max_rank = 0
    rank_dict = {}
    if is_dag:
        out_deg = {c: len(adj.get(c, set())) for c in nodes}
        sinks = [c for c in nodes if out_deg.get(c, 0) == 0]
        rank_dict = {c: 0 for c in sinks}
        radj = defaultdict(list)
        for c in nodes:
            for s in adj.get(c, set()):
                if s in nodes: radj[s].append(c)
        q = deque(sinks)
        while q:
            s = q.popleft()
            for c in radj.get(s, []):
                new_r = rank_dict[s] + 1
                if c not in rank_dict or new_r > rank_dict[c]:
                    rank_dict[c] = new_r; q.append(c)
        max_rank = max(rank_dict.values()) if rank_dict else 0

    return {
        'n': nn,
        'edges_8': len(edges_8),
        'edges_6': len(edges_6),
        'nodes_8': len(nodes),
        'is_dag': is_dag,
        'max_rank': max_rank,
        'sccs': sccs,
        'edge_set_8': edges_8,
        'rank_dict': rank_dict,
    }

# Note: 8-tuple requires n >= 10 for non-overlapping positions
# At n=9, positions 3 and n-4=5 are distinct but c[3] through c[5] are contiguous interior
print("=" * 60)
print("8-TUPLE CΦ DAG ANALYSIS")
print("=" * 60)

for nn in [10, 11, 12, 13]:
    r = analyze_8tuple(nn)
    print(f"n={r['n']}: 8-tuple {r['edges_8']} edges, {r['nodes_8']} nodes, "
          f"6-tuple {r['edges_6']} edges, DAG={r['is_dag']}, max_rank={r['max_rank']}")
    if not r['is_dag']:
        print(f"  SCCs: {len(r['sccs'])}")
        for scc in r['sccs'][:3]:
            print(f"    SCC of size {len(scc)}")

# Check n-independence of edge set
print("\nN-independence check:")
edges_10 = analyze_8tuple(10)['edge_set_8']
for nn in [11, 12, 13]:
    edges_nn = analyze_8tuple(nn)['edge_set_8']
    print(f"  n={nn} edges == n=10 edges: {edges_nn == edges_10}")

# Also try 7-tuple: add only c[n-4] (to disambiguate the cycle at n-3)
# The cycle was at positions (c[0..2], c[n-3..n-1]) = (1,1,1,X,2,1)
# The move at n-3 depends on c[n-4]. So adding c[n-4] should break the cycle.
print("\n" + "=" * 60)
print("7-TUPLE (c[0..2], c[n-4..n-1]) ANALYSIS")
print("=" * 60)

def analyze_7tuple(nn):
    ms, fs = build_system(nn); N = 1
    for m in ms: N *= m

    def idc(idx):
        c = []
        for m in reversed(ms):
            c.append(idx % m); idx //= m
        return tuple(reversed(c))
    def cdi(c):
        idx = 0
        for j in range(nn): idx = idx * ms[j] + c[j]
        return idx
    def mv(c, pos):
        L = c[(pos-1)%nn]; S = c[pos]; R = c[(pos+1)%nn]
        c2 = list(c); c2[pos] = fs[pos](L, S, R); return tuple(c2)
    def fcc(c): return sum(1 for j in range(nn) if c[j] != c[(j+1)%nn])
    def tpp(c):
        e = sum(1 for j in range(2,nn-2) if c[j]==2 and c[(j+1)%nn] in (0,1))
        i21 = sum(1 for j in range(2,nn-2) if c[j]==2 and c[(j+1)%nn]==1)
        w = sum(j for j in range(2,nn-2) if c[j]==2 and c[(j+1)%nn] in (0,1))
        return (e, i21, w)
    def b7(c):
        # 7-tuple: c[0], c[1], c[2], c[n-4], c[n-3], c[n-2], c[n-1]
        # States: 2 * 3^5 * 2 = 972
        return (((((c[0]*3+c[1])*3+c[2])*3+c[nn-4])*3+c[nn-3])*3+c[nn-2])*2+c[nn-1]

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

    edges_7 = set()
    for i in bad:
        for j in tpa[i]:
            if ff[j] == ff[i] and pf[j] == pf[i]:
                c, c2 = idc(i), idc(j)
                b7_src, b7_dst = b7(c), b7(c2)
                if b7_src != b7_dst:
                    edges_7.add((b7_src, b7_dst))

    adj = defaultdict(set); nodes = set()
    for a, b in edges_7: adj[a].add(b); nodes.add(a); nodes.add(b)

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
    sys.setrecursionlimit(50000)
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

    return len(edges_7), len(nodes), is_dag, max_rank, len(sccs), edges_7

for nn in [10, 11, 12, 13]:
    ne, nn2, dag, mr, ns, e_set = analyze_7tuple(nn)
    print(f"n={nn}: 7-tuple {ne} edges, {nn2} nodes, DAG={dag}, max_rank={mr}")

# N-independence
e10 = analyze_7tuple(10)[5]
for nn in [11, 12, 13]:
    e_nn = analyze_7tuple(nn)[5]
    print(f"  n={nn} edges == n=10: {e_nn == e10}")

print("\nDONE")
