#!/usr/bin/env python3
"""
Verify: (sixTuple, fc) combined CΦ boundary-changing graph is a DAG.

The only sixTuple cycle is {239,245,251} with edge 239→245 always fc_down.
In (sixTuple, fc) combined space, this cycle breaks because 239→245 changes fc.

If the combined graph is a DAG, we can define:
  cphiRank(c) = (combinedRank(boundary6(c), fc(c)), deepMidHopPotential(c))
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import build_system
from collections import defaultdict, deque

def analyze_combined(nn):
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
    def b6(c): return ((((c[0]*3+c[1])*3+c[2])*3+c[nn-3])*3+c[nn-2])*2+c[nn-1]

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

    # Combined (sixTuple, fc) graph for CΦ boundary-changing steps
    # Also include boundary-fixed fc-changing steps (already proved fc ≤)
    combined_edges = set()
    for i in bad:
        for j in tpa[i]:
            if ff[j] == ff[i] and pf[j] == pf[i]:
                c, c2 = idc(i), idc(j)
                b1, b2 = b6(c), b6(c2)
                f1, f2 = fcc(c), fcc(c2)
                state1 = (b1, f1)
                state2 = (b2, f2)
                if state1 != state2:  # Skip self-loops (boundary AND fc both same)
                    combined_edges.add((state1, state2))

    # Build adjacency
    adj = defaultdict(set)
    nodes = set()
    for (s1, s2) in combined_edges:
        adj[s1].add(s2); nodes.add(s1); nodes.add(s2)

    # Tarjan's for SCC detection
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

    if is_dag:
        # Compute rank
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
        return True, len(combined_edges), len(nodes), max_rank, rank, combined_edges
    else:
        return False, len(combined_edges), len(nodes), 0, None, sccs

print("=" * 60)
print("COMBINED (sixTuple, fc) CΦ GRAPH")
print("=" * 60)

for nn in [9, 10, 11, 12]:
    is_dag, n_edges, n_nodes, max_rank, rank_dict, extra = analyze_combined(nn)
    print(f"n={nn}: {n_edges} edges, {n_nodes} nodes, DAG={is_dag}, max_rank={max_rank}")
    if not is_dag:
        for scc in extra:
            print(f"  SCC: {sorted(scc)[:10]}")

# Detailed analysis at n=9
print("\n" + "=" * 60)
print("DETAILED ANALYSIS AT n=9")
print("=" * 60)

is_dag, n_edges, n_nodes, max_rank, rank_dict, combined_edges = analyze_combined(9)
if is_dag:
    print(f"✓ Combined graph IS a DAG, max rank = {max_rank}")
    print(f"  {n_nodes} combined states, {n_edges} edges")

    # What fc values appear?
    fc_vals = set(f for (b, f) in rank_dict.keys())
    print(f"  fc values: {sorted(fc_vals)}")
    print(f"  States per fc: {dict(sorted([(f, sum(1 for (b,ff) in rank_dict if ff==f)) for f in fc_vals]))}")

    # Encode combined state as single integer for Lean
    # combined_state = boundary6 * max_fc + fc
    # max fc for n=9 is 9 (or practically, max is around 8)
    max_fc = max(fc_vals)
    print(f"  Max fc in combined states: {max_fc}")
    print(f"  Combined state space: 324 * {max_fc + 1} = {324 * (max_fc + 1)}")

    # Compute rank array indexed by combined state
    combined_size = 324 * (max_fc + 1)
    rank_array = [0] * combined_size
    for (b, f), r in rank_dict.items():
        idx = b * (max_fc + 1) + f
        rank_array[idx] = r

    print(f"\n  Rank array size: {combined_size}")
    print(f"  Non-zero entries: {sum(1 for r in rank_array if r > 0)}")

    # Check n-independence: do the edges at n=10,11,12 match?
    print("\n  N-independence of combined edges:")
    edges_9 = combined_edges
    for nn in [10, 11, 12]:
        _, _, _, _, _, e_nn = analyze_combined(nn)
        print(f"    n={nn}: edges match n=9 = {e_nn == edges_9}")

    # Output for Lean embedding
    print(f"\n  -- Combined edge list ({n_edges} edges)")
    sorted_ce = sorted(combined_edges, key=lambda e: (e[0][0], e[0][1], e[1][0], e[1][1]))
    for a, b in sorted_ce[:10]:
        print(f"    ({a[0]}, {a[1]}) → ({b[0]}, {b[1]})")
    print(f"    ... ({n_edges} total)")

    # For Lean: encode as (boundary6 * 10 + fc, boundary6' * 10 + fc')
    # where 10 > max_fc
    FC_MOD = max_fc + 1
    print(f"\n  Encoding: idx = boundary6 * {FC_MOD} + fc")
    print(f"  Total encoded states: {324 * FC_MOD}")

    # Output rank values
    print(f"\n  -- Combined rank values (max {max_rank}, array size {combined_size})")
    for i in range(0, min(combined_size, 100), 20):
        chunk = rank_array[i:i+20]
        print(f"    [{i}..{i+len(chunk)-1}]: {chunk}")

    # Verify: every combined edge decreases rank
    violations = 0
    for (s1, s2) in combined_edges:
        r1 = rank_dict.get(s1, 0)
        r2 = rank_dict.get(s2, 0)
        if r1 <= r2:
            violations += 1
            if violations <= 5:
                print(f"  VIOLATION: {s1} (rank {r1}) → {s2} (rank {r2})")
    print(f"\n  Rank violations: {violations}")

print("\nDONE")
