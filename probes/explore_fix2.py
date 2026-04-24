#!/usr/bin/env python3
"""
Verify Option C: use (fc, sixStateRankNew, deepMidHopPotential) as lex measure.

Key insight from explore_fix.py:
- 6-tuple CΦ graph has exactly 1 SCC: {239, 245, 251}
- Cycle edges: 239→245 (ALWAYS fc_down), 245→251 (fc_same), 251→239 (fc_same)
- Remove 239→245 → 616-edge DAG

For this to work, we need:
1. The 616-edge graph is a DAG
2. Every boundary-changing CΦ step with fc PRESERVED has its 6-tuple edge in the 616-edge DAG
3. fc is non-increasing on boundary-changing CΦ steps (so no fc_up case)

If fc CAN increase on boundary-changing steps, we need a different approach.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import build_system
from collections import defaultdict, deque

n = 9; ms, fs = build_system(n); N = 1
for m in ms: N *= m

def idx_to_config(idx):
    c = []
    for m in reversed(ms):
        c.append(idx % m); idx //= m
    return tuple(reversed(c))
def config_to_idx(c):
    idx = 0
    for j in range(n): idx = idx * ms[j] + c[j]
    return idx
def move(c, pos):
    L = c[(pos-1)%n]; S = c[pos]; R = c[(pos+1)%n]
    c2 = list(c); c2[pos] = fs[pos](L, S, R); return tuple(c2)
def fc(c): return sum(1 for j in range(n) if c[j] != c[(j+1)%n])
def tp(c):
    e = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
    i21 = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n]==1)
    w = sum(j for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
    return (e, i21, w)
def boundary6(c): return ((((c[0]*3+c[1])*3+c[2])*3+c[n-3])*3+c[n-2])*2+c[n-1]

bad_set = set(); tp_adj = {}
for i in range(N):
    if fc(idx_to_config(i)) > 0:
        bad_set.add(i); tp_adj[i] = []
for i in bad_set:
    c = idx_to_config(i); t = tp(c)
    for p in range(n):
        c2 = move(c, p); j = config_to_idx(c2)
        if c2 != c and j in bad_set and tp(c2) == t:
            tp_adj[i].append(j)

phi_full = {i: fc(idx_to_config(i)) for i in bad_set}
tp_rev = {i: [] for i in bad_set}
for i in bad_set:
    for j in tp_adj[i]: tp_rev[j].append(i)
changed = True
while changed:
    changed = False
    for j in bad_set:
        for i in tp_rev[j]:
            if phi_full[j] > phi_full[i]:
                phi_full[i] = phi_full[j]; changed = True

future_fc = {i: fc(idx_to_config(i)) for i in bad_set}
all_adj = {i: [] for i in bad_set}
for i in bad_set:
    c = idx_to_config(i)
    for p in range(n):
        c2 = move(c, p); j = config_to_idx(c2)
        if c2 != c and j in bad_set: all_adj[i].append(j)
all_rev = {i: [] for i in bad_set}
for i in bad_set:
    for j in all_adj[i]: all_rev[j].append(i)
changed = True
while changed:
    changed = False
    for j in bad_set:
        for i in all_rev[j]:
            if future_fc[j] > future_fc[i]:
                future_fc[i] = future_fc[j]; changed = True

# Collect all boundary-changing CΦ full-config edges
print("=" * 60)
print("FC DIRECTION ON BOUNDARY-CHANGING CΦ STEPS")
print("=" * 60)

fc_up_count = 0
fc_same_count = 0
fc_down_count = 0
fc_up_edges = set()  # 6-tuple edges that have at least one fc-up instance

cphi_6tuple_edges = set()
edge_fc_always = {}  # (b_src, b_dst) -> set of fc directions

for i in bad_set:
    for j in tp_adj[i]:
        if future_fc[j] == future_fc[i] and phi_full[j] == phi_full[i]:
            c, c2 = idx_to_config(i), idx_to_config(j)
            b1, b2 = boundary6(c), boundary6(c2)
            if b1 != b2:
                cphi_6tuple_edges.add((b1, b2))
                delta = fc(c2) - fc(c)
                if delta > 0:
                    fc_up_count += 1
                    fc_up_edges.add((b1, b2))
                elif delta == 0:
                    fc_same_count += 1
                else:
                    fc_down_count += 1
                edge = (b1, b2)
                if edge not in edge_fc_always:
                    edge_fc_always[edge] = set()
                if delta > 0: edge_fc_always[edge].add("up")
                elif delta == 0: edge_fc_always[edge].add("same")
                else: edge_fc_always[edge].add("down")

print(f"Total boundary-changing CΦ instances: {fc_up_count + fc_same_count + fc_down_count}")
print(f"  fc increases: {fc_up_count}")
print(f"  fc same: {fc_same_count}")
print(f"  fc decreases: {fc_down_count}")
print(f"\n6-tuple edges with fc_up instances: {len(fc_up_edges)}")
print(f"Total 6-tuple edges: {len(cphi_6tuple_edges)}")

# Classify edges
always_down = set()
always_same = set()
always_up = set()
mixed = set()
for edge, dirs in edge_fc_always.items():
    if dirs == {"down"}: always_down.add(edge)
    elif dirs == {"same"}: always_same.add(edge)
    elif dirs == {"up"}: always_up.add(edge)
    else: mixed.add(edge)

print(f"\nEdge classification:")
print(f"  Always fc_down: {len(always_down)}")
print(f"  Always fc_same: {len(always_same)}")
print(f"  Always fc_up: {len(always_up)}")
print(f"  Mixed: {len(mixed)}")

if mixed:
    print(f"\nMixed edges (PROBLEMATIC):")
    for edge in sorted(mixed):
        print(f"  {edge[0]} → {edge[1]}: {edge_fc_always[edge]}")

print("\n" + "=" * 60)
print("APPROACH: (fc, sixStateRank_616, deepMidHop)")
print("=" * 60)

# Remove all edges that are always fc_down
# These are handled by the fc component
remaining_edges = cphi_6tuple_edges - always_down
print(f"Remaining edges after removing always-fc-down: {len(remaining_edges)}")

# Check if remaining is DAG
adj_rem = defaultdict(set)
nodes_rem = set()
for a, b in remaining_edges:
    adj_rem[a].add(b); nodes_rem.add(a); nodes_rem.add(b)

# Tarjan's
idx_c = [0]; stk = []; ll = {}; ix = {}; ons = set(); sccs = []
def sc(v):
    ix[v] = idx_c[0]; ll[v] = idx_c[0]; idx_c[0] += 1
    stk.append(v); ons.add(v)
    for w in adj_rem.get(v, set()):
        if w not in ix: sc(w); ll[v] = min(ll[v], ll[w])
        elif w in ons: ll[v] = min(ll[v], ix[w])
    if ll[v] == ix[v]:
        s = []
        while True:
            w = stk.pop(); ons.discard(w); s.append(w)
            if w == v: break
        if len(s) > 1: sccs.append(s)

sys.setrecursionlimit(10000)
for v in nodes_rem:
    if v not in ix: sc(v)

if not sccs:
    print("→ Remaining edges form a DAG! ✓")
    out_deg = {c: len(adj_rem.get(c, set())) for c in nodes_rem}
    sinks = [c for c in nodes_rem if out_deg.get(c, 0) == 0]
    rank = {c: 0 for c in sinks}
    radj = defaultdict(list)
    for c in nodes_rem:
        for s in adj_rem.get(c, set()):
            if s in nodes_rem: radj[s].append(c)
    q = deque(sinks)
    while q:
        s = q.popleft()
        for c in radj.get(s, []):
            new_r = rank[s] + 1
            if c not in rank or new_r > rank[c]:
                rank[c] = new_r; q.append(c)
    max_rank = max(rank.values()) if rank else 0
    print(f"  Max rank: {max_rank}")
    print(f"  Nodes: {len(nodes_rem)}")

    # Output the new edge list and rank values for Lean
    all_ranks = [0] * 324
    for s in range(324):
        if s in rank: all_ranks[s] = rank[s]

    sorted_edges = sorted(remaining_edges)
    print(f"\n  -- New edge list ({len(sorted_edges)} edges)")

    # Output for Lean
    print(f"\n  -- New rank values (max {max_rank})")
    for i in range(0, 324, 18):
        chunk = all_ranks[i:i+18]
        print("    " + ", ".join(str(v) for v in chunk) + ",")
else:
    print(f"→ STILL has {len(sccs)} SCCs!")
    for s in sccs:
        print(f"  {sorted(s)}")

# Now check: do mixed edges break things?
if mixed:
    print("\n" + "=" * 60)
    print("MIXED EDGE ANALYSIS")
    print("=" * 60)
    print("Mixed edges have both fc-down and fc-same/up instances.")
    print("For Option C, we need these to be in the remaining DAG AND fc to be non-increasing.")
    print()
    for edge in sorted(mixed):
        in_remaining = edge in remaining_edges
        print(f"  {edge[0]} → {edge[1]}: dirs={edge_fc_always[edge]}, in remaining DAG: {in_remaining}")
        if not in_remaining:
            print(f"    WARNING: not in DAG but has fc-preserving instances!")

# Check n-independence of the remaining edges
print("\n" + "=" * 60)
print("N-INDEPENDENCE CHECK")
print("=" * 60)

for nn in [10, 11, 12]:
    ms2, fs2 = build_system(nn)
    N2 = 1
    for m in ms2: N2 *= m

    def idc2(idx):
        c = []
        for m in reversed(ms2):
            c.append(idx % m); idx //= m
        return tuple(reversed(c))
    def cdi2(c):
        idx = 0
        for j in range(nn): idx = idx * ms2[j] + c[j]
        return idx
    def mv2(c, pos):
        L = c[(pos-1)%nn]; S = c[pos]; R = c[(pos+1)%nn]
        c2 = list(c); c2[pos] = fs2[pos](L, S, R); return tuple(c2)
    def fc2(c): return sum(1 for j in range(nn) if c[j] != c[(j+1)%nn])
    def tp2(c):
        e = sum(1 for j in range(2,nn-2) if c[j]==2 and c[(j+1)%nn] in (0,1))
        i21 = sum(1 for j in range(2,nn-2) if c[j]==2 and c[(j+1)%nn]==1)
        w = sum(j for j in range(2,nn-2) if c[j]==2 and c[(j+1)%nn] in (0,1))
        return (e, i21, w)
    def b6_2(c): return ((((c[0]*3+c[1])*3+c[2])*3+c[nn-3])*3+c[nn-2])*2+c[nn-1]

    bad2 = set(); tp2a = {}
    for i in range(N2):
        if fc2(idc2(i)) > 0: bad2.add(i); tp2a[i] = []
    for i in bad2:
        c = idc2(i); t = tp2(c)
        for p in range(nn):
            c2 = mv2(c, p); j = cdi2(c2)
            if c2 != c and j in bad2 and tp2(c2) == t: tp2a[i].append(j)

    pf2 = {i: fc2(idc2(i)) for i in bad2}
    rev2 = {i: [] for i in bad2}
    for i in bad2:
        for j in tp2a[i]: rev2[j].append(i)
    ch = True
    while ch:
        ch = False
        for j in bad2:
            for i in rev2[j]:
                if pf2[j] > pf2[i]: pf2[i] = pf2[j]; ch = True

    ff2 = {i: fc2(idc2(i)) for i in bad2}
    aa2 = {i: [] for i in bad2}
    for i in bad2:
        c = idc2(i)
        for p in range(nn):
            c2 = mv2(c, p); j = cdi2(c2)
            if c2 != c and j in bad2: aa2[i].append(j)
    ar2 = {i: [] for i in bad2}
    for i in bad2:
        for j in aa2[i]: ar2[j].append(i)
    ch = True
    while ch:
        ch = False
        for j in bad2:
            for i in ar2[j]:
                if ff2[j] > ff2[i]: ff2[i] = ff2[j]; ch = True

    # CΦ boundary-changing edges, split by fc direction
    ad_nn = set(); as_nn = set(); au_nn = set(); mx_nn = set()
    efa = {}
    for i in bad2:
        for j in tp2a[i]:
            if ff2[j] == ff2[i] and pf2[j] == pf2[i]:
                c, c2 = idc2(i), idc2(j)
                b1, b2 = b6_2(c), b6_2(c2)
                if b1 != b2:
                    edge = (b1, b2)
                    d = fc2(c2) - fc2(c)
                    if edge not in efa: efa[edge] = set()
                    if d > 0: efa[edge].add("up")
                    elif d == 0: efa[edge].add("same")
                    else: efa[edge].add("down")

    for edge, dirs in efa.items():
        if dirs == {"down"}: ad_nn.add(edge)
        elif dirs == {"same"}: as_nn.add(edge)
        elif dirs == {"up"}: au_nn.add(edge)
        else: mx_nn.add(edge)

    rem_nn = set(efa.keys()) - ad_nn  # Remove always-down
    # Check DAG
    a_r = defaultdict(set); n_r = set()
    for a, b in rem_nn: a_r[a].add(b); n_r.add(a); n_r.add(b)
    ic = [0]; sk = []; lk = {}; ix2 = {}; on2 = set(); sc2 = []
    def scc_check(v):
        ix2[v] = ic[0]; lk[v] = ic[0]; ic[0] += 1
        sk.append(v); on2.add(v)
        for w in a_r.get(v, set()):
            if w not in ix2: scc_check(w); lk[v] = min(lk[v], lk[w])
            elif w in on2: lk[v] = min(lk[v], ix2[w])
        if lk[v] == ix2[v]:
            s = []
            while True:
                w = sk.pop(); on2.discard(w); s.append(w)
                if w == v: break
            if len(s) > 1: sc2.append(s)
    for v in n_r:
        if v not in ix2: scc_check(v)

    total_edges = len(efa)
    is_dag = len(sc2) == 0
    print(f"n={nn}: {total_edges} 6-tuple edges, always_down={len(ad_nn)}, remaining={len(rem_nn)}, "
          f"mixed={len(mx_nn)}, DAG={is_dag}, "
          f"edges match n=9: {rem_nn == remaining_edges}")
    if not is_dag:
        for s in sc2:
            print(f"  SCC: {sorted(s)}")

print("\nDONE")
