#!/usr/bin/env python3
"""Explore fixes for the 6-tuple DAG cycle in CΦ.

Option A: Add NonnegMeasure layer — check if CΦ + constant NonnegMeasure → 6-tuple is DAG
Option C: Find the cycle, check if fc handles it
Option E: Find a DIFFERENT rank on the 617-edge graph (not DAG-rank, but a lex combo)
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
def psi(c):
    """Simplified psi: sum of frontier weights."""
    total = 0
    for j in range(n):
        a, b = c[j], c[(j+1)%n]
        if a != b:
            ft = (b - a) % 3  # 1 or 2
            if ft == 1:
                total += 2*(n-1-j) + 1  # w1
            else:
                total += 2*j + 1  # w2
    return total

# Build infrastructure
all_configs = [idx_to_config(i) for i in range(N)]
bad_set = set()
tp_adj = {}
for i in range(N):
    c = all_configs[i]
    if fc(c) > 0:
        bad_set.add(i)
        tp_adj[i] = []
for i in bad_set:
    c = all_configs[i]; t = tp(c)
    for p in range(n):
        c2 = move(c, p)
        if c2 == c: continue
        j = config_to_idx(c2)
        if j in bad_set and tp(c2) == t:
            tp_adj[i].append(j)

# Compute Φ_full
phi_full = {i: fc(all_configs[i]) for i in bad_set}
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

# Compute FutureFc
future_fc = {i: fc(all_configs[i]) for i in bad_set}
all_adj = {i: [] for i in bad_set}
for i in bad_set:
    c = all_configs[i]
    for p in range(n):
        c2 = move(c, p)
        if c2 == c: continue
        j = config_to_idx(c2)
        if j in bad_set: all_adj[i].append(j)
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

print("=" * 60)
print("ANALYSIS OF CΦ 6-TUPLE CYCLE")
print("=" * 60)

# Collect CΦ edges with full info
cphi_full_edges = []  # (src_idx, dst_idx, mover_pos)
for i in bad_set:
    c = all_configs[i]
    for j in tp_adj[i]:
        c2 = all_configs[j]
        if future_fc[j] == future_fc[i] and phi_full[j] == phi_full[i]:
            cphi_full_edges.append((i, j))

# 6-tuple edges with fc/psi info
cphi_6tuple_edges = set()
edge_fc_info = defaultdict(list)  # (b_src, b_dst) -> list of (fc_src, fc_dst, psi_src, psi_dst)
for i, j in cphi_full_edges:
    c, c2 = all_configs[i], all_configs[j]
    b1, b2 = boundary6(c), boundary6(c2)
    if b1 != b2:
        cphi_6tuple_edges.add((b1, b2))
        edge_fc_info[(b1, b2)].append((fc(c), fc(c2), psi(c), psi(c2)))

print(f"CΦ 6-tuple boundary-changing edges: {len(cphi_6tuple_edges)}")

# Find cycles in the 6-tuple graph
adj6 = defaultdict(set)
nodes6 = set()
for a, b in cphi_6tuple_edges:
    adj6[a].add(b); nodes6.add(a); nodes6.add(b)

# Find ALL SCCs (Tarjan's)
index_counter = [0]
stack = []
lowlink = {}
index = {}
on_stack = set()
sccs = []

def strongconnect(v):
    index[v] = index_counter[0]
    lowlink[v] = index_counter[0]
    index_counter[0] += 1
    stack.append(v)
    on_stack.add(v)
    for w in adj6.get(v, set()):
        if w not in index:
            strongconnect(w)
            lowlink[v] = min(lowlink[v], lowlink[w])
        elif w in on_stack:
            lowlink[v] = min(lowlink[v], index[w])
    if lowlink[v] == index[v]:
        scc = []
        while True:
            w = stack.pop()
            on_stack.discard(w)
            scc.append(w)
            if w == v: break
        if len(scc) > 1:
            sccs.append(scc)

sys.setrecursionlimit(10000)
for v in nodes6:
    if v not in index:
        strongconnect(v)

print(f"\nNon-trivial SCCs in 6-tuple graph: {len(sccs)}")
for scc in sccs:
    print(f"  SCC of size {len(scc)}: {sorted(scc)}")
    # Print edges within SCC
    scc_set = set(scc)
    for a in scc:
        for b in adj6[a]:
            if b in scc_set:
                fc_infos = edge_fc_info.get((a, b), [])
                fc_dirs = set()
                for fi, fj, pi, pj in fc_infos:
                    if fi < fj: fc_dirs.add("fc_up")
                    elif fi > fj: fc_dirs.add("fc_down")
                    else: fc_dirs.add("fc_same")
                print(f"    {a} → {b}: {len(fc_infos)} instances, fc: {fc_dirs}")

print("\n" + "=" * 60)
print("OPTION A: CΦ + CONSTANT NONNEG MEASURE → 6-TUPLE")
print("=" * 60)

# First check: is NonnegMeasure non-increasing within CΦ?
nonneg_increase = 0
nonneg_same = 0
nonneg_decrease = 0
for i, j in cphi_full_edges:
    c, c2 = all_configs[i], all_configs[j]
    nm_src = (n - fc(c), psi(c))
    nm_dst = (n - fc(c2), psi(c2))
    if nm_src < nm_dst:
        nonneg_increase += 1
    elif nm_src == nm_dst:
        nonneg_same += 1
    else:
        nonneg_decrease += 1

print(f"NonnegMeasure on CΦ edges: increase={nonneg_increase}, same={nonneg_same}, decrease={nonneg_decrease}")

# CΦ + constant NonnegMeasure 6-tuple edges
cnm_6tuple = set()
for i, j in cphi_full_edges:
    c, c2 = all_configs[i], all_configs[j]
    nm_src = (n - fc(c), psi(c))
    nm_dst = (n - fc(c2), psi(c2))
    if nm_src == nm_dst:
        b1, b2 = boundary6(c), boundary6(c2)
        if b1 != b2:
            cnm_6tuple.add((b1, b2))

print(f"CΦ + constant NonnegMeasure 6-tuple edges: {len(cnm_6tuple)}")

# Check if DAG
adj_cnm = defaultdict(set)
nodes_cnm = set()
for a, b in cnm_6tuple:
    adj_cnm[a].add(b); nodes_cnm.add(a); nodes_cnm.add(b)

# Tarjan's for cycles
index_counter2 = [0]
stack2 = []
lowlink2 = {}
index2 = {}
on_stack2 = set()
sccs2 = []

def strongconnect2(v):
    index2[v] = index_counter2[0]
    lowlink2[v] = index_counter2[0]
    index_counter2[0] += 1
    stack2.append(v)
    on_stack2.add(v)
    for w in adj_cnm.get(v, set()):
        if w not in index2:
            strongconnect2(w)
            lowlink2[v] = min(lowlink2[v], lowlink2[w])
        elif w in on_stack2:
            lowlink2[v] = min(lowlink2[v], index2[w])
    if lowlink2[v] == index2[v]:
        scc = []
        while True:
            w = stack2.pop()
            on_stack2.discard(w)
            scc.append(w)
            if w == v: break
        if len(scc) > 1:
            sccs2.append(scc)

for v in nodes_cnm:
    if v not in index2:
        strongconnect2(v)

if len(sccs2) == 0:
    print("→ CΦ + constant NonnegMeasure 6-tuple IS A DAG!")
    # Compute rank
    out_deg = {c: len(adj_cnm.get(c, set())) for c in nodes_cnm}
    sinks = [c for c in nodes_cnm if out_deg.get(c, 0) == 0]
    rank = {c: 0 for c in sinks}
    radj = defaultdict(list)
    for c in nodes_cnm:
        for s in adj_cnm.get(c, set()):
            if s in nodes_cnm: radj[s].append(c)
    q = deque(sinks)
    while q:
        s = q.popleft()
        for c in radj.get(s, []):
            new_r = rank[s] + 1
            if c not in rank or new_r > rank[c]:
                rank[c] = new_r; q.append(c)
    max_rank = max(rank.values())
    print(f"  Max rank: {max_rank}")
    print(f"  Nodes: {len(nodes_cnm)}")
else:
    print(f"→ STILL HAS {len(sccs2)} SCCs!")
    for scc in sccs2:
        print(f"  SCC of size {len(scc)}: {sorted(scc)}")

print("\n" + "=" * 60)
print("OPTION A': CΦ + CONSTANT FC → 6-TUPLE")
print("=" * 60)

# Maybe just constant fc is enough (simpler than NonnegMeasure)
cfc_6tuple = set()
for i, j in cphi_full_edges:
    c, c2 = all_configs[i], all_configs[j]
    if fc(c) == fc(c2):
        b1, b2 = boundary6(c), boundary6(c2)
        if b1 != b2:
            cfc_6tuple.add((b1, b2))

print(f"CΦ + constant fc 6-tuple edges: {len(cfc_6tuple)}")

adj_cfc = defaultdict(set)
nodes_cfc = set()
for a, b in cfc_6tuple:
    adj_cfc[a].add(b); nodes_cfc.add(a); nodes_cfc.add(b)

# Check DAG
index_counter3 = [0]
stack3 = []
lowlink3 = {}
index3 = {}
on_stack3 = set()
sccs3 = []

def strongconnect3(v):
    index3[v] = index_counter3[0]
    lowlink3[v] = index_counter3[0]
    index_counter3[0] += 1
    stack3.append(v)
    on_stack3.add(v)
    for w in adj_cfc.get(v, set()):
        if w not in index3:
            strongconnect3(w)
            lowlink3[v] = min(lowlink3[v], lowlink3[w])
        elif w in on_stack3:
            lowlink3[v] = min(lowlink3[v], index3[w])
    if lowlink3[v] == index3[v]:
        scc = []
        while True:
            w = stack3.pop()
            on_stack3.discard(w)
            scc.append(w)
            if w == v: break
        if len(scc) > 1:
            sccs3.append(scc)

for v in nodes_cfc:
    if v not in index3:
        strongconnect3(v)

if len(sccs3) == 0:
    print("→ CΦ + constant fc 6-tuple IS A DAG!")
    out_deg = {c: len(adj_cfc.get(c, set())) for c in nodes_cfc}
    sinks = [c for c in nodes_cfc if out_deg.get(c, 0) == 0]
    rank = {c: 0 for c in sinks}
    radj = defaultdict(list)
    for c in nodes_cfc:
        for s in adj_cfc.get(c, set()):
            if s in nodes_cfc: radj[s].append(c)
    q = deque(sinks)
    while q:
        s = q.popleft()
        for c in radj.get(s, []):
            new_r = rank[s] + 1
            if c not in rank or new_r > rank[c]:
                rank[c] = new_r; q.append(c)
    max_rank = max(rank.values())
    print(f"  Max rank: {max_rank}")
    print(f"  Nodes: {len(nodes_cfc)}")
else:
    print(f"→ STILL HAS {len(sccs3)} SCCs!")

print("\n" + "=" * 60)
print("OPTION C: FC-AUGMENTED RANK ON 617-EDGE GRAPH")
print("=" * 60)

# For each 6-tuple edge, what's the range of fc changes?
for a, b in sorted(cphi_6tuple_edges):
    infos = edge_fc_info[(a, b)]
    fc_deltas = set()
    for fi, fj, pi, pj in infos:
        fc_deltas.add(fj - fi)
    if len(fc_deltas) > 1 or (len(fc_deltas) == 1 and 0 not in fc_deltas):
        # Interesting: fc not always same
        pass

# Check: on cycle edges, does fc ALWAYS decrease?
print("\nCycle edge fc analysis:")
for scc in sccs:
    scc_set = set(scc)
    for a in scc:
        for b in adj6[a]:
            if b in scc_set:
                infos = edge_fc_info[(a, b)]
                fc_deltas = sorted(set(fj - fi for fi, fj, pi, pj in infos))
                print(f"  {a} → {b}: fc deltas = {fc_deltas}")

# Can we split 617 edges into: fc-decreasing + DAG-on-rest?
fc_always_decrease = set()
fc_can_same_or_increase = set()
for edge in cphi_6tuple_edges:
    a, b = edge
    infos = edge_fc_info[edge]
    all_decrease = all(fj < fi for fi, fj, pi, pj in infos)
    if all_decrease:
        fc_always_decrease.add(edge)
    else:
        fc_can_same_or_increase.add(edge)

print(f"\nEdges where fc always decreases: {len(fc_always_decrease)}")
print(f"Edges where fc can stay same or increase: {len(fc_can_same_or_increase)}")

# Check if fc_can_same_or_increase subgraph is a DAG
adj_rest = defaultdict(set)
nodes_rest = set()
for a, b in fc_can_same_or_increase:
    adj_rest[a].add(b); nodes_rest.add(a); nodes_rest.add(b)

index_counter4 = [0]
stack4 = []
lowlink4 = {}
index4 = {}
on_stack4 = set()
sccs4 = []

def strongconnect4(v):
    index4[v] = index_counter4[0]
    lowlink4[v] = index_counter4[0]
    index_counter4[0] += 1
    stack4.append(v)
    on_stack4.add(v)
    for w in adj_rest.get(v, set()):
        if w not in index4:
            strongconnect4(w)
            lowlink4[v] = min(lowlink4[v], lowlink4[w])
        elif w in on_stack4:
            lowlink4[v] = min(lowlink4[v], index4[w])
    if lowlink4[v] == index4[v]:
        scc = []
        while True:
            w = stack4.pop()
            on_stack4.discard(w)
            scc.append(w)
            if w == v: break
        if len(scc) > 1:
            sccs4.append(scc)

for v in nodes_rest:
    if v not in index4:
        strongconnect4(v)

if len(sccs4) == 0:
    print("→ Non-fc-decreasing edges form a DAG!")
    out_deg = {c: len(adj_rest.get(c, set())) for c in nodes_rest}
    sinks = [c for c in nodes_rest if out_deg.get(c, 0) == 0]
    rank = {c: 0 for c in sinks}
    radj = defaultdict(list)
    for c in nodes_rest:
        for s in adj_rest.get(c, set()):
            if s in nodes_rest: radj[s].append(c)
    q = deque(sinks)
    while q:
        s = q.popleft()
        for c in radj.get(s, []):
            new_r = rank[s] + 1
            if c not in rank or new_r > rank[c]:
                rank[c] = new_r; q.append(c)
    max_rank = max(rank.values()) if rank else 0
    print(f"  Max rank: {max_rank}, Nodes: {len(nodes_rest)}")
else:
    print(f"→ Non-fc-decreasing edges STILL have {len(sccs4)} SCCs!")

print("\n" + "=" * 60)
print("OPTION E: CHECK N-INDEPENDENCE AT n=10,11")
print("=" * 60)

for nn in [10, 11]:
    ms2, fs2 = build_system(nn)
    N2 = 1
    for m in ms2: N2 *= m

    def idx_to_config2(idx):
        c = []
        for m in reversed(ms2):
            c.append(idx % m); idx //= m
        return tuple(reversed(c))
    def config_to_idx2(c):
        idx = 0
        for j in range(nn): idx = idx * ms2[j] + c[j]
        return idx
    def move2(c, pos):
        L = c[(pos-1)%nn]; S = c[pos]; R = c[(pos+1)%nn]
        c2 = list(c); c2[pos] = fs2[pos](L, S, R); return tuple(c2)
    def fc2(c): return sum(1 for j in range(nn) if c[j] != c[(j+1)%nn])
    def tp2(c):
        e = sum(1 for j in range(2,nn-2) if c[j]==2 and c[(j+1)%nn] in (0,1))
        i21 = sum(1 for j in range(2,nn-2) if c[j]==2 and c[(j+1)%nn]==1)
        w = sum(j for j in range(2,nn-2) if c[j]==2 and c[(j+1)%nn] in (0,1))
        return (e, i21, w)
    def boundary6_2(c): return ((((c[0]*3+c[1])*3+c[2])*3+c[nn-3])*3+c[nn-2])*2+c[nn-1]

    bad2 = set(); tp_adj2 = {}
    for i in range(N2):
        c = idx_to_config2(i)
        if fc2(c) > 0:
            bad2.add(i); tp_adj2[i] = []
    for i in bad2:
        c = idx_to_config2(i); t = tp2(c)
        for p in range(nn):
            c2 = move2(c, p)
            if c2 == c: continue
            j = config_to_idx2(c2)
            if j in bad2 and tp2(c2) == t:
                tp_adj2[i].append(j)

    pf2 = {i: fc2(idx_to_config2(i)) for i in bad2}
    rev2 = {i: [] for i in bad2}
    for i in bad2:
        for j in tp_adj2[i]: rev2[j].append(i)
    ch = True
    while ch:
        ch = False
        for j in bad2:
            for i in rev2[j]:
                if pf2[j] > pf2[i]:
                    pf2[i] = pf2[j]; ch = True

    ff2 = {i: fc2(idx_to_config2(i)) for i in bad2}
    aa2 = {i: [] for i in bad2}
    for i in bad2:
        c = idx_to_config2(i)
        for p in range(nn):
            c2 = move2(c, p)
            if c2 == c: continue
            j = config_to_idx2(c2)
            if j in bad2: aa2[i].append(j)
    ar2 = {i: [] for i in bad2}
    for i in bad2:
        for j in aa2[i]: ar2[j].append(i)
    ch = True
    while ch:
        ch = False
        for j in bad2:
            for i in ar2[j]:
                if ff2[j] > ff2[i]:
                    ff2[i] = ff2[j]; ch = True

    # CΦ + constant fc boundary-changing 6-tuple edges
    cfc_edges_nn = set()
    cphi_edges_nn = set()
    for i in bad2:
        for j in tp_adj2[i]:
            if ff2[j] == ff2[i] and pf2[j] == pf2[i]:
                c, c2 = idx_to_config2(i), idx_to_config2(j)
                b1, b2 = boundary6_2(c), boundary6_2(c2)
                if b1 != b2:
                    cphi_edges_nn.add((b1, b2))
                    if fc2(c) == fc2(c2):
                        cfc_edges_nn.add((b1, b2))

    print(f"\nn={nn}: CΦ 6-tuple edges = {len(cphi_edges_nn)}, CΦ+fc 6-tuple edges = {len(cfc_edges_nn)}")

print("\nDONE")
