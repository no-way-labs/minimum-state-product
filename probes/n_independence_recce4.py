#!/usr/bin/env python3
"""
KEY CHECK: Do the 53 mixed Φ_full edges all have condensation_rank dropping?

If YES: the n-independence question for the 53 mixed edges is IRRELEVANT.
The proof only needs:
  1. 564 always-preserved + 53 mixed → all in condensation-rank-dropping set (native_decide)
  2. 3 SCC edges: analytical proof
  3. 481 never-preserved: show these CAN'T be CΦ

For (3): prove ∀ n ≥ 9, these 481 transitions always decrease Φ_full.
This is a UNIVERSAL claim, much easier than the existential claim for mixed edges.

The universal claim follows if: max boundary-reachable fc from destination < from source.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import build_system
from collections import defaultdict, deque

nn = 9; ms, fs = build_system(nn); N = 1
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

# Classify edges by Φ_full behavior
edge_phi = defaultdict(set)
cphi_edges = set()
for i in bad:
    for j in tpa[i]:
        c, c2 = idc(i), idc(j)
        b1, b2 = b6(c), b6(c2)
        if b1 != b2:
            edge_phi[(b1, b2)].add(pf[j] - pf[i])
            if ff[j] == ff[i] and pf[j] == pf[i]:
                cphi_edges.add((b1, b2))

always_zero = {e for e, d in edge_phi.items() if d == {0}}
mixed_phi = {e for e, d in edge_phi.items() if 0 in d and min(d) < 0}
never_zero = {e for e, d in edge_phi.items() if 0 not in d}

# Compute condensation rank (from explore_fix6.py)
adj6 = defaultdict(set); nodes6 = set()
for a, b in cphi_edges: adj6[a].add(b); nodes6.add(a); nodes6.add(b)

idx_c = [0]; stk = []; ll = {}; ix = {}; ons = set()
scc_list = []; scc_id = {}
def sc(v):
    ix[v] = idx_c[0]; ll[v] = idx_c[0]; idx_c[0] += 1
    stk.append(v); ons.add(v)
    for w in adj6.get(v, set()):
        if w not in ix: sc(w); ll[v] = min(ll[v], ll[w])
        elif w in ons: ll[v] = min(ll[v], ix[w])
    if ll[v] == ix[v]:
        s = []
        while True:
            w = stk.pop(); ons.discard(w); s.append(w)
            if w == v: break
        scc_list.append(set(s))
        for w in s: scc_id[w] = len(scc_list) - 1
sys.setrecursionlimit(10000)
for v in nodes6:
    if v not in ix: sc(v)

cond_adj = defaultdict(set)
for a in nodes6:
    for b in adj6[a]:
        sa, sb = scc_id[a], scc_id[b]
        if sa != sb: cond_adj[sa].add(sb)
cond_nodes = set(range(len(scc_list)))
out_deg = {c: len(cond_adj.get(c, set())) for c in cond_nodes}
sinks = [c for c in cond_nodes if out_deg.get(c, 0) == 0]
cond_rank = {c: 0 for c in sinks}
cond_radj = defaultdict(list)
for c in cond_nodes:
    for s in cond_adj.get(c, set()): cond_radj[s].append(c)
q = deque(sinks)
while q:
    s = q.popleft()
    for c in cond_radj.get(s, []):
        new_r = cond_rank[s] + 1
        if c not in cond_rank or new_r > cond_rank[c]:
            cond_rank[c] = new_r; q.append(c)

cr = [0] * 324
for v in nodes6: cr[v] = cond_rank[scc_id[v]]
SCC = {239, 245, 251}

print("=" * 70)
print(f"Classification: {len(always_zero)} always-zero, {len(mixed_phi)} mixed, {len(never_zero)} never-zero")
print(f"CΦ edges: {len(cphi_edges)} = {len(always_zero)} + {len(mixed_phi)} = {len(always_zero) + len(mixed_phi)}")
print("=" * 70)

# Check: do ALL 53 mixed edges have condensation rank dropping?
mixed_cond_drop = 0
mixed_scc = 0
mixed_no_drop = 0
for (a, b) in mixed_phi:
    if cr[b] < cr[a]:
        mixed_cond_drop += 1
    elif a in SCC and b in SCC:
        mixed_scc += 1
    else:
        mixed_no_drop += 1

print(f"\n53 mixed edges: {mixed_cond_drop} cond-drop, {mixed_scc} SCC, {mixed_no_drop} no-drop")

# Check: do ALL 564 always-zero edges have condensation rank dropping or SCC?
az_cond_drop = 0
az_scc = 0
az_no_drop = 0
for (a, b) in always_zero:
    if cr[b] < cr[a]:
        az_cond_drop += 1
    elif a in SCC and b in SCC:
        az_scc += 1
    else:
        az_no_drop += 1

print(f"564 always-zero edges: {az_cond_drop} cond-drop, {az_scc} SCC, {az_no_drop} no-drop")

# Check the 481 never-zero edges: are they really always negative?
assert all(all(d < 0 for d in v) for e, v in edge_phi.items() if e in never_zero)
print(f"\n481 never-zero: ALL diffs < 0 ✓")

# For the 481: check if the negative diff is determined by 6-tuple alone
# (i.e., does the diff depend on TP or interior?)
never_zero_same_diff = sum(1 for e in never_zero if len(edge_phi[e]) == 1)
never_zero_multi_diff = sum(1 for e in never_zero if len(edge_phi[e]) > 1)
print(f"481 never-zero: {never_zero_same_diff} single diff, {never_zero_multi_diff} multiple diffs")

# The key insight:
print("\n" + "=" * 70)
print("PROOF ARCHITECTURE (n-independent, zero sorry)")
print("=" * 70)
print("""
For cphi_bridge at general n ≥ 9:

STEP 1: Extract mover at boundary position (from CΦ step hypothesis).
STEP 2: Compute new 6-tuple from tables + hidden value. [analytical, n-independent]
STEP 3: Show the 6-tuple transition is TP-preserving. [native_decide on tables]
STEP 4: Show: either condensation_rank drops, OR transition is SCC edge,
         OR Φ_full STRICTLY decreases. [three-way split]

  Case A: condensation_rank drops. → 4-component lex drops. DONE.
  Case B: SCC edge. → analytical fc/scc_sub_rank proof. DONE.
  Case C: Φ_full strictly decreases. → contradicts CΦ (constant Φ_full). DONE.

For Case C: "Φ_full strictly decreases on 481 specific TP-preserving transitions."
  - This is a UNIVERSAL claim: ∀ configs, Φ_full drops on these transitions.
  - Follows from: Φ_full is non-increasing (proved), AND these 481 transitions
    are NOT in the CΦ edge set.
  - By contrapositive: if Φ_full is preserved, the transition is in the CΦ set.
  - CΦ set has 617 edges (the 564+53). The 481 are the complement.

  THE N-INDEPENDENCE QUESTION: Is it true for all n that these 481 transitions
  always decrease Φ_full?

  Approach: show analytically that these 481 transitions reduce the
  "max boundary-reachable boundary-fc" — a boundary-level quantity
  that is n-independent.
""")

# Compute max boundary-reachable boundary-fc for each 6-tuple state
# "boundary-reachable" = reachable via TP-preserving boundary transitions
# "boundary-fc" = fc counting only boundary frontiers

def decode_b6(s):
    cN1 = s % 2; s //= 2; cN2 = s % 3; s //= 3; cN3 = s % 3; s //= 3
    c2 = s % 3; s //= 3; c1 = s % 3; s //= 3; c0 = s
    return (c0, c1, c2, cN3, cN2, cN1)

def boundary_fc_6(s):
    c0, c1, c2, cN3, cN2, cN1 = decode_b6(s)
    # Frontiers involving only boundary positions:
    # (c0,c1), (c1,c2), (cN3,cN2), (cN2,cN1), (cN1,c0)
    return sum([c0!=c1, c1!=c2, cN3!=cN2, cN2!=cN1, cN1!=c0])

# TP-preserving boundary transitions (already have all_edges from 1098)
all_tp_edges = set(edge_phi.keys())

# Compute max reachable boundary-fc from each 6-tuple state via TP-pres transitions
adj_tp = defaultdict(set)
for a, b in all_tp_edges:
    adj_tp[a].add(b)

# BFS/fixpoint: max boundary-fc reachable from each state
max_bfc = {}
for s in range(324):
    max_bfc[s] = boundary_fc_6(s)

changed = True
while changed:
    changed = False
    for s in range(324):
        for t in adj_tp.get(s, set()):
            if max_bfc[t] > max_bfc[s]:
                # Wait, this is wrong. The reachable set from s includes states reachable via the transition graph.
                # We need: max boundary_fc over all states reachable from s.
                pass
    break  # Will redo properly

# Proper computation: max boundary-fc reachable from each state
# via the TP-preserving boundary transition graph
max_reach_bfc = {s: boundary_fc_6(s) for s in range(324)}
rev_tp = defaultdict(set)
for a, b in all_tp_edges:
    rev_tp[b].add(a)

changed = True
while changed:
    changed = False
    for t in range(324):
        for s in rev_tp.get(t, set()):
            if max_reach_bfc[t] > max_reach_bfc[s]:
                max_reach_bfc[s] = max_reach_bfc[t]
                changed = True

print("\n" + "=" * 70)
print("Max boundary-reachable boundary-fc analysis")
print("=" * 70)

# For the 481 never-zero edges: does max_reach_bfc(dst) < max_reach_bfc(src)?
nz_bfc_drop = 0
nz_bfc_same = 0
nz_bfc_rise = 0
for (a, b) in never_zero:
    if max_reach_bfc[b] < max_reach_bfc[a]:
        nz_bfc_drop += 1
    elif max_reach_bfc[b] == max_reach_bfc[a]:
        nz_bfc_same += 1
    else:
        nz_bfc_rise += 1

print(f"481 never-zero: max_reach_bfc drops={nz_bfc_drop}, same={nz_bfc_same}, rises={nz_bfc_rise}")

# For the 617 CΦ edges: does max_reach_bfc stay same?
cphi_bfc_drop = 0
cphi_bfc_same = 0
for (a, b) in cphi_edges:
    if max_reach_bfc[b] < max_reach_bfc[a]:
        cphi_bfc_drop += 1
    else:
        cphi_bfc_same += 1

print(f"617 CΦ: max_reach_bfc same={cphi_bfc_same}, drops={cphi_bfc_drop}")

# KEY: does max_reach_bfc perfectly separate CΦ from non-CΦ?
print(f"\nPerfect separation: {nz_bfc_drop == 481 and cphi_bfc_same == 617}")

print("\nDONE")
