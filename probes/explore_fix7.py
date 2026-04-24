#!/usr/bin/env python3
"""
Compute ALL possible TP-preserving boundary transitions (superset of CΦ).
If the condensation approach works on this larger set, cphi_bridge becomes trivial.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import build_system, T_bot, T_low, T_mid, T_high, T_top
from collections import defaultdict, deque

n = 9; ms, fs = build_system(n)

def boundary6(c): return ((((c[0]*3+c[1])*3+c[2])*3+c[n-3])*3+c[n-2])*2+c[n-1]

def decode_b6(s):
    """Decode 6-tuple state into (c0, c1, c2, cN3, cN2, cN1)."""
    cN1 = s % 2; s //= 2
    cN2 = s % 3; s //= 3
    cN3 = s % 3; s //= 3
    c2 = s % 3; s //= 3
    c1 = s % 3; s //= 3
    c0 = s
    return (c0, c1, c2, cN3, cN2, cN1)

def tp_local_change(pos, old_c, new_c, n):
    """Check TP change from a single position change.
    TP counts positions j in [2, n-2) where c[j]=2 and c[j+1] in {0,1}.
    Returns (delta_e2, delta_i21, delta_w) or None if TP changes."""
    # old_c and new_c are full configs differing only at pos
    delta_e2 = 0; delta_i21 = 0; delta_w = 0
    # Check positions j that could be affected: j = pos or j = pos-1
    for j in range(max(2, pos-1), min(n-2, pos+1)):
        # Before
        if old_c[j] == 2 and old_c[(j+1)%n] in (0, 1):
            delta_e2 -= 1
            if old_c[(j+1)%n] == 1: delta_i21 -= 1
            delta_w -= j
        # After
        if new_c[j] == 2 and new_c[(j+1)%n] in (0, 1):
            delta_e2 += 1
            if new_c[(j+1)%n] == 1: delta_i21 += 1
            delta_w += j
    return (delta_e2, delta_i21, delta_w)

# Compute ALL possible boundary transitions for each boundary position.
# For positions 0, 1, n-2, n-1: all neighbor values are in the 6-tuple.
# For position 2: left=c[1] (6-tuple), self=c[2] (6-tuple), right=c[3] (NOT 6-tuple, varies 0..2)
# For position n-3: left=c[n-4] (NOT 6-tuple), self=c[n-3] (6-tuple), right=c[n-2] (6-tuple)

all_edges = set()  # TP-preserving boundary transitions
all_edges_no_tp = set()  # ALL boundary transitions (no TP check)

for s in range(324):
    c0, c1, c2, cN3, cN2, cN1 = decode_b6(s)

    # Move at position 0: P_bot table, context (c[n-1], c[0], c[1])
    # c[n-1]=cN1 (6-tuple), c[0]=c0 (6-tuple), c[1]=c1 (6-tuple)
    out = T_bot[(cN1, c0, c1)]
    if out != c0:
        new_c0 = out
        t = ((((new_c0*3+c1)*3+c2)*3+cN3)*3+cN2)*2+cN1
        all_edges_no_tp.add((s, t))
        # TP check: position 0 is not in [2, n-2), so no TP change
        all_edges.add((s, t))

    # Move at position 1: P_low table, context (c[0], c[1], c[2])
    out = T_low[(c0, c1, c2)]
    if out != c1:
        new_c1 = out
        t = ((((c0*3+new_c1)*3+c2)*3+cN3)*3+cN2)*2+cN1
        all_edges_no_tp.add((s, t))
        # TP check: position 1 is not in [2, n-2), but position 1's change affects
        # the check at position 1 (if in range) — but position 1 < 2, so no direct TP
        # However, the neighbor at position 2 checks c[2]=? and c[1+1]=c[2].
        # Position 0 checks... wait, TP range is j in [2, n-2).
        # Position 1 changing might affect TP at j=1 (not in range) or j=0 (not in range).
        # But c[2] and c[1] are in TP check for j=1 only if j=1 >= 2, which is false.
        # Wait, j ranges from 2 to n-3. Position 1's change doesn't affect any TP position.
        # Actually, TP at j=2 checks c[2]=2 and c[3]∈{0,1}. Changing c[1] doesn't affect c[2] or c[3].
        # But wait, I need to double-check: does changing c[1] affect TP at ANY j?
        # TP at j checks c[j] and c[j+1]. For c[1] to appear, we need j=0 (c[0],c[1]) or j=1 (c[1],c[2]).
        # But j starts at 2. So c[1] doesn't appear in TP. No TP change.
        all_edges.add((s, t))

    # Move at position 2: T_mid table (for n>=6, position 2 uses T_mid if n>5)
    # Actually for n=9, position 2 uses T_mid (positions 2..n-3 all use T_mid)
    # Context: (c[1], c[2], c[3]) where c[3] varies
    for c3 in range(3):
        out = T_mid[(c1, c2, c3)]
        if out != c2:
            new_c2 = out
            t = ((((c0*3+c1)*3+new_c2)*3+cN3)*3+cN2)*2+cN1
            all_edges_no_tp.add((s, t))
            # TP check: position 2 might be in TP range [2, n-2) = [2, 7).
            # j=2: old c[2] and c[3]. New c[2] and c[3] (c[3] unchanged).
            # j=1: not in range.
            # So check: old TP at j=2 vs new TP at j=2.
            old_exp2_2 = (c2 == 2 and c3 in (0, 1))
            new_exp2_2 = (new_c2 == 2 and c3 in (0, 1))
            old_i21_2 = (c2 == 2 and c3 == 1)
            new_i21_2 = (new_c2 == 2 and c3 == 1)
            # Also j=1 checks c[1] and c[2]. j=1 < 2, not in range.
            if old_exp2_2 == new_exp2_2 and old_i21_2 == new_i21_2:
                # TP preserved (weight also preserved since j=2 is same)
                all_edges.add((s, t))

    # Move at position n-3 (=6): T_mid table, context (c[n-4], c[n-3], c[n-2])
    # c[n-4] varies (0..2)
    for cN4 in range(3):
        out = T_mid[(cN4, cN3, cN2)]
        if out != cN3:
            new_cN3 = out
            t = ((((c0*3+c1)*3+c2)*3+new_cN3)*3+cN2)*2+cN1
            all_edges_no_tp.add((s, t))
            # TP check: j=n-4 and j=n-3 are in [2, n-2)=[2,7).
            # n-4=5, n-3=6. Both in [2,7).
            # j=n-4: checks c[n-4] and c[n-3]. c[n-4]=cN4, c[n-3] changes.
            old_exp2_nm4 = (cN4 == 2 and cN3 in (0, 1))
            new_exp2_nm4 = (cN4 == 2 and new_cN3 in (0, 1))
            old_i21_nm4 = (cN4 == 2 and cN3 == 1)
            new_i21_nm4 = (cN4 == 2 and new_cN3 == 1)
            # j=n-3: checks c[n-3] and c[n-2].
            old_exp2_nm3 = (cN3 == 2 and cN2 in (0, 1))
            new_exp2_nm3 = (new_cN3 == 2 and cN2 in (0, 1))
            old_i21_nm3 = (cN3 == 2 and cN2 == 1)
            new_i21_nm3 = (new_cN3 == 2 and cN2 == 1)
            # All TP changes
            de2 = (new_exp2_nm4 - old_exp2_nm4) + (new_exp2_nm3 - old_exp2_nm3)
            di21 = (new_i21_nm4 - old_i21_nm4) + (new_i21_nm3 - old_i21_nm3)
            dw = 0
            if old_exp2_nm4 != new_exp2_nm4: dw += (n-4) * (1 if new_exp2_nm4 else -1)
            if old_exp2_nm3 != new_exp2_nm3: dw += (n-3) * (1 if new_exp2_nm3 else -1)
            if de2 == 0 and di21 == 0 and dw == 0:
                all_edges.add((s, t))

    # Move at position n-2 (=7): T_high table, context (c[n-3], c[n-2], c[n-1])
    out = T_high[(cN3, cN2, cN1)]
    if out != cN2:
        new_cN2 = out
        t = ((((c0*3+c1)*3+c2)*3+cN3)*3+new_cN2)*2+cN1
        all_edges_no_tp.add((s, t))
        # TP check: j=n-3 and j=n-2.
        # j=n-3 (=6): checks c[n-3] and c[n-2]. c[n-2] changes.
        old_exp2_nm3 = (cN3 == 2 and cN2 in (0, 1))
        new_exp2_nm3 = (cN3 == 2 and new_cN2 in (0, 1))
        old_i21_nm3 = (cN3 == 2 and cN2 == 1)
        new_i21_nm3 = (cN3 == 2 and new_cN2 == 1)
        # j=n-2 (=7): checks c[n-2] and c[n-1]. n-2=7, range is [2,7). 7 NOT in [2,7).
        # So only j=n-3 matters.
        de2 = new_exp2_nm3 - old_exp2_nm3
        di21 = new_i21_nm3 - old_i21_nm3
        dw = 0
        if old_exp2_nm3 != new_exp2_nm3: dw = (n-3) * (1 if new_exp2_nm3 else -1)
        if de2 == 0 and di21 == 0 and dw == 0:
            all_edges.add((s, t))

    # Move at position n-1 (=8): T_top table, context (c[n-2], c[n-1], c[0])
    out = T_top[(cN2, cN1, c0)]
    if out != cN1:
        new_cN1 = out
        t = ((((c0*3+c1)*3+c2)*3+cN3)*3+cN2)*2+new_cN1
        all_edges_no_tp.add((s, t))
        # TP check: j=n-2 (=7). 7 NOT in [2,7). And j=n-1 (=8) also not in range.
        # No TP change.
        all_edges.add((s, t))

# Remove self-loops
all_edges = {(a, b) for a, b in all_edges if a != b}
all_edges_no_tp = {(a, b) for a, b in all_edges_no_tp if a != b}

print(f"All boundary transitions (no TP): {len(all_edges_no_tp)}")
print(f"TP-preserving boundary transitions: {len(all_edges)}")

# Load the CΦ 617-edge set for comparison
from collections import defaultdict
def fc(c): return sum(1 for j in range(n) if c[j] != c[(j+1)%n])
def tp(c):
    e = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
    i21 = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n]==1)
    w = sum(j for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
    return (e, i21, w)

N = 1
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

# CΦ edges
bad_set = set(); tp_adj = {}
for i in range(N):
    if fc(idx_to_config(i)) > 0: bad_set.add(i); tp_adj[i] = []
for i in bad_set:
    c = idx_to_config(i); t = tp(c)
    for p in range(n):
        c2 = move(c, p); j = config_to_idx(c2)
        if c2 != c and j in bad_set and tp(c2) == t: tp_adj[i].append(j)

phi_full = {i: fc(idx_to_config(i)) for i in bad_set}
tp_rev = {i: [] for i in bad_set}
for i in bad_set:
    for j in tp_adj[i]: tp_rev[j].append(i)
changed = True
while changed:
    changed = False
    for j in bad_set:
        for i in tp_rev[j]:
            if phi_full[j] > phi_full[i]: phi_full[i] = phi_full[j]; changed = True

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
            if future_fc[j] > future_fc[i]: future_fc[i] = future_fc[j]; changed = True

cphi_edges = set()
for i in bad_set:
    for j in tp_adj[i]:
        if future_fc[j] == future_fc[i] and phi_full[j] == phi_full[i]:
            c, c2 = idx_to_config(i), idx_to_config(j)
            b1, b2 = boundary6(c), boundary6(c2)
            if b1 != b2: cphi_edges.add((b1, b2))

print(f"CΦ boundary edges (n=9): {len(cphi_edges)}")
print(f"CΦ ⊆ TP-preserving: {cphi_edges.issubset(all_edges)}")

extra_tp = all_edges - cphi_edges
print(f"Extra TP-preserving edges not in CΦ: {len(extra_tp)}")

# Check if the TP-preserving set is a DAG with condensation approach
adj_tp = defaultdict(set); nodes_tp = set()
for a, b in all_edges: adj_tp[a].add(b); nodes_tp.add(a); nodes_tp.add(b)

# Tarjan's SCC
idx_c = [0]; stk = []; ll = {}; ix = {}; ons = set(); sccs = []
def sc(v):
    ix[v] = idx_c[0]; ll[v] = idx_c[0]; idx_c[0] += 1
    stk.append(v); ons.add(v)
    for w in adj_tp.get(v, set()):
        if w not in ix: sc(w); ll[v] = min(ll[v], ll[w])
        elif w in ons: ll[v] = min(ll[v], ix[w])
    if ll[v] == ix[v]:
        s = []
        while True:
            w = stk.pop(); ons.discard(w); s.append(w)
            if w == v: break
        if len(s) > 1: sccs.append(s)

sys.setrecursionlimit(10000)
for v in nodes_tp:
    if v not in ix: sc(v)

print(f"\nTP-preserving graph SCCs: {len(sccs)}")
for scc in sccs:
    print(f"  SCC of size {len(scc)}: {sorted(scc)}")
    # Check edges within SCC
    scc_set = set(scc)
    for a in scc:
        for b in adj_tp[a]:
            if b in scc_set:
                in_cphi = (a, b) in cphi_edges
                print(f"    {a}→{b} (in CΦ: {in_cphi})")

print("\nDONE")
