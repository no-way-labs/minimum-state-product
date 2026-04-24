#!/usr/bin/env python3
"""
Zero-sorry approach: prove cphi_boundary_lex_drop DIRECTLY by native_decide
on (source_6tuple, mover_position, hidden_value) triples.

For each triple where TP is preserved AND boundary changes:
→ condensation rank drops OR it's a specific SCC case (handled analytically)

This avoids needing cphi_bridge entirely — we go directly from
"CΦ step with boundary change" to "4-component lex drops".
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top
from collections import defaultdict, deque

def decode_b6(s):
    cN1 = s % 2; s //= 2
    cN2 = s % 3; s //= 3
    cN3 = s % 3; s //= 3
    c2 = s % 3; s //= 3
    c1 = s % 3; s //= 3
    c0 = s
    return (c0, c1, c2, cN3, cN2, cN1)

def encode_b6(c0, c1, c2, cN3, cN2, cN1):
    return ((((c0*3+c1)*3+c2)*3+cN3)*3+cN2)*2+cN1

# Precompute all boundary transitions with TP check
# Returns: list of (src, dst, position, hidden_val, tp_preserved)
n = 9  # representative, but transitions are n-independent for n>=9

transitions = []  # (src_6tuple, dst_6tuple, pos_type, hidden_val, tp_preserved)

for src in range(324):
    c0, c1, c2, cN3, cN2, cN1 = decode_b6(src)

    # Position 0 (T_bot): context = (cN1, c0, c1), no hidden
    out = T_bot[(cN1, c0, c1)]
    if out != c0:
        dst = encode_b6(out, c1, c2, cN3, cN2, cN1)
        # TP: position 0 not in [2, n-2), no TP change
        transitions.append((src, dst, 0, 0, True))

    # Position 1 (T_low): context = (c0, c1, c2), no hidden
    out = T_low[(c0, c1, c2)]
    if out != c1:
        dst = encode_b6(c0, out, c2, cN3, cN2, cN1)
        # TP: position 1 not in [2, n-2), no TP change
        transitions.append((src, dst, 1, 0, True))

    # Position 2 (T_mid): context = (c1, c2, c3), c3 is hidden
    for c3 in range(3):
        out = T_mid[(c1, c2, c3)]
        if out != c2:
            dst = encode_b6(c0, c1, out, cN3, cN2, cN1)
            # TP at j=2: c[2] changes. Check Exp2 at j=2: c[j]=2 and c[j+1]∈{0,1}
            old_e2 = (c2 == 2 and c3 in (0, 1))
            new_e2 = (out == 2 and c3 in (0, 1))
            old_i21 = (c2 == 2 and c3 == 1)
            new_i21 = (out == 2 and c3 == 1)
            tp_ok = (old_e2 == new_e2 and old_i21 == new_i21)
            transitions.append((src, dst, 2, c3, tp_ok))

    # Position n-3 (T_mid): context = (c[n-4], cN3, cN2), c[n-4] is hidden
    for cN4 in range(3):
        out = T_mid[(cN4, cN3, cN2)]
        if out != cN3:
            dst = encode_b6(c0, c1, c2, out, cN2, cN1)
            # TP at j=n-4 (=5 for n=9): c[n-4]=cN4, c[n-3] changes
            old_e2_nm4 = (cN4 == 2 and cN3 in (0, 1))
            new_e2_nm4 = (cN4 == 2 and out in (0, 1))
            old_i21_nm4 = (cN4 == 2 and cN3 == 1)
            new_i21_nm4 = (cN4 == 2 and out == 1)
            # TP at j=n-3 (=6): c[n-3] changes, c[n-2]=cN2
            old_e2_nm3 = (cN3 == 2 and cN2 in (0, 1))
            new_e2_nm3 = (out == 2 and cN2 in (0, 1))
            old_i21_nm3 = (cN3 == 2 and cN2 == 1)
            new_i21_nm3 = (out == 2 and cN2 == 1)
            de2 = (new_e2_nm4 - old_e2_nm4) + (new_e2_nm3 - old_e2_nm3)
            di21 = (new_i21_nm4 - old_i21_nm4) + (new_i21_nm3 - old_i21_nm3)
            dw = 0
            if old_e2_nm4 != new_e2_nm4:
                dw += (5) * (1 if new_e2_nm4 else -1)  # n-4=5 for n=9, but weight = position
            if old_e2_nm3 != new_e2_nm3:
                dw += (6) * (1 if new_e2_nm3 else -1)  # n-3=6 for n=9
            # For n-independence: position of n-4 and n-3 change with n, but
            # we only care about SIGN of de2, di21, dw — not values
            # Actually for Exp2Weight, the actual weight changes. But for TP preservation,
            # we need de2=0, di21=0, dw=0. The specific weight values depend on n.
            # For n-independence: dw depends on j values (n-4, n-3). These differ by n.
            # BUT: if de2=0 and di21=0, then no Exp2 positions changed, so dw=0 regardless.
            # The only case where dw matters is if Exp2 positions changed (de2≠0 or we need same count but diff weight)
            # Actually: de2=0 means count unchanged. di21=0 means int21 unchanged. But weight can change
            # if one Exp2 position is removed and another added at a different j.
            # For position n-3 move: only j=n-4 and j=n-3 are affected. Both are single positions.
            # If BOTH changed (one added, one removed at DIFFERENT j values): de2=0 but dw≠0.
            # However, old_e2_nm4→new_e2_nm4 and old_e2_nm3→new_e2_nm3 are two independent changes.
            # If one goes 0→1 and the other 1→0: de2=0 but dw=(new_j - old_j). n-dependent!
            #
            # But actually: for the SCC edges, I showed c[n-4]∈{0,1} (not 2), so the Exp2 at n-4
            # doesn't trigger. So for the SCC case, tp is preserved without weight issues.
            #
            # For the general case: I need to check BOTH count and weight.
            # Weight check is n-dependent. So I can't do a single native_decide.
            # BUT: the only case where weight matters is when one Exp2 is added and one removed.
            # In that case, de2=0 but dw≠0 (generically). So tp_ok should be False.
            # The issue is: dw depends on n. For n=9: dw = 5*(new_e2_nm4-old_e2_nm4) + 6*(new_e2_nm3-old_e2_nm3).
            # For general n: dw = (n-4)*(new_e2_nm4-old_e2_nm4) + (n-3)*(new_e2_nm3-old_e2_nm3).
            #
            # If de2=0: either both are unchanged (dw=0), or one added and one removed.
            # If one added and one removed: dw = (n-4)*(1) + (n-3)*(-1) = n-4-n+3 = -1 (for nm4 added, nm3 removed)
            #                           or = (n-4)*(-1) + (n-3)*(1) = -n+4+n-3 = 1 (for nm4 removed, nm3 added)
            # So dw ∈ {-1, 1} when one is added and one removed. ALWAYS nonzero. So tp_ok = False.
            #
            # Great! So the weight check is actually n-independent in the binary sense:
            # dw=0 iff (both unchanged or both changed in same direction).

            # Recompute tp_ok properly:
            if de2 == 0 and di21 == 0:
                # Check if weight changed: only if Exp2 positions swapped
                if old_e2_nm4 == new_e2_nm4 and old_e2_nm3 == new_e2_nm3:
                    tp_ok = True  # Nothing changed
                else:
                    # One added, one removed → dw ≠ 0
                    tp_ok = False
            else:
                tp_ok = False

            transitions.append((src, dst, 3, cN4, tp_ok))  # pos_type 3 = n-3

    # Position n-2 (T_high): context = (cN3, cN2, cN1), no hidden
    out = T_high[(cN3, cN2, cN1)]
    if out != cN2:
        dst = encode_b6(c0, c1, c2, cN3, out, cN1)
        # TP at j=n-3 (=6): c[n-3]=cN3, c[n-2] changes
        old_e2_nm3 = (cN3 == 2 and cN2 in (0, 1))
        new_e2_nm3 = (cN3 == 2 and out in (0, 1))
        old_i21_nm3 = (cN3 == 2 and cN2 == 1)
        new_i21_nm3 = (cN3 == 2 and out == 1)
        # j=n-2 (=7) is NOT in [2, 7) for n=9. But for general n, n-2 is in [2, n-2)
        # iff n-2 >= 2 (always true for n>=4) AND n-2 < n-2 (FALSE).
        # So j=n-2 is NOT in the range. Only j=n-3 matters.
        tp_ok = (old_e2_nm3 == new_e2_nm3 and old_i21_nm3 == new_i21_nm3)
        transitions.append((src, dst, 4, 0, tp_ok))  # pos_type 4 = n-2

    # Position n-1 (T_top): context = (cN2, cN1, c0), no hidden
    out = T_top[(cN2, cN1, c0)]
    if out != cN1:
        dst = encode_b6(c0, c1, c2, cN3, cN2, out)
        # TP: position n-1 not in [2, n-2), no TP change
        transitions.append((src, dst, 5, 0, tp_ok))

# Now compute condensation rank (from the CΦ 617-edge graph)
# Reuse from explore_fix6.py
from cup2_theorem import build_system
ms, fs = build_system(n)
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
def fc(c): return sum(1 for j in range(n) if c[j] != c[(j+1)%n])
def tp(c):
    e = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
    i21 = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n]==1)
    w = sum(j for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
    return (e, i21, w)
def boundary6(c): return ((((c[0]*3+c[1])*3+c[2])*3+c[n-3])*3+c[n-2])*2+c[n-1]

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

# Condensation
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
sr = [0] * 324
sr[245] = 2; sr[251] = 1

# Now check: for every TP-preserving boundary-changing transition,
# either condensation rank drops, OR scc_sub_rank drops, OR it's edge (239,245)
print("=" * 60)
print("ZERO-SORRY CHECK")
print("=" * 60)

tp_changing = [(s, d, p, h) for s, d, p, h, tp in transitions if tp and s != d]
print(f"Total TP-preserving boundary-changing transitions: {len(tp_changing)}")

# Check each
unhandled = []
for src, dst, pos, hidden in tp_changing:
    cr_src, cr_dst = cr[src], cr[dst]
    sr_src, sr_dst = sr[src], sr[dst]
    if cr_dst < cr_src:
        continue  # condensation drops ✓
    elif cr_dst == cr_src and sr_dst < sr_src:
        continue  # scc sub-rank drops ✓
    elif src == 239 and dst == 245:
        continue  # SCC fc edge, handled analytically ✓
    else:
        unhandled.append((src, dst, pos, hidden))

print(f"Unhandled transitions: {len(unhandled)}")
for src, dst, pos, hidden in unhandled[:20]:
    in_cphi = (src, dst) in cphi_edges
    c0, c1, c2, cN3, cN2, cN1 = decode_b6(src)
    d0, d1, d2, dN3, dN2, dN1 = decode_b6(dst)
    print(f"  {src}→{dst} pos={pos} hidden={hidden} in_CΦ={in_cphi}")
    print(f"    src=({c0},{c1},{c2},{cN3},{cN2},{cN1}) dst=({d0},{d1},{d2},{dN3},{dN2},{dN1})")
    print(f"    cond_rank: {cr[src]}→{cr[dst]}, scc_sub: {sr[src]}→{sr[dst]}")

if not unhandled:
    print("\n✓ ALL TP-preserving boundary-changing transitions are handled!")
    print("  → cphi_bridge can be closed by native_decide on (source, position, hidden_val) triples")
    print("  → No sorry needed!")
else:
    print(f"\n✗ {len(unhandled)} unhandled transitions (NOT in CΦ 617 edges)")
    # Check if all unhandled are NOT in CΦ
    all_non_cphi = all((s, d) not in cphi_edges for s, d, p, h in unhandled)
    print(f"  All unhandled are non-CΦ: {all_non_cphi}")
    if all_non_cphi:
        print("  These transitions never occur within CΦ.")
        print("  Need CΦ constraint to rule them out → cannot use pure native_decide.")

print("\nDONE")
