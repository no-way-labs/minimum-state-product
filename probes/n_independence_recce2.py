#!/usr/bin/env python3
"""
Deep recce: WHY is the CΦ 6-tuple edge set n-independent?

Key hypothesis: For a boundary transition c→c', Φ_full(c')-Φ_full(c) is n-independent.
This would follow if the deep interior's max-fc contribution cancels between c and c'.

But c[3] and c[n-4] can be CHANGED by interior TP-preserving moves. So the max fc
over TP-reachable configs involves optimizing over c[3]/c[n-4] values too.

Test: compute Φ_full as decomposition into parts and check what's n-independent.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import build_system
from collections import defaultdict, deque

def full_analysis(nn):
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

    # Extended boundary: (6-tuple, c[3], c[n-4])
    def b8(c): return (b6(c), c[3], c[nn-4])

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

    # For each TP-preserving boundary-changing transition, compute Φ_full difference
    cphi_edges = set()
    phi_diff_by_edge = defaultdict(set)  # (b_src, b_dst) -> set of Φ_full differences
    phi_diff_by_edge_8 = defaultdict(set)  # (b8_src, b8_dst) -> set of Φ_full differences

    for i in bad:
        for j in tpa[i]:
            c, c2 = idc(i), idc(j)
            b1, b2 = b6(c), b6(c2)
            if b1 != b2:
                diff = pf[j] - pf[i]
                phi_diff_by_edge[(b1, b2)].add(diff)
                phi_diff_by_edge_8[(b8(c), b8(c2))].add(diff)
                if ff[j] == ff[i] and pf[j] == pf[i]:
                    cphi_edges.add((b1, b2))

    return cphi_edges, phi_diff_by_edge, phi_diff_by_edge_8

print("=" * 70)
print("CHECK 1: Is Φ_full difference n-independent at 6-tuple level?")
print("=" * 70)

for nn in [9, 10, 11]:
    cphi, pd6, pd8 = full_analysis(nn)
    # For each 6-tuple edge, what are the possible Φ_full diffs?
    multi_diff = sum(1 for v in pd6.values() if len(v) > 1)
    all_zero_or_neg = all(all(d <= 0 for d in v) for v in pd6.values())
    zero_diff_edges = sum(1 for v in pd6.values() if 0 in v)
    only_zero = sum(1 for v in pd6.values() if v == {0})
    has_zero_and_neg = sum(1 for v in pd6.values() if 0 in v and any(d < 0 for d in v))
    print(f"\nn={nn}: {len(pd6)} 6-tuple edges, {len(cphi)} CΦ")
    print(f"  Edges with multiple Φ_full diffs: {multi_diff}")
    print(f"  All diffs ≤ 0: {all_zero_or_neg}")
    print(f"  Edges with 0 in diffs: {zero_diff_edges}")
    print(f"  Edges with ONLY 0: {only_zero}")
    print(f"  Edges with both 0 and negative: {has_zero_and_neg}")

print("\n" + "=" * 70)
print("CHECK 2: Is Φ_full difference determined at 8-tuple level?")
print("(If so, n-independence follows from 8-tuple n-independence)")
print("=" * 70)

for nn in [9, 10, 11]:
    cphi, pd6, pd8 = full_analysis(nn)
    multi_diff_8 = sum(1 for v in pd8.values() if len(v) > 1)
    only_zero_8 = sum(1 for v in pd8.values() if v == {0})
    print(f"\nn={nn}: {len(pd8)} 8-tuple edges")
    print(f"  Edges with multiple Φ_full diffs: {multi_diff_8}")
    print(f"  Edges with ONLY 0 diff: {only_zero_8}")

print("\n" + "=" * 70)
print("CHECK 3: Are the 8-tuple CΦ edges n-independent?")
print("=" * 70)

cphi_8_sets = {}
for nn in [9, 10, 11, 12]:
    cphi, pd6, pd8 = full_analysis(nn)
    # 8-tuple CΦ edges: TP-preserving + Φ_full preserved + boundary changed
    cphi_8 = set()
    for (b8s, b8d), diffs in pd8.items():
        if 0 in diffs and b8s[0] != b8d[0]:  # 6-tuple changed + Φ_full preserved for some instance
            cphi_8.add((b8s, b8d))
    cphi_8_sets[nn] = cphi_8
    print(f"n={nn}: {len(cphi_8)} 8-tuple CΦ edges")

print(f"\nn=10 == n=9: {cphi_8_sets[10] == cphi_8_sets[9]}")
print(f"n=11 == n=9: {cphi_8_sets[11] == cphi_8_sets[9]}")
print(f"n=12 == n=9: {cphi_8_sets[12] == cphi_8_sets[9]}")

print("\n" + "=" * 70)
print("CHECK 4: For 6-tuple edges with mixed diffs (0 and negative),")
print("is the diff determined by the 8-tuple?")
print("=" * 70)

for nn in [9, 10]:
    cphi, pd6, pd8 = full_analysis(nn)
    # 6-tuple edges where diff can be 0 or negative
    mixed_6 = {e: d for e, d in pd6.items() if 0 in d and any(x < 0 for x in d)}
    print(f"\nn={nn}: {len(mixed_6)} mixed 6-tuple edges")
    # For these, check if the 8-tuple resolves the ambiguity
    resolved = 0
    unresolved = 0
    for (b1, b2), diffs_6 in mixed_6.items():
        # Find all 8-tuple edges that project to this 6-tuple edge
        sub_edges = {(k, v) for k, v in pd8.items()
                     if k[0][0] == b1 and k[1][0] == b2}
        # Check if each 8-tuple edge has a unique diff
        all_unique = all(len(v) == 1 for _, v in sub_edges)
        if all_unique:
            resolved += 1
        else:
            unresolved += 1
    print(f"  Resolved by 8-tuple: {resolved}")
    print(f"  Unresolved: {unresolved}")

print("\n" + "=" * 70)
print("CHECK 5: Direct n-independence of CΦ 6-tuple edges")
print("(just reconfirm)")
print("=" * 70)

cphi_6_sets = {}
for nn in [9, 10, 11, 12]:
    cphi, _, _ = full_analysis(nn)
    cphi_6_sets[nn] = cphi
    print(f"n={nn}: {len(cphi)} CΦ 6-tuple edges")

for nn in [10, 11, 12]:
    print(f"n={nn} == n=9: {cphi_6_sets[nn] == cphi_6_sets[9]}")

print("\nDONE")
