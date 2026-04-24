#!/usr/bin/env python3
"""
Verify the deep interior cancellation argument.

Claim: For a boundary transition c→c' (preserving TP):
  Φ_full(c') - Φ_full(c) depends only on (6-tuple, c[3], c[n-4]).

This means: configs with same (6-tuple, c[3], c[n-4]) have the same Φ_full diff
on the same boundary transition. If true, n-independence follows from
8-tuple n-independence (already verified).

Also: verify the "padding" argument — adding interior positions preserves
CΦ edge membership.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import build_system
from collections import defaultdict

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
    def b8_key(c): return (b6(c), c[3], c[nn-4])

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

    return bad, tpa, pf, idc, cdi, fcc, tpp, b6, b8_key, mv

print("=" * 70)
print("TEST: Φ_full diff determined by (8-tuple of src, 8-tuple of dst, TP)")
print("=" * 70)

for nn in [9, 10, 11]:
    bad, tpa, pf, idc, cdi, fcc, tpp, b6, b8, mv = full_analysis(nn)

    # For each TP-preserving boundary-changing transition,
    # group by (b8_src, b8_dst, TP) and check if Φ_full diff is constant
    groups = defaultdict(set)
    for i in bad:
        for j in tpa[i]:
            c, c2 = idc(i), idc(j)
            if b6(c) != b6(c2):
                key = (b8(c), b8(c2), tpp(c))
                diff = pf[j] - pf[i]
                groups[key].add(diff)

    multi = sum(1 for v in groups.values() if len(v) > 1)
    print(f"\nn={nn}: {len(groups)} (8-tuple-src, 8-tuple-dst, TP) groups")
    print(f"  Groups with multiple Φ_full diffs: {multi}")
    if multi > 0:
        for k, v in sorted(groups.items()):
            if len(v) > 1:
                print(f"    {k}: diffs={sorted(v)}")
                break  # Just show first

print("\n" + "=" * 70)
print("TEST: Φ_full diff determined by (b8_src, b8_dst) ALONE (no TP)?")
print("=" * 70)

for nn in [9, 10, 11]:
    bad, tpa, pf, idc, cdi, fcc, tpp, b6, b8, mv = full_analysis(nn)

    groups = defaultdict(set)
    for i in bad:
        for j in tpa[i]:
            c, c2 = idc(i), idc(j)
            if b6(c) != b6(c2):
                key = (b8(c), b8(c2))
                diff = pf[j] - pf[i]
                groups[key].add(diff)

    multi = sum(1 for v in groups.values() if len(v) > 1)
    print(f"\nn={nn}: {len(groups)} (b8_src, b8_dst) groups")
    print(f"  Groups with multiple Φ_full diffs: {multi}")

print("\n" + "=" * 70)
print("TEST: For the 53 mixed 6-tuple edges, does the 8-tuple resolve?")
print("=" * 70)

for nn in [9]:
    bad, tpa, pf, idc, cdi, fcc, tpp, b6, b8, mv = full_analysis(nn)

    # Find mixed 6-tuple edges
    edge_diffs_6 = defaultdict(set)
    edge_diffs_8 = defaultdict(set)
    for i in bad:
        for j in tpa[i]:
            c, c2 = idc(i), idc(j)
            if b6(c) != b6(c2):
                diff = pf[j] - pf[i]
                edge_diffs_6[(b6(c), b6(c2))].add(diff)
                edge_diffs_8[(b8(c), b8(c2))].add(diff)

    mixed_6 = [(e, d) for e, d in edge_diffs_6.items() if 0 in d and min(d) < 0]
    print(f"\nn={nn}: {len(mixed_6)} mixed 6-tuple edges")

    resolved_count = 0
    for (b1, b2), diffs_6 in mixed_6:
        # Find 8-tuple sub-edges
        sub = [(k, v) for k, v in edge_diffs_8.items()
               if k[0][0] == b1 and k[1][0] == b2]
        all_single = all(len(v) == 1 for k, v in sub)
        if all_single:
            resolved_count += 1
        else:
            print(f"  UNRESOLVED: 6-tuple ({b1},{b2}), diffs={sorted(diffs_6)}")
            for k, v in sub:
                if len(v) > 1:
                    print(f"    8-tuple {k}: diffs={sorted(v)}")
                    break

    print(f"  Resolved by 8-tuple: {resolved_count}/{len(mixed_6)}")

print("\n" + "=" * 70)
print("CONCLUSION: Can we prove n-independence?")
print("=" * 70)

# The key question: is Φ_full diff determined by (b8_src, b8_dst, TP)?
# If yes with 0 multi-diff groups → n-independence follows from 8-tuple n-independence
# (since 8-tuple transitions are n-independent for n ≥ 9)

print("""
If Φ_full diff is determined by (b8_src, b8_dst, TP):
  → CΦ edge membership = {6-tuple edge : ∃ (c3,cn4,TP) s.t. diff=0}
  → This is determined by 8-tuple transition existence, which is n-independent
  → Therefore CΦ 6-tuple edge set is n-independent ✓

Proof in Lean would be:
  1. cphi_bridge: CΦ → boundary transition (extract mover, compute output)
  2. Show boundary transition is in 1098-edge TP-preserving set (native_decide on tables)
  3. Show: for each TP-preserving transition, Φ_full diff is determined by (b8, TP)
  4. Show: for 617 edges, ∃ (c3,cn4) giving diff=0 (witnessed at n=9, n-independent)
  5. Show: for 481 edges, ∀ (c3,cn4), diff<0 (verified at n=9, n-independent)

  Step 3 is the key analytical claim.
  Steps 4-5 are finite checks.
""")

print("DONE")
