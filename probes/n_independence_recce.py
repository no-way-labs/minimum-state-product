#!/usr/bin/env python3
"""
Recce: What EXACTLY makes the CΦ 6-tuple edge set n-independent?

The CΦ edge set = {(b1, b2) : ∃ configs c,c' with boundary(c)=b1, boundary(c')=b2,
                    c→c' is a bad step, same FutureFc, same TP, same Φ_full, b1≠b2}

For n-independence, we need: this set is the same for all n ≥ 9.

Key question: WHY does adding more interior positions (n=10 vs n=9) not change which
boundary transitions preserve Φ_full?

Hypothesis: Φ_full at a given boundary state b is:
  Φ_full(b) = fc_boundary(b) + max_interior_excess(TP)
where max_interior_excess depends only on TP (not on b or n).

If true, then Φ_full(b1) = Φ_full(b2) iff fc_boundary(b1) = fc_boundary(b2).
And transitions preserving Φ_full = transitions preserving fc_boundary.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import build_system
from collections import defaultdict, deque

def analyze_phi_full_structure(nn):
    """Analyze the structure of Φ_full at the boundary level."""
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

    # Compute TP-preserving adjacency
    bad = set(); tpa = {}
    for i in range(N):
        if fcc(idc(i)) > 0: bad.add(i); tpa[i] = []
    for i in bad:
        c = idc(i); t = tpp(c)
        for p in range(nn):
            c2 = mv(c, p); j = cdi(c2)
            if c2 != c and j in bad and tpp(c2) == t: tpa[i].append(j)

    # Compute Φ_full
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

    # For each boundary state b, compute:
    # - min and max Φ_full over all configs with boundary b
    # - min and max fc over all configs with boundary b
    # - the "Φ_full excess" = Φ_full - fc for each config
    boundary_phi = defaultdict(list)  # b -> list of (phi_full, fc, tp)
    for i in bad:
        c = idc(i)
        b = b6(c)
        boundary_phi[b].append((pf[i], fcc(c), tpp(c)))

    return boundary_phi

# Check hypothesis: is Φ_full - fc constant across configs with same boundary + TP?
print("=" * 70)
print("HYPOTHESIS CHECK: Φ_full - fc depends only on TP, not boundary")
print("=" * 70)

for nn in [9, 10, 11]:
    bp = analyze_phi_full_structure(nn)

    # Group by (boundary, TP) → set of (phi_full, fc) values
    bt_groups = defaultdict(set)
    for b, entries in bp.items():
        for phi, fc, tp in entries:
            bt_groups[(b, tp)].add((phi, fc))

    # Check: within (boundary, TP), is phi_full - fc constant?
    constant_excess = True
    variable_excess_count = 0
    for (b, tp), values in bt_groups.items():
        excesses = set(phi - fc for phi, fc in values)
        if len(excesses) > 1:
            constant_excess = False
            variable_excess_count += 1

    # Also check: within same TP, is the excess the same across different boundaries?
    tp_excesses = defaultdict(set)
    for (b, tp), values in bt_groups.items():
        for phi, fc in values:
            tp_excesses[tp].add(phi - fc)

    excess_per_tp_constant = all(len(v) == 1 for v in tp_excesses.values())

    print(f"\nn={nn}:")
    print(f"  Φ_full - fc constant within (boundary, TP): {constant_excess}")
    print(f"  Variable excess groups: {variable_excess_count}/{len(bt_groups)}")
    print(f"  Φ_full - fc constant within TP (across boundaries): {excess_per_tp_constant}")

    if not excess_per_tp_constant:
        # How many TP groups have variable excess?
        var_tp = sum(1 for v in tp_excesses.values() if len(v) > 1)
        print(f"  TP groups with variable Φ_full-fc: {var_tp}/{len(tp_excesses)}")
        # Show an example
        for tp, exc in sorted(tp_excesses.items()):
            if len(exc) > 1:
                print(f"    TP={tp}: excesses={sorted(exc)}")
                break

# Check alternative hypothesis: Φ_full depends only on 6-tuple (not interior)
print("\n" + "=" * 70)
print("HYPOTHESIS CHECK: Φ_full depends only on 6-tuple boundary")
print("=" * 70)

for nn in [9, 10]:
    bp = analyze_phi_full_structure(nn)

    # Within same boundary, how many distinct Φ_full values?
    boundary_phi_distinct = {}
    for b, entries in bp.items():
        phi_vals = set(phi for phi, fc, tp in entries)
        boundary_phi_distinct[b] = len(phi_vals)

    max_distinct = max(boundary_phi_distinct.values())
    multi_phi = sum(1 for v in boundary_phi_distinct.values() if v > 1)

    print(f"\nn={nn}: max distinct Φ_full per boundary: {max_distinct}")
    print(f"  Boundaries with multiple Φ_full: {multi_phi}/{len(boundary_phi_distinct)}")

# Key check: CΦ boundary edges = boundary edges preserving fc?
print("\n" + "=" * 70)
print("KEY CHECK: CΦ edges vs fc-preserving edges")
print("=" * 70)

for nn in [9, 10, 11]:
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

    # CΦ boundary edges
    cphi = set()
    # TP-preserving + fc-preserving boundary edges
    tp_fc = set()
    # TP-preserving + boundary-fc-preserving boundary edges
    def boundary_fc(c):
        """Frontier count among boundary positions only."""
        # Frontiers: (c[0],c[1]), (c[1],c[2]), (c[n-3],c[n-2]), (c[n-2],c[n-1]), (c[n-1],c[0])
        # Also (c[2],c[3]) and (c[n-4],c[n-3]) — these involve interior!
        # Pure boundary frontiers (both positions in 6-tuple):
        return sum(1 for j in [0, 1, nn-2, nn-1] if c[j] != c[(j+1)%nn])

    tp_bfc = set()

    for i in bad:
        for j in tpa[i]:
            if ff[j] == ff[i] and pf[j] == pf[i]:
                c, c2 = idc(i), idc(j)
                b1, b2 = b6(c), b6(c2)
                if b1 != b2:
                    cphi.add((b1, b2))
            c, c2 = idc(i), idc(j)
            b1, b2 = b6(c), b6(c2)
            if b1 != b2 and fcc(c) == fcc(c2):
                tp_fc.add((b1, b2))
            if b1 != b2 and boundary_fc(c) == boundary_fc(c2):
                tp_bfc.add((b1, b2))

    print(f"\nn={nn}:")
    print(f"  CΦ edges: {len(cphi)}")
    print(f"  TP + fc-preserving edges: {len(tp_fc)}")
    print(f"  TP + boundary-fc-preserving edges: {len(tp_bfc)}")
    print(f"  CΦ ⊆ TP+fc: {cphi.issubset(tp_fc)}")
    print(f"  CΦ = TP+fc: {cphi == tp_fc}")

print("\nDONE")
