#!/usr/bin/env python3
"""
WHY fc change is determined by (b6_src, b6_dst) for boundary moves.

The puzzle: firing position 2 changes c[2], which affects pair (2,3).
The fc change at (2,3) depends on c[3] (interior). How can the total
fc change be boundary-determined?

Answer: For TP-preserving moves, the T_mid copy-neighbor behavior
constrains the relationship between c[2] and c[3].

Let's verify: for position 2 fires, what is the relationship between
(c[2], c[3]) values that actually occur in TP-preserving transitions?
"""

import sys
from itertools import product as cartesian
from collections import defaultdict

sys.stdout.reconfigure(line_buffering=True)

T_low = {
    (0,0,0):0, (0,0,1):0, (0,0,2):0,
    (0,1,0):0, (0,1,1):0, (0,1,2):0,
    (1,0,0):0, (1,0,1):0, (1,0,2):0,
    (1,1,0):0, (1,1,1):1, (1,1,2):0,
}
T_high = {
    (0,0,0):0, (0,0,1):0, (0,1,0):0, (0,1,1):0,
    (0,2,0):0, (0,2,1):0, (1,0,0):0, (1,0,1):1,
    (1,1,0):0, (1,1,1):1, (1,2,0):0, (1,2,1):1,
}
T_mid = {
    (0,0,0):0, (0,0,1):0, (0,0,2):0,
    (0,1,0):1, (0,1,1):0, (0,1,2):0,
    (0,2,0):2, (0,2,1):0, (0,2,2):0,
    (1,0,0):0, (1,0,1):1, (1,0,2):1,
    (1,1,0):1, (1,1,1):1, (1,1,2):1,
    (1,2,0):2, (1,2,1):1, (1,2,2):1,
    (2,0,0):0, (2,0,1):0, (2,0,2):2,
    (2,1,0):1, (2,1,1):0, (2,1,2):2,
    (2,2,0):2, (2,2,1):0, (2,2,2):2,
}
T_lo_adj = {
    (0,0,0):0, (0,0,1):0, (0,0,2):0,
    (0,1,0):1, (0,1,1):0, (0,1,2):0,
    (1,0,0):0, (1,0,1):1, (1,0,2):1,
    (1,1,0):1, (1,1,1):1, (1,1,2):1,
    (2,0,0):0, (2,0,1):0, (2,0,2):2,
    (2,1,0):1, (2,1,1):0, (2,1,2):2,
}
T_hi_adj = {
    (0,0,0):0, (0,0,1):0, (0,1,0):1, (0,1,1):0,
    (0,2,0):2, (0,2,1):0, (1,0,0):0, (1,0,1):1,
    (1,1,0):1, (1,1,1):1, (1,2,0):2, (1,2,1):1,
    (2,0,0):0, (2,0,1):0, (2,1,0):1, (2,1,1):0,
    (2,2,0):2, (2,2,1):0,
}

def cup2_output(n, c, i):
    S, L, R = c[i], c[(i-1)%n], c[(i+1)%n]
    if i == 0: return T_low.get((S, L, R), S)
    elif i == n-1: return T_high.get((S, L, R), S)
    elif i == 1: return T_lo_adj.get((S, L, R), S)
    elif i == n-2: return T_hi_adj.get((S, L, R), S)
    else: return T_mid.get((S, L, R), S)

def is_privileged(n, c, i):
    return cup2_output(n, c, i) != c[i]

def fire(n, c, i):
    lst = list(c)
    lst[i] = cup2_output(n, c, i)
    return tuple(lst)

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j+1)%n])

def modulus(i, n):
    return 2 if i == 0 or i == n-1 else 3

def all_configs(n):
    return list(cartesian(*(range(modulus(i, n)) for i in range(n))))

def tp_invariant(c, n):
    e2, i21, ew = 0, 0, 0
    for j in range(2, n-2):
        if c[j] == 2:
            r = c[(j+1)%n]
            if r == 0 or r == 1:
                e2 += 1; ew += j
                if r == 1: i21 += 1
    return (e2, i21, ew)

def build_good_set(n):
    configs = all_configs(n)
    return {c for c in configs if sum(1 for i in range(n) if is_privileged(n, c, i)) == 1}

def boundary_6(c, n):
    return c[:3] + c[n-3:]

def main():
    print("=" * 70)
    print("WHY fc CHANGE IS BOUNDARY-DETERMINED")
    print("=" * 70)

    n = 11
    configs = all_configs(n)
    good = build_good_set(n)
    bad_set = set(c for c in configs if c not in good)

    # Position 2: T_mid(c[1], c[2], c[3]) is the output
    # T_mid fires when output != c[2], i.e., T_mid(c[1], c[2], c[3]) != c[2]
    # The new c[2]' = T_mid(c[1], c[2], c[3])
    #
    # fc pairs affected: (1,2) and (2,3)
    # (1,2): old = c[1]!=c[2], new = c[1]!=c[2]'
    # (2,3): old = c[2]!=c[3], new = c[2]'!=c[3]
    #
    # For TP preservation at position 2 (which has j=2 in the exp2 range):
    # exp2 at j=2: c[j]=2 and c[j+1] in {0,1} => c[2]=2 and c[3] in {0,1}
    # After firing: c[2]' and c[3] unchanged (c[3] is interior)
    # TP change at j=2: (c[2]=2 and c[3]<=1) vs (c[2]'=2 and c[3]<=1)
    # So TP preservation requires: c[2]=2 implies c[2]'=2 (or c[3]>1), etc.
    #
    # Actually, the key is MUCH simpler: T_mid at position 2 is T_lo_adj,
    # not T_mid! Position 2 uses T_mid only for positions 3..n-4.
    # Wait, position 2:
    #   i=0 -> T_low, i=1 -> T_lo_adj, i=n-2 -> T_hi_adj, i=n-1 -> T_high
    #   i=2..n-3 -> T_mid
    # So position 2 uses T_mid. Its context: L=c[1], S=c[2], R=c[3].
    #
    # For position 2 to fire: T_mid(c[1], c[2], c[3]) != c[2]
    # After: c[2]' = T_mid(c[1], c[2], c[3])
    #
    # Q: does the fc change at (2,3) depend on c[3]?
    # A: Yes, it depends on whether c[2]!=c[3] changes to c[2]'!=c[3].
    #    Since c[2]' = T_mid(c[1], c[2], c[3]), both c[2]' and the comparison
    #    depend on c[3].
    #
    # BUT: the (b6_src, b6_dst) pair determines c[2] and c[2]' (since both are
    # in the boundary 6-tuple). The question is whether
    #    (c[2]!=c[3]) -> (c[2]'!=c[3])
    # has a fixed delta regardless of c[3].
    #
    # Let's check which (c[1], c[2], c[3]) triples lead to TP-preserving fires.

    print(f"\n  Position 2 fires at n={n}:")
    print(f"  Context: (L, S, R) = (c[1], c[2], c[3])")
    print()

    triples = set()
    for c in bad_set:
        if not is_privileged(n, c, 2): continue
        d = fire(n, c, 2)
        if d not in bad_set: continue
        if tp_invariant(d, n) != tp_invariant(c, n): continue

        # cup2_output: S=c[2], L=c[1], R=c[3], lookup T_mid[(S,L,R)]
        S, L, R = c[2], c[1], c[3]
        S_new = d[2]
        old_23 = 1 if c[2] != c[3] else 0
        new_23 = 1 if S_new != c[3] else 0
        delta_23 = new_23 - old_23
        triples.add((L, S, R, S_new, delta_23))

    print(f"  {len(triples)} distinct (c[1], c[2], c[3], c[2]', delta_23) triples:")
    for L, S, R, S_new, d23 in sorted(triples):
        expected = T_mid.get((S, L, R), S)
        assert expected == S_new, f"Mismatch: T_mid({S},{L},{R})={expected} != {S_new}"
        print(f"    c[1]={L}, c[2]={S} -> c[2]'={S_new}, c[3]={R}, "
              f"delta_pair23={d23:+d}")

    # Key insight: for each (c[1], c[2]) pair (which is in b6),
    # does the delta_pair23 depend on c[3]?
    print(f"\n  Grouping by (c[1], c[2]) — boundary-known values:")
    by_LS = defaultdict(set)
    by_LS_detail = defaultdict(list)
    for L, S, R, S_new, d23 in triples:
        by_LS[(L, S)].add(d23)
        by_LS_detail[(L, S)].append((R, S_new, d23))

    for (L, S), deltas in sorted(by_LS.items()):
        details = sorted(by_LS_detail[(L, S)])
        print(f"    c[1]={L}, c[2]={S}: delta_23 values = {sorted(deltas)}")
        for R, S_new, d23 in details:
            print(f"      c[3]={R}: c[2]={S}->c[2]'={S_new}, delta_23={d23:+d}")

    # Check: is the delta_23 always the same regardless of c[3]?
    varying = {k: v for k, v in by_LS.items() if len(v) > 1}
    if varying:
        print(f"\n  VARYING: {len(varying)} (c[1],c[2]) pairs have c[3]-dependent delta_23")
        print(f"  This means fc change at pair (2,3) DOES depend on c[3]")
        print(f"  But total fc change is still b6-determined. Why?")
        print(f"  Because the variation in delta_23 must be compensated elsewhere.")
        print()
        # Check: for the varying cases, does the total fc change still agree?
        # Actually, the ONLY pairs affected by firing position 2 are (1,2) and (2,3).
        # If delta_23 varies by c[3], then total fc change = delta_12 + delta_23 varies.
        # But we PROVED above that total fc change is b6-determined (0 violations).
        # Contradiction? No: the TP-preservation filter eliminates some (c[1],c[2],c[3])
        # combinations. Let me check whether the varying triples actually pass TP.
        print(f"  Checking: do the varying (c[1],c[2]) cases actually have multiple c[3]")
        print(f"  values that pass both (privileged AND TP-preserving AND bad-to-bad)?")
        for (L, S) in sorted(varying):
            details = sorted(by_LS_detail[(L, S)])
            print(f"    c[1]={L}, c[2]={S}:")
            for R, S_new, d23 in details:
                print(f"      c[3]={R}: c[2]'={S_new}, delta_23={d23:+d}")
    else:
        print(f"\n  NO VARIATION: delta_23 is always determined by (c[1], c[2]) alone")
        print(f"  Even though c[2]' = T_mid(c[1], c[2], c[3]) depends on c[3],")
        print(f"  the pair (2,3) contribution: (c[2]!=c[3]) vs (c[2]'!=c[3])")
        print(f"  has the same delta regardless of c[3].")

    # Same analysis for position n-3
    print(f"\n{'─'*60}")
    print(f"  Position {n-3} fires at n={n}:")
    print(f"  Context: (L, S, R) = (c[{n-4}], c[{n-3}], c[{n-2}])")

    triples2 = set()
    for c in bad_set:
        p = n - 3
        if not is_privileged(n, c, p): continue
        d = fire(n, c, p)
        if d not in bad_set: continue
        if tp_invariant(d, n) != tp_invariant(c, n): continue

        # cup2_output: S=c[n-3], L=c[n-4], R=c[n-2], lookup T_mid[(S,L,R)]
        S_val, L_val, R_val = c[n-3], c[n-4], c[n-2]
        S_new = d[n-3]
        # Pair (n-4, n-3) depends on interior c[n-4]
        old_pair = 1 if c[n-4] != c[n-3] else 0
        new_pair = 1 if c[n-4] != S_new else 0
        delta_pair = new_pair - old_pair
        triples2.add((L_val, S_val, R_val, S_new, delta_pair))

    by_SR = defaultdict(set)
    by_SR_detail = defaultdict(list)
    for L_val, S_val, R_val, S_new, dp in triples2:
        by_SR[(S_val, R_val)].add(dp)
        by_SR_detail[(S_val, R_val)].append((L_val, S_new, dp))

    print(f"  Grouping by (c[{n-3}], c[{n-2}]) — boundary-known values:")
    for (S, R), deltas in sorted(by_SR.items()):
        details = sorted(by_SR_detail[(S, R)])
        print(f"    c[{n-3}]={S}, c[{n-2}]={R}: delta values = {sorted(deltas)}")
        for L, S_new, dp in details:
            print(f"      c[{n-4}]={L}: c[{n-3}]={S}->{S_new}, delta={dp:+d}")

    varying2 = {k: v for k, v in by_SR.items() if len(v) > 1}
    if varying2:
        print(f"\n  VARYING: {len(varying2)} pairs")
    else:
        print(f"\n  NO VARIATION: delta determined by (c[{n-3}], c[{n-2}]) alone")

if __name__ == "__main__":
    main()
