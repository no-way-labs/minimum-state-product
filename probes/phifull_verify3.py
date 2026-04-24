#!/usr/bin/env python3
"""
Check: does T_mid (S=2, L=2, R=1) -> 0 ever preserve TP?
This is a deep interior move (not copy-neighbor) that increases fc.
If it preserves TP, our proof has a gap.
"""
from itertools import product as cartesian
from collections import defaultdict

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

# Check: at positions 2 through n-3 using T_mid, when (S=2, L=2, R=1)->0 fires,
# does TP change?
print("="*60)
print("T_mid (2,2,1)->0 TP preservation check")
print("="*60)

# This move fires at position i where c[i]=2, c[i-1]=2, c[i+1]=1.
# After: c'[i]=0.
# TP contribution analysis:
# The TP counts exp2 at j where c[j]=2 and c[j+1] in {0,1}, for j in [2,n-3].
#
# Affected positions in TP:
# j = i-1: c[i-1]=2. Before: c[i]=2, not in {0,1} -> no contribution.
#          After: c'[i]=0, in {0,1} -> YES contribution! (exp2 +1, int21 +0, ew += (i-1))
# j = i: Before: c[i]=2, c[i+1]=1 in {0,1} -> contribution (exp2 +1, int21 +1, ew += i)
#         After: c'[i]=0, not 2 -> no contribution. (exp2 -1, int21 -1, ew -= i)
# Net: exp2 same (0), int21 goes from 1 to 0 (if c[i+1]=1, which it does) vs
#      new int21 from j=i-1: c'[i]=0, is that counted as int21? int21 counts c[j+1]=1.
#      For j=i-1: c[j+1]=c[i] was 2 (not 1), now c'[i]=0 (not 1). So int21 += 0.
#      For j=i: c[j+1]=c[i+1]=1. Before: int21 += 1. After: j=i not counted (c'[i]=0).
#
# So: exp2: +1 from j=i-1, -1 from j=i = net 0
#     int21: +0 from j=i-1, -1 from j=i = net -1 (DECREASE)
#     ew: +(i-1) from j=i-1, -i from j=i = net -1
#
# int21 changes -> TP NOT preserved.

print("Analytical: TP change for T_mid (2,2,1)->0 at position i:")
print("  j=i-1: Before: c[i-1]=2, c[i]=2 (not in {0,1}) -> no exp2.")
print("         After: c[i-1]=2, c'[i]=0 (in {0,1}) -> exp2! int21 += 0 (c'[i]=0, not 1)")
print("  j=i: Before: c[i]=2, c[i+1]=1 (in {0,1}) -> exp2! int21 += 1 (c[i+1]=1)")
print("       After: c'[i]=0, not 2 -> no exp2.")
print("  Net exp2: +1 - 1 = 0")
print("  Net int21: +0 - 1 = -1 (CHANGES)")
print("  Net ew: +(i-1) - i = -1 (CHANGES)")
print("  Therefore TP is NOT preserved.")

# But wait - what about j=i-1 range check? We need i-1 in [2, n-3].
# i is a T_mid position: 2 <= i, i+2 < n, so 2 <= i <= n-3.
# i-1 >= 1. If i=2, then j=i-1=1 which is NOT in [2, n-3]. Let's handle that.
print("\nRange check: j=i-1 must be in [2, n-3] for TP contribution")
print("  If i=2: j=i-1=1, NOT in range. So no new exp2 from j=i-1.")
print("  If i=2: j=i=2 contribution lost: exp2 -1, int21 -1, ew -2")
print("  Net: exp2 -1, int21 -1, ew -2 -> TP strictly drops (not preserved)")
print("  If i >= 3: j=i-1 >= 2, IS in range. Both j=i-1 and j=i contribute.")
print("  As computed: net int21 = -1, not preserved.")

# Verify computationally at n=11
print("\n" + "="*60)
print("Computational verification at n=11")
print("="*60)
n = 11
configs = all_configs(n)
good = build_good_set(n)
bad = [c for c in configs if c not in good]

tp_preserving_fc_up_mid = 0
tp_not_preserving_fc_up_mid = 0
for c in bad:
    for i in range(2, n-2):  # T_mid range
        if c[i] != 2 or c[(i-1)%n] != 2 or c[(i+1)%n] != 1:
            continue  # not the (2,2,1) pattern
        if not is_privileged(n, c, i):
            continue
        d = fire(n, c, i)
        if d not in set(bad):
            continue
        delta_fc = fc(d, n) - fc(c, n)
        if delta_fc <= 0:
            continue
        tp_c = tp_invariant(c, n)
        tp_d = tp_invariant(d, n)
        if tp_c == tp_d:
            tp_preserving_fc_up_mid += 1
            print(f"  TP PRESERVED + FC UP: c={c}, i={i}, d={d}")
        else:
            tp_not_preserving_fc_up_mid += 1

print(f"\nT_mid (2,2,1)->0 fc-increasing moves:")
print(f"  TP preserved: {tp_preserving_fc_up_mid}")
print(f"  TP not preserved: {tp_not_preserving_fc_up_mid}")

# Also check T_mid (2,1,1)->0 which is also not copy-neighbor
print("\n" + "="*60)
print("T_mid (2,1,1)->0 fc change and TP check")
print("="*60)
print("Analytical: (S=2,L=1,R=1)->out=0")
print("  pair(L,S): 1 vs 2 -> 1 vs 0: 1->1, no change")
print("  pair(S,R): 2 vs 1 -> 0 vs 1: 1->1, no change")
print("  delta_fc = 0. Not a problem for fc.")

# Check if existing Lean proof handles this differently
print("\nNote: The Lean proof uses cup2TpPreserving_mid_copyNeighbor_val")
print("which says TP-preserving + privileged at mid position -> copy-neighbor.")
print("So if the (2,2,1)->0 and (2,1,1)->0 cases fire and are TP-preserving,")
print("the Lean theorem says they must be copy-neighbor -- contradiction!")
print("This means the Lean proof already establishes that these non-copy-neighbor")
print("cases never preserve TP. Our analytical argument agrees.")
