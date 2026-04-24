#!/usr/bin/env python3
"""
Verify specific claims in the PhiFull proof:
1. Position n-1 NOT privileged in c when delta(c)=1
2. Position 1 privileged status in c when delta(c)=1
3. After delta-move, which positions are privileged
4. T_mid never increases fc (copy-neighbor check)
"""

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

# Test 1: T_high(1, *, 1) = 1 for all L (position n-1 not privileged when c[0]=1, c[n-1]=1)
print("TEST 1: T_high(1, L, 1) for all L values")
for L in range(3):
    out = T_high[(1, L, 1)]
    priv = (out != 1)
    print(f"  T_high(1, {L}, 1) = {out}, privileged = {priv}")

# Test 2: T_lo_adj(2, 1, c2) for all c2 (position 1 when c[0]=1, c[1]=2)
print("\nTEST 2: T_lo_adj(2, 1, c2) — position 1 in c when delta=1")
for c2 in range(3):
    out = T_lo_adj[(2, 1, c2)]
    priv = (out != 2)
    print(f"  T_lo_adj(2, 1, {c2}) = {out}, privileged = {priv}")

# Test 3: After delta move (c[0]=1->0), check position n-1 privileged
print("\nTEST 3: T_high(1, L, 0) for all L — position n-1 in c' after delta move")
for L in range(3):
    out = T_high[(1, L, 0)]
    priv = (out != 1)
    print(f"  T_high(1, {L}, 0) = {out}, privileged = {priv}")

# Test 4: After delta move, position 1: T_lo_adj(2, 0, c2)
print("\nTEST 4: T_lo_adj(2, 0, c2) — position 1 in c' after delta move")
for c2 in range(3):
    out = T_lo_adj[(2, 0, c2)]
    priv = (out != 2)
    print(f"  T_lo_adj(2, 0, {c2}) = {out}, privileged = {priv}")

# Test 5: After delta move, position 0: T_low(0, 1, 2)
print("\nTEST 5: T_low(0, 1, 2) — position 0 in c' after delta move")
out = T_low[(0, 1, 2)]
priv = (out != 0)
print(f"  T_low(0, 1, 2) = {out}, privileged = {priv}")

# Test 6: T_mid copy-neighbor verification + fc change
print("\nTEST 6: T_mid firing cases — copy-neighbor and fc change")
for (S,L,R), out in sorted(T_mid.items()):
    if out == S: continue
    is_cn = (out == L or out == R)
    old_left = (1 if L != S else 0)
    new_left = (1 if L != out else 0)
    old_right = (1 if S != R else 0)
    new_right = (1 if out != R else 0)
    delta_fc = (new_left - old_left) + (new_right - old_right)
    if not is_cn:
        print(f"  NOT copy-neighbor: (S={S},L={L},R={R})->out={out}, delta_fc={delta_fc}")
    if delta_fc > 0:
        print(f"  FC INCREASE: (S={S},L={L},R={R})->out={out}, delta_fc={delta_fc}, copy={is_cn}")

# Test 7: T_lo_adj copy-neighbor check
print("\nTEST 7: T_lo_adj firing cases — all fc changes")
for (S,L,R), out in sorted(T_lo_adj.items()):
    if out == S: continue
    old_left = (1 if L != S else 0)
    new_left = (1 if L != out else 0)
    old_right = (1 if S != R else 0)
    new_right = (1 if out != R else 0)
    delta_fc = (new_left - old_left) + (new_right - old_right)
    is_cn = (out == L or out == R)
    print(f"  (S={S},L={L},R={R})->out={out}: delta_fc={delta_fc}, copy_neighbor={is_cn}")

# Test 8: Verify T_lo_adj never increases fc
print("\nTEST 8: T_lo_adj max fc change")
max_delta = max(
    (1 if L != out else 0) - (1 if L != S else 0) + (1 if out != R else 0) - (1 if S != R else 0)
    for (S,L,R), out in T_lo_adj.items() if out != S
)
print(f"  Max delta_fc for T_lo_adj: {max_delta}")

# Test 9: hi_adj (2,2,1)->0 TP analysis
print("\nTEST 9: T_hi_adj (S=2,L=2,R=1)->0 TP change")
print("  Before: c[n-2]=2, c[n-3]=2, c[n-1]=1")
print("  After: c'[n-2]=0, c[n-3]=2, c[n-1]=1")
print("  TP range: j in [2, n-3]")
print("  Position j=n-3:")
print("    Before: c[n-3]=2, c[n-2]=2. c[n-2]=2 not in {0,1} -> no exp2 at j=n-3")
print("    After: c[n-3]=2, c'[n-2]=0. c'[n-2]=0 in {0,1} -> exp2 at j=n-3!")
print("  Exp2Count increases by 1 -> TP NOT preserved.")
