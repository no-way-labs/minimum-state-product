#!/usr/bin/env python3
"""
Check: is TP = (Exp2Count, Int21Count, Exp2Weight) lex-nonincreasing on ALL bad steps?
Also: analyze the local TP change per table entry to inform analytical proof.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import build_system, T_bot, T_low, T_mid, T_high, T_top

n = 9
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
    return tuple(c[j] if j != pos else fs[pos](L, S, R) for j in range(n))
def fc(c):
    return sum(1 for j in range(n) if c[j] != c[(j+1)%n])
def exp2_count(c):
    return sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
def int_21(c):
    return sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n]==1)
def exp2_weight(c):
    return sum(j for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
def tp(c): return (exp2_count(c), int_21(c), exp2_weight(c))

# Check TP lex nonincreasing on ALL bad steps
print("=== TP lex-nonincreasing check on ALL bad steps ===")
bad_configs = []
for i in range(N):
    c = idx_to_config(i)
    if fc(c) > 0:
        bad_configs.append(c)

tp_increases = 0
tp_decreases = 0
tp_same = 0
tp_increase_examples = []

for c in bad_configs:
    for p in range(n):
        c2 = move(c, p)
        if c2 == c: continue
        if fc(c2) == 0: continue  # c2 is good, not a bad step target
        t1, t2 = tp(c), tp(c2)
        if t2 < t1:
            tp_decreases += 1
        elif t2 == t1:
            tp_same += 1
        else:
            tp_increases += 1
            if len(tp_increase_examples) < 5:
                tp_increase_examples.append((c, c2, p, t1, t2))

total = tp_increases + tp_decreases + tp_same
print(f"Total bad steps: {total}")
print(f"TP decreases (lex): {tp_decreases}")
print(f"TP same: {tp_same}")
print(f"TP increases (lex): {tp_increases}")

if tp_increases > 0:
    print(f"\n*** TP is NOT lex-nonincreasing on all bad steps ***")
    for (c, c2, p, t1, t2) in tp_increase_examples:
        print(f"  pos={p}: {c} -> {c2}  TP: {t1} -> {t2}")
else:
    print(f"\n*** TP IS lex-nonincreasing on ALL bad steps ***")

# Analyze per-table local TP changes
print("\n=== Local TP change per table entry ===")
tables = {
    'TBot': T_bot, 'TLow': T_low, 'TMid': T_mid, 'THigh': T_high, 'TTop': T_top
}
for name, table in tables.items():
    print(f"\n{name}:")
    for (L, S, R), out in sorted(table.items()):
        if out == S:
            continue  # no-op, not privileged
        # Local exp2 change: depends on position
        # Exp2Bit at (j, a, b) = 1 if 2≤j, j+2<n, a=2, b≠2
        # For a move at position p:
        #   Term at j=p-1: before=(c[p-1], S), after=(c[p-1], out) → here c[p-1]=L
        #   Term at j=p:   before=(S, c[p+1]), after=(out, c[p+1]) → here c[p+1]=R

        # Exp2Bit(j, a, b) for interior positions where 2≤j and j+2<n:
        def e2(a, b): return 1 if a == 2 and b != 2 else 0
        def i21(a, b): return 1 if a == 2 and b == 1 else 0

        # At j=p-1 (affected by L→L, S→out on right):
        d_e2_left = e2(L, out) - e2(L, S)
        d_i21_left = i21(L, out) - i21(L, S)

        # At j=p (affected by S→out on left, R→R on right):
        d_e2_right = e2(out, R) - e2(S, R)
        d_i21_right = i21(out, R) - i21(S, R)

        d_e2 = d_e2_left + d_e2_right
        d_i21 = d_i21_left + d_i21_right
        # Weight change: j * de2 for each affected term
        # At j=p-1: weight change = (p-1) * d_e2_left
        # At j=p: weight change = p * d_e2_right
        # Combined: depends on p, so not position-independent for weight

        marker = ""
        if d_e2 > 0:
            marker = " *** EXP2 INCREASES"
        elif d_e2 == 0 and d_i21 > 0:
            marker = " *** INT21 INCREASES (exp2 same)"

        print(f"  ({L},{S},{R})->{out}: Δe2=({d_e2_left:+d},{d_e2_right:+d})={d_e2:+d}  "
              f"Δi21=({d_i21_left:+d},{d_i21_right:+d})={d_i21:+d}{marker}")

print("\nDONE")
