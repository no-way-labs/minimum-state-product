#!/usr/bin/env python3
"""
Verify PhiFull = fc + delta where delta(c) = 1 iff c[0]=1, c[1]=2, c[n-1]=1.
Also verify all the analytical claims needed for the proof.
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

def compute_phi_full(n):
    configs = all_configs(n)
    good = build_good_set(n)
    bad = [c for c in configs if c not in good]
    bad_set = set(bad)
    phi = {c: (0 if c in good else fc(c, n)) for c in configs}
    tp_edges = defaultdict(list)
    for c in bad:
        tp_c = tp_invariant(c, n)
        for i in range(n):
            if not is_privileged(n, c, i): continue
            d = fire(n, c, i)
            if d not in bad_set: continue
            if tp_invariant(d, n) == tp_c:
                tp_edges[c].append(d)
    for _ in range(3*n):
        changed = False
        for c in bad:
            old = phi[c]
            best = fc(c, n)
            for d in tp_edges[c]:
                if phi[d] > best: best = phi[d]
            if best > old: phi[c] = best; changed = True
        if not changed: break
    return phi, good, tp_edges

print("="*70)
print("TEST 1: PhiFull = fc + delta, delta=1 iff c[0]=1,c[1]=2,c[n-1]=1")
print("="*70)

for nv in [9, 10, 11, 12]:
    phi_n, good_n, tp_n = compute_phi_full(nv)
    bad_n = [c for c in phi_n if c not in good_n]
    correct = 0; wrong = 0; wrong_examples = []
    for c in bad_n:
        predicted = 1 if (c[0] == 1 and c[1] == 2 and c[nv-1] == 1) else 0
        actual_delta = phi_n[c] - fc(c, nv)
        if predicted == actual_delta:
            correct += 1
        else:
            wrong += 1
            if wrong <= 3:
                wrong_examples.append((c, predicted, actual_delta))
    print(f"n={nv}: {correct} correct, {wrong} wrong out of {len(bad_n)} bad configs")
    for c, pred, actual in wrong_examples:
        print(f"  WRONG: c={c}, pred={pred}, actual={actual}, fc={fc(c,nv)}, phi={phi_n[c]}")

print()
print("="*70)
print("TEST 2: Position 0 fc change analysis for ALL boundary fire cases")
print("="*70)

# When position 0 fires (T_low(S,L,R) != S), analyze the fc change.
# S=c[0], L=c[n-1], R=c[1]
print("Position 0 fires when T_low(S,L,R) != S:")
for (S,L,R), out in sorted(T_low.items()):
    if out != S:
        # Pair (n-1, 0): was L vs S, becomes L vs out
        # Pair (0, 1): was S vs R, becomes out vs R
        old_left = (1 if L != S else 0)
        new_left = (1 if L != out else 0)
        old_right = (1 if S != R else 0)
        new_right = (1 if out != R else 0)
        delta_fc = (new_left - old_left) + (new_right - old_right)
        print(f"  (S={S},L={L},R={R}) -> out={out}: "
              f"pair(n-1,0): {L}vs{S}->{L}vs{out} ({old_left}->{new_left}), "
              f"pair(0,1): {S}vs{R}->{out}vs{R} ({old_right}->{new_right}), "
              f"delta_fc={delta_fc}")

print()
print("="*70)
print("TEST 3: Position n-1 fc change analysis for ALL boundary fire cases")
print("="*70)

# When position n-1 fires (T_high(S,L,R) != S), analyze the fc change.
# S=c[n-1], L=c[n-2], R=c[0]
print("Position n-1 fires when T_high(S,L,R) != S:")
for (S,L,R), out in sorted(T_high.items()):
    if out != S:
        # Pair (n-2, n-1): was L vs S, becomes L vs out
        # Pair (n-1, 0): was S vs R, becomes out vs R
        old_left = (1 if L != S else 0)
        new_left = (1 if L != out else 0)
        old_right = (1 if S != R else 0)
        new_right = (1 if out != R else 0)
        delta_fc = (new_left - old_left) + (new_right - old_right)
        print(f"  (S={S},L={L},R={R}) -> out={out}: "
              f"pair(n-2,n-1): {L}vs{S}->{L}vs{out} ({old_left}->{new_left}), "
              f"pair(n-1,0): {S}vs{R}->{out}vs{R} ({old_right}->{new_right}), "
              f"delta_fc={delta_fc}")

print()
print("="*70)
print("TEST 4: After delta=1 move, verify delta(c')=0 and c' is bad")
print("="*70)

nv = 11
phi_n, good_n, tp_n = compute_phi_full(nv)
bad_n = set(c for c in phi_n if c not in good_n)
delta1_configs = [c for c in bad_n if c[0]==1 and c[1]==2 and c[nv-1]==1]
print(f"n={nv}: {len(delta1_configs)} configs with delta=1 condition")

all_ok = True
for c in delta1_configs:
    d = fire(nv, c, 0)  # fire position 0
    # Check d[0]=0
    if d[0] != 0:
        print(f"  ERROR: after fire, d[0]={d[0]} != 0")
        all_ok = False
    # Check delta(d)=0: d[0]=0 => delta=0
    if d[0] == 1 and d[1] == 2 and d[nv-1] == 1:
        print(f"  ERROR: d still has delta=1: {d}")
        all_ok = False
    # Check d is bad
    if d in good_n:
        print(f"  ERROR: d is good: {d}")
        all_ok = False
    # Check TP preserved
    if tp_invariant(c, nv) != tp_invariant(d, nv):
        print(f"  ERROR: TP changed: {c} -> {d}")
        all_ok = False

if all_ok:
    print(f"  ALL OK: {len(delta1_configs)} configs verified")
else:
    print(f"  ERRORS found")

print()
print("="*70)
print("TEST 5: Position 1 fc change (T_lo_adj)")
print("="*70)
# When position 1 fires, S=c[1], L=c[0], R=c[2]
# Pairs affected: (0,1) and (1,2)
print("Position 1 fires when T_lo_adj(S,L,R) != S:")
for (S,L,R), out in sorted(T_lo_adj.items()):
    if out != S:
        old_left = (1 if L != S else 0)
        new_left = (1 if L != out else 0)
        old_right = (1 if S != R else 0)
        new_right = (1 if out != R else 0)
        delta_fc = (new_left - old_left) + (new_right - old_right)
        if delta_fc > 0:
            print(f"  FC INCREASE: (S={S},L={L},R={R}) -> out={out}: delta_fc={delta_fc}")

print()
print("="*70)
print("TEST 6: Position n-2 fc change (T_hi_adj)")
print("="*70)
# When position n-2 fires, S=c[n-2], L=c[n-3], R=c[n-1]
# Pairs affected: (n-3,n-2) and (n-2,n-1)
print("Position n-2 fires when T_hi_adj(S,L,R) != S:")
for (S,L,R), out in sorted(T_hi_adj.items()):
    if out != S:
        old_left = (1 if L != S else 0)
        new_left = (1 if L != out else 0)
        old_right = (1 if S != R else 0)
        new_right = (1 if out != R else 0)
        delta_fc = (new_left - old_left) + (new_right - old_right)
        if delta_fc > 0:
            print(f"  FC INCREASE: (S={S},L={L},R={R}) -> out={out}: delta_fc={delta_fc}")

print()
print("="*70)
print("TEST 7: Check which lo_adj/hi_adj fc-increase cases preserve TP")
print("="*70)
# For the fc-increasing cases found above, check if they actually preserve TP
# at n=11 by examining all configs with those local patterns

nv = 11
phi_n, good_n, tp_n = compute_phi_full(nv)
bad_set = set(c for c in phi_n if c not in good_n)

# Check position 1 TP-preserving fc-increase
print("Position 1 TP-preserving fc-increase check:")
count_tp_fc_up = 0
for c in bad_set:
    if not is_privileged(nv, c, 1): continue
    d = fire(nv, c, 1)
    if d not in bad_set: continue
    if tp_invariant(c, nv) != tp_invariant(d, nv): continue
    if fc(d, nv) > fc(c, nv):
        count_tp_fc_up += 1
        if count_tp_fc_up <= 3:
            print(f"  c={c}, d={d}, fc: {fc(c,nv)}->{fc(d,nv)}")
print(f"  Total: {count_tp_fc_up}")

# Check position n-2 TP-preserving fc-increase
print(f"Position {nv-2} TP-preserving fc-increase check:")
count_tp_fc_up = 0
for c in bad_set:
    if not is_privileged(nv, c, nv-2): continue
    d = fire(nv, c, nv-2)
    if d not in bad_set: continue
    if tp_invariant(c, nv) != tp_invariant(d, nv): continue
    if fc(d, nv) > fc(c, nv):
        count_tp_fc_up += 1
        if count_tp_fc_up <= 3:
            print(f"  c={c}, d={d}, fc: {fc(c,nv)}->{fc(d,nv)}")
print(f"  Total: {count_tp_fc_up}")

# Check ALL positions TP-preserving fc-increase
print(f"\nALL positions TP-preserving fc-increase summary:")
for pos in range(nv):
    count = 0
    for c in bad_set:
        if not is_privileged(nv, c, pos): continue
        d = fire(nv, c, pos)
        if d not in bad_set: continue
        if tp_invariant(c, nv) != tp_invariant(d, nv): continue
        if fc(d, nv) > fc(c, nv):
            count += 1
    if count > 0:
        print(f"  Position {pos}: {count} TP-preserving fc-increasing moves")
