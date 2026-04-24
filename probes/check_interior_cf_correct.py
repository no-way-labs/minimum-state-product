#!/usr/bin/env python3
"""
Check interior CF steps for CUP-2 system at n=9.
Verify TP invariant behavior on constant-FutureFc (CF) steps.
"""

from itertools import product as iterproduct

# === Transition tables ===
TBot = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
TLow = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
TMid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
THigh = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
TTop = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}

n = 9
ms = [2, 3, 3, 3, 3, 3, 3, 3, 2]

def get_table(i):
    if i == 0: return TBot
    if i == 1: return TLow
    if 2 <= i <= 6: return TMid
    if i == 7: return THigh
    if i == 8: return TTop

def fire_value(c, i):
    """Return f(L, S, R) for position i in config c."""
    L = c[(i - 1) % n]
    S = c[i]
    R = c[(i + 1) % n]
    return get_table(i)[(L, S, R)]

def is_privileged(c, i):
    return fire_value(c, i) != c[i]

def fc(c):
    return sum(1 for i in range(n) if is_privileged(c, i))

def move(c, i):
    """Fire position i in config c."""
    c2 = list(c)
    c2[i] = fire_value(c, i)
    return tuple(c2)

# === Generate all configs ===
print("Generating all configs...")
all_configs = []
for c0 in range(2):
    for mid in iterproduct(range(3), repeat=7):
        for c8 in range(2):
            all_configs.append((c0,) + mid + (c8,))
print(f"Total configs: {len(all_configs)}")
assert len(all_configs) == 8748

# === Find good cycle ===
print("\nFinding good cycle...")
good_cycle_set = None
good_cycle_list = None

for start in all_configs:
    if fc(start) != 1:
        continue
    # Find the single privileged position
    priv = [i for i in range(n) if is_privileged(start, i)]
    if len(priv) != 1:
        continue
    # Trace cycle
    cycle = [start]
    c = move(start, priv[0])
    steps = 0
    while c != start and steps < 30:
        priv_c = [i for i in range(n) if is_privileged(c, i)]
        if len(priv_c) != 1:
            break
        c = move(c, priv_c[0])
        if c != start:
            cycle.append(c)
        steps += 1
    if c == start and len(cycle) == 25:
        good_cycle_list = cycle
        good_cycle_set = set(cycle)
        print(f"Found good cycle of length {len(cycle)}")
        break

if good_cycle_set is None:
    # Try fc=1 configs that form a 25-cycle
    # Actually, let's be more careful: trace from each fc=1 config
    for start in all_configs:
        if fc(start) != 1:
            continue
        priv = [i for i in range(n) if is_privileged(start, i)][0]
        cycle = [start]
        c = move(start, priv)
        ok = True
        for _ in range(24):
            if c == start:
                break
            priv_c = [i for i in range(n) if is_privileged(c, i)]
            if len(priv_c) != 1:
                ok = False
                break
            cycle.append(c)
            c = move(c, priv_c[0])
        if ok and c == start and len(cycle) == 25:
            good_cycle_list = cycle
            good_cycle_set = set(cycle)
            print(f"Found good cycle of length {len(cycle)}")
            break

if good_cycle_set is None:
    print("ERROR: Could not find good cycle!")
    exit(1)

print(f"Good cycle configs: {len(good_cycle_set)}")
# Print first few
for i, c in enumerate(good_cycle_list[:5]):
    priv = [j for j in range(n) if is_privileged(c, j)]
    print(f"  gc[{i}]: {c}  fc={fc(c)} priv={priv}")
print("  ...")

# === Bad configs ===
bad_configs = [c for c in all_configs if c not in good_cycle_set]
print(f"\nBad configs: {len(bad_configs)}")

# === Compute bad steps ===
# badStep(c', c): c not in good, c' not in good, c' = move(c, i) for some privileged i
print("\nComputing bad steps...")
bad_set = set(bad_configs)
bad_steps = []  # (c, c', i)
for c in bad_configs:
    for i in range(n):
        if is_privileged(c, i):
            c2 = move(c, i)
            if c2 in bad_set:
                bad_steps.append((c, c2, i))

print(f"Total bad steps: {len(bad_steps)}")

# === Compute FutureFc via fixpoint ===
print("\nComputing FutureFc via fixpoint...")
future_fc = {}
for c in bad_configs:
    future_fc[c] = fc(c)

# Build adjacency: for each bad config, what bad configs can it reach?
adj = {}
for c in bad_configs:
    adj[c] = []
for c, c2, i in bad_steps:
    adj[c].append(c2)

changed = True
iterations = 0
while changed:
    changed = False
    iterations += 1
    for c in bad_configs:
        for c2 in adj[c]:
            if future_fc[c2] > future_fc[c]:
                future_fc[c] = future_fc[c2]
                changed = True
    if iterations > 100:
        print("WARNING: fixpoint did not converge in 100 iterations")
        break

print(f"FutureFc converged in {iterations} iterations")

# Distribution of FutureFc
from collections import Counter
ffc_dist = Counter(future_fc[c] for c in bad_configs)
print(f"FutureFc distribution: {sorted(ffc_dist.items())}")

# === CF steps: bad steps where FutureFc is preserved ===
print("\nFinding CF (constant-FutureFc) bad steps...")
cf_steps = []
for c, c2, i in bad_steps:
    if future_fc[c] == future_fc[c2]:
        cf_steps.append((c, c2, i))

print(f"Total CF bad steps: {len(cf_steps)}")

# === TP invariant ===
def exp2Bit(j, cj, cj1):
    """1 if 2 <= j and j+2 < n and c[j]=2 and c[j+1] != 2"""
    if 2 <= j and j + 2 < n and cj == 2 and cj1 != 2:
        return 1
    return 0

def int21Bit(j, cj, cj1):
    """1 if 2 <= j and j+2 < n and c[j]=2 and c[j+1]=1"""
    if 2 <= j and j + 2 < n and cj == 2 and cj1 == 1:
        return 1
    return 0

def exp2Count(c):
    return sum(exp2Bit(j, c[j], c[(j+1) % n]) for j in range(n))

def int21Count(c):
    return sum(int21Bit(j, c[j], c[(j+1) % n]) for j in range(n))

def exp2Weight(c):
    return sum(j * exp2Bit(j, c[j], c[(j+1) % n]) for j in range(n))

def TP(c):
    return (exp2Count(c), int21Count(c), exp2Weight(c))

# === Classify CF steps ===
boundary_positions = {0, 1, 2, 7, 8}
interior_positions = {3, 4, 5, 6}

cf_boundary = [(c, c2, i) for c, c2, i in cf_steps if i in boundary_positions]
cf_interior = [(c, c2, i) for c, c2, i in cf_steps if i in interior_positions]

print(f"\nCF boundary steps (i in {{0,1,2,7,8}}): {len(cf_boundary)}")
print(f"CF interior steps (i in {{3,4,5,6}}): {len(cf_interior)}")

# === Analyze CF interior steps ===
print("\n=== CF Interior Step Analysis ===")

tp_decrease = []
tp_increase = []
tp_preserve_fc_preserve = []  # deepMidTpZero
tp_preserve_fc_change = []    # GAP

for c, c2, i in cf_interior:
    tp_c = TP(c)
    tp_c2 = TP(c2)
    fc_c = fc(c)
    fc_c2 = fc(c2)

    if tp_c2 < tp_c:  # lex decrease
        tp_decrease.append((c, c2, i, tp_c, tp_c2, fc_c, fc_c2))
    elif tp_c2 > tp_c:  # lex increase
        tp_increase.append((c, c2, i, tp_c, tp_c2, fc_c, fc_c2))
    else:  # TP preserved
        if fc_c == fc_c2:
            tp_preserve_fc_preserve.append((c, c2, i, tp_c, tp_c2, fc_c, fc_c2))
        else:
            tp_preserve_fc_change.append((c, c2, i, tp_c, tp_c2, fc_c, fc_c2))

print(f"  TP decreases (lex): {len(tp_decrease)}")
print(f"  TP increases (lex): {len(tp_increase)}")
print(f"  TP preserved, fc preserved (deepMidTpZero): {len(tp_preserve_fc_preserve)}")
print(f"  TP preserved, fc changed (GAP): {len(tp_preserve_fc_change)}")

if tp_increase:
    print("\n  WARNING: TP INCREASES found on CF interior steps!")
    for c, c2, i, tp_c, tp_c2, fc_c, fc_c2 in tp_increase[:10]:
        print(f"    c={c} -> c'={c2} at pos {i}")
        print(f"      TP: {tp_c} -> {tp_c2}, fc: {fc_c} -> {fc_c2}")
        print(f"      FutureFc: {future_fc[c]} -> {future_fc[c2]}")
else:
    print("\n  GOOD: No TP increases on CF interior steps.")

if tp_preserve_fc_change:
    print(f"\n  GAP cases (TP preserved, fc changed) — {len(tp_preserve_fc_change)} steps:")
    for c, c2, i, tp_c, tp_c2, fc_c, fc_c2 in tp_preserve_fc_change[:10]:
        print(f"    c={c} -> c'={c2} at pos {i}")
        print(f"      TP: {tp_c} -> {tp_c2}, fc: {fc_c} -> {fc_c2}")
        print(f"      FutureFc: {future_fc[c]}")

if tp_preserve_fc_preserve:
    print(f"\n  deepMidTpZero cases — {len(tp_preserve_fc_preserve)} steps (first 10):")
    for c, c2, i, tp_c, tp_c2, fc_c, fc_c2 in tp_preserve_fc_preserve[:10]:
        print(f"    c={c} -> c'={c2} at pos {i}")
        print(f"      TP: {tp_c}, fc: {fc_c}, FutureFc: {future_fc[c]}")

if tp_decrease:
    print(f"\n  TP decrease cases — {len(tp_decrease)} steps (first 5):")
    for c, c2, i, tp_c, tp_c2, fc_c, fc_c2 in tp_decrease[:5]:
        print(f"    c={c} -> c'={c2} at pos {i}")
        print(f"      TP: {tp_c} -> {tp_c2}, fc: {fc_c} -> {fc_c2}")

# === Verify TP non-increasing on ALL bad steps ===
print("\n=== TP non-increasing on ALL bad steps ===")
all_tp_increase = []
for c, c2, i in bad_steps:
    tp_c = TP(c)
    tp_c2 = TP(c2)
    if tp_c2 > tp_c:
        all_tp_increase.append((c, c2, i, tp_c, tp_c2))

print(f"Bad steps with TP increase: {len(all_tp_increase)}")
if all_tp_increase:
    print("FAIL: TP is NOT non-increasing on all bad steps!")
    for c, c2, i, tp_c, tp_c2 in all_tp_increase[:10]:
        print(f"  c={c} -> c'={c2} at pos {i}")
        print(f"    TP: {tp_c} -> {tp_c2}, fc: {fc(c)} -> {fc(c2)}")
        print(f"    FutureFc: {future_fc[c]} -> {future_fc[c2]}")
else:
    print("PASS: TP is non-increasing on ALL bad steps.")

# === Also check TP on ALL CF steps (boundary + interior) ===
print("\n=== TP on ALL CF steps ===")
all_cf_tp_increase = []
for c, c2, i in cf_steps:
    tp_c = TP(c)
    tp_c2 = TP(c2)
    if tp_c2 > tp_c:
        all_cf_tp_increase.append((c, c2, i, tp_c, tp_c2))

print(f"CF steps with TP increase: {len(all_cf_tp_increase)}")
if all_cf_tp_increase:
    print("TP increases on CF steps (first 10):")
    for c, c2, i, tp_c, tp_c2 in all_cf_tp_increase[:10]:
        print(f"  c={c} -> c'={c2} at pos {i}")
        print(f"    TP: {tp_c} -> {tp_c2}, fc: {fc(c)} -> {fc(c2)}")

# === Summary ===
print("\n" + "="*60)
print("SUMMARY")
print("="*60)
print(f"n = {n}, total configs = {len(all_configs)}")
print(f"Good cycle length = {len(good_cycle_set)}")
print(f"Bad configs = {len(bad_configs)}")
print(f"Bad steps = {len(bad_steps)}")
print(f"CF bad steps = {len(cf_steps)}")
print(f"  CF boundary = {len(cf_boundary)}")
print(f"  CF interior = {len(cf_interior)}")
print(f"    TP decrease: {len(tp_decrease)}")
print(f"    TP increase: {len(tp_increase)}")
print(f"    TP=, fc=  (deepMidTpZero): {len(tp_preserve_fc_preserve)}")
print(f"    TP=, fc!= (GAP):           {len(tp_preserve_fc_change)}")
print(f"TP non-increasing on ALL bad steps: {'YES' if not all_tp_increase else 'NO'}")
print(f"TP non-increasing on ALL CF steps:  {'YES' if not all_cf_tp_increase else 'NO'}")
