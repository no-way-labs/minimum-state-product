#!/usr/bin/env python3
"""
Check CF (constant-FutureFc) bad steps at true interior positions for CUP-2, n=9.

True interior = {3,4,5} (don't affect the 6-tuple {0,1,2,6,7,8}).
Also check position 6 separately.

fc(c) = number of processors p where f_p(L,S,R) == S (i.e., p is "fixed"/legitimate).
A config is "good" (legitimate) iff fc(c) == n.
A "bad step" fires a processor p where f_p(L,S,R) != S.
FutureFc(c) = max fc reachable from c via bad steps (fixpoint).
CF step = bad step where FutureFc is preserved.
"""

from itertools import product as iproduct

n = 9
ms = [2] + [3]*7 + [2]  # ms = (2,3,3,3,3,3,3,3,2)

# CUP-2 tables
TBot = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
TLow = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
TMid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
THigh = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
TTop = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}

def apply_table(c, p):
    """Return the new value for position p given config c."""
    L = c[(p - 1) % n]
    S = c[p]
    R = c[(p + 1) % n]
    if p == 0:
        return TBot[(L, S, R)]
    elif p == 1:
        return TLow[(L, S, R)]
    elif 2 <= p <= n - 3:  # positions 2..6
        return TMid[(L, S, R)]
    elif p == n - 2:  # position 7
        return THigh[(L, S, R)]
    elif p == n - 1:  # position 8
        return TTop[(L, S, R)]

def fc(c):
    """Count fixed processors: fc(c) = #{p : f_p(L,S,R) == S}."""
    return sum(1 for p in range(n) if apply_table(c, p) == c[p])

def is_legitimate(c):
    """Config is legitimate (good) iff all processors are fixed."""
    return fc(c) == n

def fire(c, p):
    """Fire processor p: returns new config."""
    c2 = list(c)
    c2[p] = apply_table(c, p)
    return tuple(c2)

def is_bad_at(c, p):
    """Processor p is 'bad' (wants to change) at config c."""
    return apply_table(c, p) != c[p]

# Enumerate all configs
all_configs = list(iproduct(*[range(m) for m in ms]))
print(f"Total configs: {len(all_configs)}")

legit_count = sum(1 for c in all_configs if is_legitimate(c))
print(f"Legitimate configs (fc=n): {legit_count}")

bad_configs = [c for c in all_configs if not is_legitimate(c)]
print(f"Non-legitimate configs: {len(bad_configs)}")

# fc distribution
fc_dist = {}
for c in all_configs:
    f = fc(c)
    fc_dist[f] = fc_dist.get(f, 0) + 1
print(f"fc distribution: { {k: fc_dist[k] for k in sorted(fc_dist)} }")

# ---- Compute FutureFc ----
# FutureFc(c) = max fc reachable from c via any sequence of bad steps
# For legitimate configs, FutureFc = n.
# For non-legitimate, propagate via fixpoint.

print("\nComputing FutureFc via fixpoint...")
future_fc = {}
for c in all_configs:
    future_fc[c] = fc(c)

changed = True
iteration = 0
while changed:
    changed = False
    iteration += 1
    for c in bad_configs:
        for p in range(n):
            if not is_bad_at(c, p):
                continue
            c2 = fire(c, p)
            if future_fc[c2] > future_fc[c]:
                future_fc[c] = future_fc[c2]
                changed = True
    if iteration % 10 == 0:
        print(f"  iteration {iteration}...")

print(f"  Converged after {iteration} iterations")

# FutureFc distribution
ffc_dist = {}
for c in bad_configs:
    f = future_fc[c]
    ffc_dist[f] = ffc_dist.get(f, 0) + 1
print(f"FutureFc distribution (bad configs): { {k: ffc_dist[k] for k in sorted(ffc_dist)} }")

# ---- Collect CF bad steps ----
# CF bad step: fire p at c (p is bad), get c2, with future_fc[c] == future_fc[c2]

true_interior = {3, 4, 5}

cf_steps_true_interior = []
cf_steps_pos6 = []

print("\nScanning CF bad steps...")
for c in bad_configs:
    ffc_c = future_fc[c]
    fc_c = fc(c)
    for p in range(n):
        if not is_bad_at(c, p):
            continue
        c2 = fire(c, p)
        ffc_c2 = future_fc[c2]
        fc_c2 = fc(c2)
        delta_fc = fc_c2 - fc_c

        if ffc_c == ffc_c2:  # CF step
            record = (c, p, fc_c, fc_c2, ffc_c, delta_fc)
            if p in true_interior:
                cf_steps_true_interior.append(record)
            if p == 6:
                cf_steps_pos6.append(record)

# ---- Results ----
print("\n" + "="*60)
print("CF bad steps at TRUE INTERIOR positions {3,4,5}")
print("="*60)

total_ti = len(cf_steps_true_interior)
inc_ti = sum(1 for r in cf_steps_true_interior if r[5] > 0)
zero_ti = sum(1 for r in cf_steps_true_interior if r[5] == 0)
neg_ti = sum(1 for r in cf_steps_true_interior if r[5] < 0)

print(f"1. Total CF bad steps:      {total_ti}")
print(f"2. fc INCREASE (delta > 0): {inc_ti}")
print(f"3. fc PRESERVE (delta = 0): {zero_ti}")
print(f"4. fc DECREASE (delta < 0): {neg_ti}")

print("\n" + "="*60)
print("CF bad steps at position 6")
print("="*60)

total_p6 = len(cf_steps_pos6)
neg_p6 = sum(1 for r in cf_steps_pos6 if r[5] < 0)

print(f"5. Total CF bad steps:      {total_p6}")
print(f"6. fc DECREASE (delta < 0): {neg_p6}")

# Examples
if neg_ti > 0:
    print("\n" + "="*60)
    print("Examples of fc-DECREASING CF steps at true interior {3,4,5}")
    print("="*60)
    neg_examples = [r for r in cf_steps_true_interior if r[5] < 0]
    for i, (c, p, fc_b, fc_a, ffc, delta) in enumerate(neg_examples[:3]):
        c2 = fire(c, p)
        print(f"\nExample {i+1}:")
        print(f"  Config:       {c}")
        print(f"  Position:     {p}")
        print(f"  fc before:    {fc_b}")
        print(f"  fc after:     {fc_a}")
        print(f"  FutureFc:     {ffc}")
        print(f"  delta_fc:     {delta}")
        print(f"  Config after: {c2}")
else:
    print("\nNo fc-decreasing CF steps at true interior positions.")

# ---- Per-position breakdown ----
print("\n" + "="*60)
print("CF bad step counts by position (all positions)")
print("="*60)

for pos in range(n):
    steps = []
    for c in bad_configs:
        if not is_bad_at(c, pos):
            continue
        c2 = fire(c, pos)
        if future_fc[c] == future_fc[c2]:
            steps.append(fc(c2) - fc(c))

    total = len(steps)
    inc = sum(1 for d in steps if d > 0)
    zero = sum(1 for d in steps if d == 0)
    dec = sum(1 for d in steps if d < 0)
    marker = ""
    if pos in true_interior:
        marker = " <-- true interior"
    elif pos == 6:
        marker = " <-- boundary-adjacent"
    print(f"  P{pos}: total={total:5d}  inc={inc:5d}  same={zero:5d}  dec={dec:5d}{marker}")
