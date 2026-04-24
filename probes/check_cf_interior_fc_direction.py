#!/usr/bin/env python3
"""Check fc direction of CF interior vs boundary bad steps for CUP-2 at n=9."""

from itertools import product

n = 9
ms = [2] + [3]*7 + [2]

TBot = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
TLow = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
TMid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
THigh = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
TTop = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}

def table_for(p):
    if p == 0: return TBot
    if p == 1: return TLow
    if p == n-2: return THigh
    if p == n-1: return TTop
    return TMid

def apply_rule(c, p):
    """Apply rule at position p, return new config."""
    L = c[(p-1) % n]
    S = c[p]
    R = c[(p+1) % n]
    T = table_for(p)
    new_val = T[(L, S, R)]
    if new_val == S:
        return None  # not privileged
    c2 = list(c)
    c2[p] = new_val
    return tuple(c2)

def privileged(c):
    """Return set of privileged positions."""
    privs = []
    for p in range(n):
        L = c[(p-1) % n]
        S = c[p]
        R = c[(p+1) % n]
        T = table_for(p)
        if T[(L, S, R)] != S:
            privs.append(p)
    return privs

def fc(c):
    """Number of non-privileged (fixed) positions."""
    return n - len(privileged(c))

# Build good cycle
print("Building good cycle...")
good_set = set()
c = tuple([0]*n)
good_cycle = [c]
good_set.add(c)
for step in range(25):
    privs = privileged(c)
    assert len(privs) == 1, f"Step {step}: {len(privs)} privileged at {c}"
    c = apply_rule(c, privs[0])
    if c in good_set:
        break
    good_set.add(c)
    good_cycle.append(c)

print(f"Good cycle length: {len(good_set)}")
print(f"fc values in good cycle: {sorted(set(fc(c) for c in good_set))}")

# Enumerate all configs
print("\nEnumerating all configs...")
all_configs = []
for vals in product(*(range(ms[i]) for i in range(n))):
    all_configs.append(vals)
print(f"Total configs: {len(all_configs)}")

bad_configs = set(c for c in all_configs if c not in good_set)
print(f"Bad configs: {len(bad_configs)}")

# Enumerate ALL bad steps: c bad, fire at p, get c' bad
print("\nEnumerating bad steps...")
bad_steps = []  # (c, p, c')
for c in bad_configs:
    for p in privileged(c):
        c2 = apply_rule(c, p)
        if c2 is not None and c2 in bad_configs:
            bad_steps.append((c, p, c2))

print(f"Total bad steps (bad->bad): {len(bad_steps)}")

# Compute FutureFc by fixpoint: FutureFc(c) = max fc reachable via bad steps
print("\nComputing FutureFc by fixpoint...")
future_fc = {}
for c in bad_configs:
    future_fc[c] = fc(c)

changed = True
iters = 0
while changed:
    changed = False
    iters += 1
    for (c, p, c2) in bad_steps:
        if future_fc[c2] > future_fc[c]:
            future_fc[c] = future_fc[c2]
            changed = True

print(f"FutureFc fixpoint converged in {iters} iterations")
print(f"FutureFc range: {min(future_fc.values())}..{max(future_fc.values())}")

# CF bad steps: FutureFc(c') == FutureFc(c)
cf_steps = [(c, p, c2) for (c, p, c2) in bad_steps if future_fc[c2] == future_fc[c]]
print(f"\nCF bad steps: {len(cf_steps)}")

# Classify by position type and fc direction
interior = {3, 4, 5, 6}
boundary = {0, 1, 2, 7, 8}

def classify(steps, label):
    int_inc, int_eq, int_dec = 0, 0, 0
    bnd_inc, bnd_eq, bnd_dec = 0, 0, 0
    for (c, p, c2) in steps:
        fc_c = fc(c)
        fc_c2 = fc(c2)
        if p in interior:
            if fc_c2 > fc_c: int_inc += 1
            elif fc_c2 == fc_c: int_eq += 1
            else: int_dec += 1
        else:
            if fc_c2 > fc_c: bnd_inc += 1
            elif fc_c2 == fc_c: bnd_eq += 1
            else: bnd_dec += 1

    print(f"\n{'='*60}")
    print(f"{label}")
    print(f"{'='*60}")
    int_total = int_inc + int_eq + int_dec
    bnd_total = bnd_inc + bnd_eq + bnd_dec
    print(f"\nInterior (pos 3,4,5,6): {int_total} steps")
    print(f"  fc increases: {int_inc}")
    print(f"  fc preserved: {int_eq}")
    print(f"  fc decreases: {int_dec}")
    if int_total > 0:
        print(f"  (inc {100*int_inc/int_total:.1f}%, eq {100*int_eq/int_total:.1f}%, dec {100*int_dec/int_total:.1f}%)")

    print(f"\nBoundary (pos 0,1,2,7,8): {bnd_total} steps")
    print(f"  fc increases: {bnd_inc}")
    print(f"  fc preserved: {bnd_eq}")
    print(f"  fc decreases: {bnd_dec}")
    if bnd_total > 0:
        print(f"  (inc {100*bnd_inc/bnd_total:.1f}%, eq {100*bnd_eq/bnd_total:.1f}%, dec {100*bnd_dec/bnd_total:.1f}%)")

classify(cf_steps, "CF BAD STEPS (FutureFc preserved)")
classify(bad_steps, "ALL BAD STEPS")

# Extra: check if ANY interior bad step decreases fc
int_dec_all = [(c,p,c2) for (c,p,c2) in bad_steps if p in interior and fc(c2) < fc(c)]
print(f"\n{'='*60}")
print(f"SUMMARY: Interior fc-decreasing bad steps exist? {len(int_dec_all) > 0} ({len(int_dec_all)} total)")
int_dec_cf = [(c,p,c2) for (c,p,c2) in cf_steps if p in interior and fc(c2) < fc(c)]
print(f"SUMMARY: Interior fc-decreasing CF steps exist?  {len(int_dec_cf) > 0} ({len(int_dec_cf)} total)")

# Also show fc distribution of CF steps
print(f"\n{'='*60}")
print("FC values at CF steps:")
from collections import Counter
fc_vals = Counter()
for (c, p, c2) in cf_steps:
    fc_vals[fc(c)] += 1
for k in sorted(fc_vals):
    print(f"  fc={k}: {fc_vals[k]} steps")

ffc_vals = Counter()
for (c, p, c2) in cf_steps:
    ffc_vals[future_fc[c]] += 1
print("\nFutureFc values at CF steps:")
for k in sorted(ffc_vals):
    print(f"  FutureFc={k}: {ffc_vals[k]} steps")
