#!/usr/bin/env python3
"""
Check whether Φ_full is monotone on ALL bad steps (not just TP-preserving).
If yes: we can use Φ_full as a drop-in replacement for FutureFc.
If no: we need three-level decomposition (TP + Φ_full + DAG).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import build_system
from collections import Counter

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
    new = fs[pos](L, S, R)
    c2 = list(c); c2[pos] = new
    return tuple(c2)

def fc(c):
    return sum(1 for j in range(n) if c[j] != c[(j+1)%n])

def exp2_count(c):
    return sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
def int_21(c):
    return sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n]==1)
def exp2_weight(c):
    return sum(j for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
def tp(c):
    return (exp2_count(c), int_21(c), exp2_weight(c))

# Build
bad = {}
for i in range(N):
    c = idx_to_config(i)
    f = fc(c)
    if f > 0:
        bad[i] = {'c': c, 'fc': f, 'tp': tp(c)}

print(f"Bad configs: {len(bad)}")

# Build bad-step + TP-preserving subgraph
bad_adj = {i: [] for i in bad}
tp_adj = {i: [] for i in bad}
for i in bad:
    c = bad[i]['c']
    for p in range(n):
        c2 = move(c, p)
        if c2 == c: continue
        j = config_to_idx(c2)
        if j in bad:
            bad_adj[i].append(j)
            if bad[j]['tp'] == bad[i]['tp']:
                tp_adj[i].append(j)

# Compute FutureFc and Φ_full
future_fc = {i: bad[i]['fc'] for i in bad}
phi_full = {i: bad[i]['fc'] for i in bad}

# FutureFc: max over ALL bad-reachable
rev = {i: [] for i in bad}
for i in bad:
    for j in bad_adj[i]: rev[j].append(i)

changed = True
while changed:
    changed = False
    for j in bad:
        for i in rev[j]:
            if future_fc[j] > future_fc[i]:
                future_fc[i] = future_fc[j]; changed = True

# Φ_full: max over TP-reachable
tp_rev = {i: [] for i in bad}
for i in bad:
    for j in tp_adj[i]: tp_rev[j].append(i)

changed = True
while changed:
    changed = False
    for j in bad:
        for i in tp_rev[j]:
            if phi_full[j] > phi_full[i]:
                phi_full[i] = phi_full[j]; changed = True

# Check Φ_full monotonicity on ALL bad steps
print("\n=== Φ_full monotonicity on ALL bad steps ===")
phi_increase = 0
phi_preserve = 0
phi_decrease = 0
phi_increase_examples = []

for i in bad:
    for j in bad_adj[i]:
        if phi_full[j] > phi_full[i]:
            phi_increase += 1
            if len(phi_increase_examples) < 5:
                phi_increase_examples.append((i, j))
        elif phi_full[j] == phi_full[i]:
            phi_preserve += 1
        else:
            phi_decrease += 1

total = phi_increase + phi_preserve + phi_decrease
print(f"Total bad steps: {total}")
print(f"  Φ_full increases: {phi_increase}")
print(f"  Φ_full preserves: {phi_preserve}")
print(f"  Φ_full decreases: {phi_decrease}")

if phi_increase > 0:
    print(f"\n*** Φ_full is NOT monotone on all bad steps ***")
    for (i, j) in phi_increase_examples:
        c, c2 = bad[i]['c'], bad[j]['c']
        print(f"  {c} -> {c2}")
        print(f"    tp: {bad[i]['tp']} -> {bad[j]['tp']}")
        print(f"    fc: {bad[i]['fc']} -> {bad[j]['fc']}")
        print(f"    Φ_full: {phi_full[i]} -> {phi_full[j]}")
        print(f"    FutureFc: {future_fc[i]} -> {future_fc[j]}")
else:
    print(f"\n*** Φ_full IS monotone on all bad steps ***")

# Also check: FutureFc monotonicity (should always hold)
print("\n=== FutureFc monotonicity check ===")
ff_increase = sum(1 for i in bad for j in bad_adj[i] if future_fc[j] > future_fc[i])
print(f"FutureFc increases: {ff_increase}  (should be 0)")

# Check: does (TP, Φ_full) decrease in lex on all bad steps?
print("\n=== (TP, Φ_full) lex descent on all bad steps ===")
tp_phi_violations = 0
for i in bad:
    ti = bad[i]['tp']
    for j in bad_adj[i]:
        tj = bad[j]['tp']
        if tj < ti: continue  # TP drops: OK
        if tj == ti and phi_full[j] <= phi_full[i]: continue  # TP same, Φ ≤: OK
        tp_phi_violations += 1

print(f"Violations: {tp_phi_violations}")
if tp_phi_violations == 0:
    print("*** (TP, Φ_full) decreases in lex on ALL bad steps! ***")

# Check: does (TP, Φ_full, sixStateRank, deepMidHopPotential) decrease on all bad steps?
# Approximate: just check (TP, Φ_full) first since that's the outer layers

print("\nDONE")
