#!/usr/bin/env python3
"""Check: within CΦ (constant FutureFc + TP + Φ_full), is fc always preserved?"""
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

def boundary6(c):
    return ((((c[0]*3+c[1])*3+c[2])*3+c[n-3])*3+c[n-2])*2+c[n-1]

bad = {}
for i in range(N):
    c = idx_to_config(i)
    f = fc(c)
    if f > 0:
        bad[i] = {'c': c, 'fc': f, 'tp': tp(c)}

# Build TP-preserving adjacency + compute Φ_full
bad_adj = {i: [] for i in bad}
tp_adj = {i: [] for i in bad}
for i in bad:
    c = bad[i]['c']
    for p in range(n):
        c2 = move(c, p)
        if c2 == c: continue
        j = config_to_idx(c2)
        if j in bad:
            bad_adj[i].append((j, p))
            if bad[j]['tp'] == bad[i]['tp']:
                tp_adj[i].append(j)

# FutureFc
future_fc = {i: bad[i]['fc'] for i in bad}
rev = {i: [] for i in bad}
for i in bad:
    for j, _ in bad_adj[i]: rev[j].append(i)
changed = True
while changed:
    changed = False
    for j in bad:
        for i in rev[j]:
            if future_fc[j] > future_fc[i]:
                future_fc[i] = future_fc[j]; changed = True

# Φ_full
phi_full = {i: bad[i]['fc'] for i in bad}
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

# Check CΦ steps: fc preservation
print("=== CΦ fc preservation check ===")
cphi_total = 0
cphi_fc_changes = 0
cphi_fc_change_examples = []
cphi_bdry_fixed_fc_changes = 0

for i in bad:
    c = bad[i]['c']
    for j, p in bad_adj[i]:
        if (future_fc[j] == future_fc[i] and
            bad[j]['tp'] == bad[i]['tp'] and
            phi_full[j] == phi_full[i]):
            # CΦ step
            cphi_total += 1
            if bad[j]['fc'] != bad[i]['fc']:
                cphi_fc_changes += 1
                if boundary6(bad[j]['c']) == boundary6(c):
                    cphi_bdry_fixed_fc_changes += 1
                    if len(cphi_fc_change_examples) < 5:
                        cphi_fc_change_examples.append((i, j, p))

print(f"CΦ steps total: {cphi_total}")
print(f"CΦ steps with fc change: {cphi_fc_changes}")
print(f"CΦ steps with fc change AND fixed boundary: {cphi_bdry_fixed_fc_changes}")

if cphi_fc_change_examples:
    print("\nExamples (boundary-fixed, fc changes):")
    for (i, j, p) in cphi_fc_change_examples:
        c, c2 = bad[i]['c'], bad[j]['c']
        print(f"  pos={p}: {c} -> {c2}  fc: {bad[i]['fc']}->{bad[j]['fc']}  "
              f"FutureFc={future_fc[i]}  Φ_full={phi_full[i]}")
else:
    print("\n*** ALL CΦ boundary-fixed steps preserve fc! ***")

print("\nDONE")
