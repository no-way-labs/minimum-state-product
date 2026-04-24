#!/usr/bin/env python3
"""Check fc direction within CΦ boundary-fixed steps."""
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
def boundary6(c):
    return ((((c[0]*3+c[1])*3+c[2])*3+c[n-3])*3+c[n-2])*2+c[n-1]
def psi(c):
    """Simplified Psi from CopyDAG."""
    total = 0
    for j in range(n):
        a, b = c[j], c[(j+1)%n]
        if a != b:
            # frontier type 1 = (2,x) where x!=2, weight w1
            # frontier type 2 = other, weight w2
            w1 = n - 1 if j == 0 else j
            w2 = 0 if j + 1 == n else (n - 1 if j == 0 else n - 1 - j)
            if a == 2:
                total += w1
            else:
                total += w2
    return total

bad = {}
for i in range(N):
    c = idx_to_config(i)
    f = fc(c)
    if f > 0:
        bad[i] = {'c': c, 'fc': f, 'tp': tp(c)}

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

# CΦ boundary-fixed steps: fc direction
print("=== CΦ boundary-fixed fc direction ===")
fc_up = 0; fc_down = 0; fc_same = 0

for i in bad:
    c = bad[i]['c']
    for j, p in bad_adj[i]:
        if (future_fc[j] == future_fc[i] and
            bad[j]['tp'] == bad[i]['tp'] and
            phi_full[j] == phi_full[i] and
            boundary6(bad[j]['c']) == boundary6(c)):
            dfc = bad[j]['fc'] - bad[i]['fc']
            if dfc > 0: fc_up += 1
            elif dfc < 0: fc_down += 1
            else: fc_same += 1

print(f"fc increases: {fc_up}")
print(f"fc decreases: {fc_down}")
print(f"fc same: {fc_same}")

# Check: within CΦ boundary-fixed, does (Fc, deepMidHopPotential) or
# (Fc, Psi, sixStateRank, deepMidHopPotential) always decrease?
# If fc always ≤, we can use (Fc, deepMidHopPotential).
if fc_up == 0:
    print("\n*** fc is NON-INCREASING within CΦ boundary-fixed ***")
    print("Can use (sixStateRank, cup2Fc, deepMidHopPotential) as CΦ lex measure")

# Also check ALL CΦ steps (not just boundary-fixed)
print("\n=== ALL CΦ steps: fc direction ===")
all_fc_up = 0; all_fc_down = 0; all_fc_same = 0
for i in bad:
    for j, p in bad_adj[i]:
        if (future_fc[j] == future_fc[i] and
            bad[j]['tp'] == bad[i]['tp'] and
            phi_full[j] == phi_full[i]):
            dfc = bad[j]['fc'] - bad[i]['fc']
            if dfc > 0: all_fc_up += 1
            elif dfc < 0: all_fc_down += 1
            else: all_fc_same += 1

print(f"fc increases: {all_fc_up}")
print(f"fc decreases: {all_fc_down}")
print(f"fc same: {all_fc_same}")

if all_fc_up == 0:
    print("\n*** fc is NON-INCREASING within ALL CΦ steps ***")

print("\nDONE")
