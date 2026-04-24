#!/usr/bin/env python3
"""Check: within constant-TP, is Φ_full determined by the 6-tuple?"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import build_system
from collections import defaultdict

n = 9; ms, fs = build_system(n); N = 1
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
    c2 = list(c); c2[pos] = fs[pos](L, S, R); return tuple(c2)
def fc(c): return sum(1 for j in range(n) if c[j] != c[(j+1)%n])
def tp(c):
    e = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
    i21 = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n]==1)
    w = sum(j for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
    return (e, i21, w)
def boundary6(c): return ((((c[0]*3+c[1])*3+c[2])*3+c[n-3])*3+c[n-2])*2+c[n-1]

bad = {}
for i in range(N):
    c = idx_to_config(i)
    f = fc(c)
    if f > 0: bad[i] = {'c': c, 'fc': f, 'tp': tp(c)}

tp_adj = {i: [] for i in bad}
for i in bad:
    c = bad[i]['c']
    for p in range(n):
        c2 = move(c, p)
        if c2 == c: continue
        j = config_to_idx(c2)
        if j in bad and bad[j]['tp'] == bad[i]['tp']:
            tp_adj[i].append(j)

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

# Group by (6-tuple, TP) and check Φ_full variation
groups = defaultdict(set)
for i in bad:
    c = bad[i]['c']
    key = (boundary6(c), bad[i]['tp'])
    groups[key].add(phi_full[i])

multi = sum(1 for v in groups.values() if len(v) > 1)
print(f"Groups (6-tuple, TP): {len(groups)}")
print(f"Groups with multiple Φ_full values: {multi}")

if multi == 0:
    print("\n*** Φ_full IS determined by (6-tuple, TP) ***")
    print("This means the bridge theorem can be checked at the 6-tuple level!")
else:
    print(f"\nΦ_full varies within (6-tuple, TP) for {multi} groups")
    for k, v in sorted(groups.items()):
        if len(v) > 1:
            print(f"  6tuple={k[0]}, TP={k[1]}: Φ_full values = {sorted(v)}")

print("\nDONE")
