#!/usr/bin/env python3
"""Compare current SixTuple.lean edges with correct CΦ edges."""
import re, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import build_system
from collections import defaultdict

# Extract edges from current file
with open('LeanMn/Convergence/SixTuple.lean') as f:
    content = f.read()
start = content.find('def sixTupleEdgeVals')
end = content.find(']', start)
chunk = content[start:end+1]
edges_current = set()
for m in re.finditer(r'\((\d+),\s*(\d+)\)', chunk):
    edges_current.add((int(m.group(1)), int(m.group(2))))

# Compute correct edges
n = 9; ms, fs = build_system(n); N = 1
for m in ms: N *= m
def idc(idx):
    c = []
    for m in reversed(ms): c.append(idx % m); idx //= m
    return tuple(reversed(c))
def cdi(c):
    idx = 0
    for j in range(n): idx = idx * ms[j] + c[j]
    return idx
def mv(c, pos):
    L = c[(pos-1)%n]; S = c[pos]; R = c[(pos+1)%n]
    c2 = list(c); c2[pos] = fs[pos](L, S, R); return tuple(c2)
def fcc(c): return sum(1 for j in range(n) if c[j] != c[(j+1)%n])
def tpp(c):
    e = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
    i21 = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n]==1)
    w = sum(j for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
    return (e, i21, w)
def b6(c): return ((((c[0]*3+c[1])*3+c[2])*3+c[n-3])*3+c[n-2])*2+c[n-1]

bad = set(); tpa = {}
for i in range(N):
    if fcc(idc(i)) > 0: bad.add(i); tpa[i] = []
for i in bad:
    c = idc(i); t = tpp(c)
    for p in range(n):
        c2 = mv(c, p); j = cdi(c2)
        if c2 != c and j in bad and tpp(c2) == t: tpa[i].append(j)
pf = {i: fcc(idc(i)) for i in bad}
rev = {i: [] for i in bad}
for i in bad:
    for j in tpa[i]: rev[j].append(i)
ch = True
while ch:
    ch = False
    for j in bad:
        for i in rev[j]:
            if pf[j] > pf[i]: pf[i] = pf[j]; ch = True
ff = {i: fcc(idc(i)) for i in bad}
aa = {i: [] for i in bad}
for i in bad:
    c = idc(i)
    for p in range(n):
        c2 = mv(c, p); j = cdi(c2)
        if c2 != c and j in bad: aa[i].append(j)
ar = {i: [] for i in bad}
for i in bad:
    for j in aa[i]: ar[j].append(i)
ch = True
while ch:
    ch = False
    for j in bad:
        for i in ar[j]:
            if ff[j] > ff[i]: ff[i] = ff[j]; ch = True

correct = set()
for i in bad:
    for j in tpa[i]:
        if ff[j] == ff[i] and pf[j] == pf[i]:
            c, c2 = idc(i), idc(j)
            b1, b2 = b6(c), b6(c2)
            if b1 != b2: correct.add((b1, b2))

print(f"Current edges: {len(edges_current)}")
print(f"Correct edges: {len(correct)}")
print(f"Match: {edges_current == correct}")
diff1 = sorted(edges_current - correct)
diff2 = sorted(correct - edges_current)
if diff1: print(f"In current only ({len(diff1)}): {diff1[:10]}")
if diff2: print(f"In correct only ({len(diff2)}): {diff2[:10]}")
