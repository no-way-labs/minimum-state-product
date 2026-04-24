#!/usr/bin/env python3
"""Test 3: Deep structural analysis for proof.

Key questions:
1. WHY does P1 fire exactly 2 times? (context counting)
2. WHY is the pattern anti-diagonal for n>=5?
3. What role does the "different non-binary neighbors" play?

For the fire count: P1 is binary (m_1=2), fires from state 0 and state 1.
The 4 possible (L,R) contexts are (0,0),(0,1),(1,0),(1,1).
P1 fires on exactly 2 contexts (one per state).

For anti-diagonal: The claim is that if P1 fires on (a,0,c), it also fires
on (1-a,1,1-c). Both L=c[0] and R=c[2] flip.

Hypothesis: The mover sequence constrains when P1 can fire. Between P1's
two firings, certain processors must fire, and their firings flip the
neighboring binary states.
"""
from itertools import product as iproduct
from collections import Counter

def enum_cycles(ms, max_cycles=500, max_time=30):
    import time
    n = len(ms)
    t0 = time.time()
    all_configs = list(iproduct(*[range(m) for m in ms]))
    cycles = []
    for start in all_configs:
        if time.time() - t0 > max_time: break
        stack = [(start, [start], {}, [])]
        nodes = 0
        while stack and nodes < 100000:
            if time.time() - t0 > max_time: break
            nodes += 1
            config, path, det, movers = stack.pop()
            for p in range(n):
                for nv in range(ms[p]):
                    if nv == config[p]: continue
                    if movers:
                        d = min(abs(p-movers[-1]), n-abs(p-movers[-1]))
                        if d > 1: continue
                    L,S,R = config[(p-1)%n], config[p], config[(p+1)%n]
                    nd = dict(det); ok = True
                    km = (p,L,S,R)
                    if km in nd:
                        if nd[km] != nv: ok = False
                    else: nd[km] = nv
                    if not ok: continue
                    for i in range(n):
                        if i == p: continue
                        Li,Si,Ri = config[(i-1)%n], config[i], config[(i+1)%n]
                        ki = (i,Li,Si,Ri)
                        if ki in nd:
                            if nd[ki] != Si: ok = False; break
                        else: nd[ki] = Si
                    if not ok: continue
                    nc = list(config); nc[p] = nv; nc = tuple(nc)
                    if nc == start and len(path) >= n:
                        fired = set(movers + [p])
                        if fired == set(range(n)):
                            fm = movers + [p]
                            me_ok = True
                            for idx in range(len(path)):
                                c = path[idx]; priv = []
                                for i in range(n):
                                    ki = (i,c[(i-1)%n],c[i],c[(i+1)%n])
                                    if ki in nd and nd[ki] != c[i]: priv.append(i)
                                if len(priv) != 1: me_ok = False; break
                            if me_ok:
                                cycles.append((path, fm, nd))
                                if len(cycles) >= max_cycles: return cycles
                        continue
                    if nc not in set(path) and len(path) < 6*n:
                        stack.append((nc, path+[nc], nd, movers+[p]))
    return cycles

# For n=5: analyze what happens between P1's two firings
ms = (2,2,2,3,3); n = 5
cycles = enum_cycles(ms, 200, 30)
print(f'n={n}, ms={ms}: {len(cycles)} cycles')

print('\n=== Between P1 firings ===')
for ci, (path, movers, det) in enumerate(cycles[:10]):
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    assert len(p1_steps) == 2
    s1, s2 = p1_steps

    # What happens between s1 and s2?
    between = []
    for s in range(s1+1, s2):
        between.append(movers[s])
    # What happens between s2 and s1 (wrapping)?
    after = []
    for s in list(range(s2+1, L)) + list(range(0, s1)):
        after.append(movers[s])

    c_at_s1 = path[s1]
    c_at_s2 = path[s2]

    ctx1 = (c_at_s1[0], c_at_s1[1], c_at_s1[2])
    ctx2 = (c_at_s2[0], c_at_s2[1], c_at_s2[2])

    # How many times does each binary proc fire in each segment?
    p0_between = sum(1 for m in between if m == 0)
    p2_between = sum(1 for m in between if m == 2)
    p0_after = sum(1 for m in after if m == 0)
    p2_after = sum(1 for m in after if m == 2)

    print(f'  Cycle {ci}: P1 fires at steps {s1},{s2}')
    print(f'    ctx1={ctx1}, ctx2={ctx2}')
    print(f'    Between: movers={between}')
    print(f'    P0 fires {p0_between}x between, {p0_after}x after')
    print(f'    P2 fires {p2_between}x between, {p2_after}x after')

# Key: how many times does P0 fire between P1's two firings?
print('\n=== P0, P2 fire parity between P1 firings ===')
p0_between_dist = Counter()
p2_between_dist = Counter()
for path, movers, det in cycles:
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    s1, s2 = p1_steps
    between = [movers[s] for s in range(s1+1, s2)]
    p0_b = sum(1 for m in between if m == 0)
    p2_b = sum(1 for m in between if m == 2)
    p0_between_dist[p0_b] += 1
    p2_between_dist[p2_b] += 1

print(f'  P0 fires between P1 firings: {dict(p0_between_dist)}')
print(f'  P2 fires between P1 firings: {dict(p2_between_dist)}')

# Check: is exactly one of {P0,P2} odd between, one even?
print('\n=== P0 parity + P2 parity between P1 firings ===')
parity_dist = Counter()
for path, movers, det in cycles:
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    s1, s2 = p1_steps
    between = [movers[s] for s in range(s1+1, s2)]
    p0_b = sum(1 for m in between if m == 0) % 2
    p2_b = sum(1 for m in between if m == 2) % 2
    parity_dist[(p0_b, p2_b)] += 1

print(f'  (P0_parity, P2_parity) between: {dict(parity_dist)}')
# If both odd: both L and R flip -> anti-diagonal
# If both even: neither flips -> same context (impossible, state changed)
# If one odd one even: one flips, one doesn't

# Also check: total fire counts (full cycle)
print('\n=== Total fire parities ===')
total_parity = Counter()
for path, movers, det in cycles:
    p0_total = sum(1 for m in movers if m == 0) % 2
    p2_total = sum(1 for m in movers if m == 2) % 2
    total_parity[(p0_total, p2_total)] += 1
print(f'  (P0_total%2, P2_total%2): {dict(total_parity)}')
