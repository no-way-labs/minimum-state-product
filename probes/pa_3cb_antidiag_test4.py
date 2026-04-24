#!/usr/bin/env python3
"""Test 4: WHY does P0 fire exactly once between P1's two firings?

Key structural fact: In the mover sequence, consecutive movers must be
ring-adjacent. So when P1 fires, the next mover must be P0 or P2.

Also: P0 total fires = 2 (binary), P1 total fires = 2, P2 total fires = 2.
P0 fires 1 time between P1's firings, 1 time in the other segment.
Same for P2.

Let's understand the mover word structure around P1's firings.
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

# Analyze the mover word structure
ms = (2,2,2,3,3); n = 5
cycles = enum_cycles(ms, 200, 30)

print('=== Mover neighbors of P1 firings ===')
# What fires right before and after P1?
before_after = Counter()
for path, movers, det in cycles:
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    for s in p1_steps:
        prev = movers[(s-1) % L]
        nxt = movers[(s+1) % L]
        before_after[(prev, nxt)] += 1

print('  (before P1, after P1):')
for (b, a), cnt in sorted(before_after.items()):
    print(f'    P{b} -> P1 -> P{a}: {cnt}')

# What's the mover word segment containing binary block?
print('\n=== Binary block mover subsequence ===')
block_patterns = Counter()
for path, movers, det in cycles:
    L = len(path)
    # Extract all steps where mover is in {0,1,2}
    bin_steps = [(s, movers[s]) for s in range(L) if movers[s] in {0,1,2}]
    bin_movers = tuple(m for s, m in bin_steps)
    block_patterns[bin_movers] += 1

print(f'  {len(block_patterns)} distinct binary mover subsequences')
for pat, cnt in sorted(block_patterns.items(), key=lambda x: -x[1])[:15]:
    print(f'    {pat}: {cnt}')

# Check: is the binary block always traversed as a contiguous run?
print('\n=== Contiguous binary traversals ===')
# Extract runs of consecutive binary movers
for ci, (path, movers, det) in enumerate(cycles[:5]):
    L = len(path)
    print(f'  Cycle {ci}: movers={movers}')
    runs = []
    current = []
    for s in range(L):
        if movers[s] in {0,1,2}:
            current.append((s, movers[s]))
        else:
            if current:
                runs.append(current)
                current = []
    if current:
        runs.append(current)
    print(f'    Binary runs: {[[m for _,m in r] for r in runs]}')

# Key question: can P1 fire without P0 or P2 firing adjacent to it?
print('\n=== P1 immediate predecessor/successor ===')
# We know consecutive movers are ring-adjacent.
# P1's ring neighbors are P0 and P2.
# So the mover before P1 must be P0 or P2, and same for after.
# This means P1 is always "sandwiched" in the mover word by P0/P2.

# Between P1's two firings, BOTH P0 and P2 must fire (each binary fires 2x total).
# If P0 fires 1x between and 1x after, and P2 fires 1x between and 1x after,
# then L and R both flip between firings -> anti-diagonal.

# WHY must each fire exactly 1x between (not 0 or 2)?

# If P0 fires 0 between, it fires 2 after. But P0 is binary, so 2 firings = identity.
# That means c[0] doesn't change net between P1's firings.
# But P1's state DID change (0->1 or 1->0).
# The context went from (a,0,c) to (a,1,c') or vice versa.
# For P1 to fire again, it needs a mover context. If a didn't change...
# Actually there's no contradiction yet. Let's check directly.

# At n=4 (where AD fails), check if P0/P2 can fire 0 times between
ms4 = (2,2,2,3); n4 = 4
cycles4 = enum_cycles(ms4, 500, 30)
p0_between4 = Counter()
p2_between4 = Counter()
ad4 = 0; non_ad4 = 0
for path, movers, det in cycles4:
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    s1, s2 = p1_steps
    between = [movers[s] for s in range(s1+1, s2)]
    p0_b = sum(1 for m in between if m == 0)
    p2_b = sum(1 for m in between if m == 2)
    p0_between4[p0_b] += 1
    p2_between4[p2_b] += 1

    ctx1 = (path[s1][0], path[s1][1], path[s1][2])
    ctx2 = (path[s2][0], path[s2][1], path[s2][2])
    is_ad = all(ctx2[i] == 1-ctx1[i] for i in range(3))
    if is_ad: ad4 += 1
    else: non_ad4 += 1

print(f'\nn=4: P0 between = {dict(p0_between4)}, P2 between = {dict(p2_between4)}')
print(f'n=4: AD={ad4}, non-AD={non_ad4}')

# Cross-tab: P0_between vs AD status
print('\n=== n=4: P0_between x P2_between vs AD ===')
cross = Counter()
for path, movers, det in cycles4:
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    s1, s2 = p1_steps
    between = [movers[s] for s in range(s1+1, s2)]
    p0_b = sum(1 for m in between if m == 0)
    p2_b = sum(1 for m in between if m == 2)

    ctx1 = (path[s1][0], path[s1][1], path[s1][2])
    ctx2 = (path[s2][0], path[s2][1], path[s2][2])
    is_ad = all(ctx2[i] == 1-ctx1[i] for i in range(3))
    cross[(p0_b, p2_b, is_ad)] += 1

for (p0, p2, ad), cnt in sorted(cross.items()):
    print(f'  P0={p0}, P2={p2}, AD={ad}: {cnt}')
