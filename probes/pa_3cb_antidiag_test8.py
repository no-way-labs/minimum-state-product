#!/usr/bin/env python3
"""Test 8: Parity argument from ring topology.

The mover word is a walk on the ring graph where consecutive movers
are ring-adjacent.

KEY INSIGHT: Consider the walk restricted to the edge (P0, P_{n-1}).
Each time the walk crosses this edge (in either direction), P0 fires once
(either P0 fires going from binary to non-binary, or returning).

Between P1's two firings, the walk starts at P1 and ends at P1.
It must cross from the binary block to the non-binary block and back.
The number of times it crosses the edge (P0, P_{n-1}) between the two
P1 firings equals the number of times P0 fires in that segment.

Similarly, it crosses the edge (P2, P3) some number of times.

For n >= 5, the two edges (P0, P_{n-1}) and (P2, P3) are the ONLY
connections between the binary block and the non-binary block.

The walk from P1 to P1 (between firings) must exit and re-enter the
binary block. Each exit-and-return uses one of the two bridges.

Does the walk always exit through one bridge and return through the other?
Or can it exit and return through the same bridge?
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

# For the between-segment walk, track bridge crossings
ms = (2,2,2,3,4); n = 5
cycles = enum_cycles(ms, 200, 30)

print('=== Bridge crossing analysis ===')
print(f'n={n}, ms={ms}')
print(f'Binary block: {{P0,P1,P2}}')
print(f'Bridge 0: edge (P0, P4)')
print(f'Bridge 2: edge (P2, P3)')

cross_pattern = Counter()
for path, movers, det in cycles:
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    s1, s2 = p1_steps

    # Between segment
    between = [movers[s] for s in range(s1+1, s2)]

    # Count bridge crossings
    # Bridge 0 crossing: step where mover is P0 and prev was P4, or P4 and prev was P0
    # But actually P0 fires = crosses bridge 0 once (either entering or leaving binary block)
    p0_cross = sum(1 for m in between if m == 0)
    p2_cross = sum(1 for m in between if m == 2)

    cross_pattern[(p0_cross % 2, p2_cross % 2)] += 1

print(f'\n(P0_parity, P2_parity) between: {dict(cross_pattern)}')

# Now the KEY: what's the relationship between P0 crossings and P2 crossings?
# Between P1's firings, the walk goes from P1 to some non-binary procs and back to P1.
# The walk enters non-binary territory through P0 (bridge 0) or P2 (bridge 2).
# Each entry through bridge 0 means P0 fires. Each entry through bridge 2 means P2 fires.

# Track the exact bridge sequence
print('\n=== Bridge sequence between P1 firings ===')
for ci, (path, movers, det) in enumerate(cycles[:5]):
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    s1, s2 = p1_steps
    between = [movers[s] for s in range(s1+1, s2)]

    bridges = []
    for m in between:
        if m == 0:
            bridges.append('B0')
        elif m == 2:
            bridges.append('B2')

    print(f'  Cycle {ci}: bridges = {bridges}, P0={between.count(0)}, P2={between.count(2)}')

# KEY OBSERVATION: The walk starts at P1 after P1 fires (step s1).
# The NEXT mover after P1 must be P0 or P2 (adjacency).
# The PREVIOUS mover before P1's second firing must be P0 or P2.
# From the data, it's always P0 after P1 (first), P2 before P1 (second).

# Between the two P1 firings: walk goes P1 -> P0 -> ... -> P2 -> P1.
# It exits through bridge 0 and enters through bridge 2.
# That's 1 bridge-0 crossing (P0 fires), then possibly bounces,
# then 1 bridge-2 crossing (P2 fires).

# The bounce pattern: 0, 4, 0, 4, 0, ... -> each return to P0 through bridge 0
# adds another P0 firing. But eventually the walk must reach P2 to re-enter the
# binary block.

# For n >= 5, the non-binary path from P4 to P3 goes through P4, ..., P3.
# At n=5, the only non-binary procs are P3 and P4. The path P4 -> P3 is direct.
# So the walk goes: P0, P4, ..., P3, P2.
# Every time P0 bounces (P0, P4, P0), it adds 2 to P0's count (1 exit + 1 return).
# Base: P0 fires once (initial exit through bridge 0).
# Each bounce adds 2 (but waits -- from the data, bounces add individual firings).

# Actually let me reconsider. The walk after P1's first firing:
# Step s1+1: P0 fires (bridge 0 exit, P0 count = 1)
# Then the walk goes to P4. If it goes to P3 and then P2, done: P0=1, P2=1.
# If instead from P4 it bounces back to P0: P0 fires again (count = 2).
# Then from P0 back to P4: P0 fires again? No -- the mover goes to P4, not P0.
# Wait, the mover at step s1+1 is P0. Next mover is P4. Then next can be P0 or P3.
# If P0: P0 fires (count = 2). Then next is P4. etc.
# If P3: walk proceeds toward P2.

# Pattern: P0, (P4, P0)^k, P4, ..., P3, P2
# P0 fires 1 + k times. For k=0: P0=1. For k=2: P0=3. For k=4: P0=5.
# Always odd! Because: initial 1 + even number of bounces.

# Wait, from the data, P0 fires 3 between (not 1+2k for k integer).
# Let me recount. Pattern: P0, P4, P0, P4, P0, P4, P3, P2
# P0 count: 3 (at positions 0, 2, 4). That's 1 + 2*1 = 3. k=1 bounce pair.

# AH: each "bounce" is: after initial P0, the walk goes P4, P0, P4, P0, ...
# Each pair (P4, P0) adds 1 to P0 count.
# Total P0 = 1 + (number of P4->P0 returns).
# But: the walk alternates P0, P4, P0, P4, ...
# Starting from P0 (first exit), the walk is: P4, P0, P4, P0, ..., P4, P3, P2
# So after the first P0: we see (P4, P0) repeated some number of times, then P4, P3, P2.
# P0 count = 1 + (number of P4->P0 returns) = 1 + (number of extra P0 firings).

# If 0 returns: P0, P4, ..., P3, P2. P0 fires 1 time.
# If 1 return: P0, P4, P0, P4, ..., P3, P2. P0 fires 2 times.
# If 2 returns: P0, P4, P0, P4, P0, P4, ..., P3, P2. P0 fires 3 times.

# Hmm, that gives 1, 2, 3, ... -- not always odd!
# But the data shows always odd (1, 3, 5). Why?

# The P0, P4 subsequences from data:
# [0, 4, 0, 4, 0, 4] -> P0 fires 3 times.
# Pattern: 0, 4, 0, 4, 0, 4 (then 3, 2)
# This is P0, P4, P0, P4, P0, P4 -- the walk ends at P4, then goes to P3, P2.
# So the walk leaves through P0 and ends at P4.
# P0 fires 3 times, P4 fires 3 times in this segment.

# From P4 (after last P0 bounce), the walk goes to P3, then P2.
# So the bridge-2 crossing is P3 -> P2 -> P1.

# Now I see: the walk pattern through bridge 0 is always:
# P0, P4, P0, P4, ..., P0, P4 (alternating, starting and ending with...)
# Actually from data: [0, 4, 0, 4, 0, 4, 4, 4] at n=5
# After the P0-P4 bouncing, the walk continues through P4 to P3.
# So last element is P4, meaning walk exits through bridge 0 at P4's side.

# The key: from P1, the walk goes to P0 (bridge 0), then bounces between P0 and P4.
# At some point, from P4, instead of going to P0, it goes to P3, then to P2 (bridge 2),
# then to P1.

# So the walk crosses bridge 0 by visiting P0: happens at positions 0, 2, 4, ...
# The number of P0 visits = ceil(length of P0-P4 alternation / 2).
# If alternation length is 2k: P0 visits = k. If 2k+1: P0 visits = k+1.
# But from data, alternation is always even length? Let me check.

for ci, (path, movers, det) in enumerate(cycles[:40]):
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    s1, s2 = p1_steps
    between = [movers[s] for s in range(s1+1, s2)]

    p0_count = sum(1 for m in between if m == 0)
    p2_count = sum(1 for m in between if m == 2)

    # Find P0-P4 alternation
    alt = []
    for m in between:
        if m in (0, 4):
            alt.append(m)
        elif alt and alt[-1] in (0, 4):
            break  # left the P0-P4 zone

    if p0_count > 1 and ci < 5:
        print(f'\n  Cycle {ci}: between={between}')
        print(f'    P0-P4 alternation: {alt}')
        print(f'    P0 fires {p0_count}, P2 fires {p2_count}')
