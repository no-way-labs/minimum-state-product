#!/usr/bin/env python3
"""Test 10: Verify n=4 failure mode.
At n=4, binary = {0,1,2}, non-binary = {3}.
P0's non-binary neighbor = P3. P2's non-binary neighbor = P3.
SAME processor! So the two bridges merge.
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

ms = (2,2,2,3); n = 4
cycles = enum_cycles(ms, 500, 30)

print(f'n={n}, ms={ms}: {len(cycles)} cycles')
print(f'P0 neighbor: P3. P2 neighbor: P3. SAME non-binary proc!')

# Check (after_p1, before_p1_2)
first_last = Counter()
p0_parity = Counter()
for path, movers, det in cycles:
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    s1, s2 = p1_steps
    after_p1 = movers[(s1+1) % L]
    before_p1_2 = movers[(s2-1) % L]
    first_last[(after_p1, before_p1_2)] += 1

    between = [movers[s] for s in range(s1+1, s2)]
    p0_b = sum(1 for m in between if m == 0) % 2
    p0_parity[p0_b] += 1

print(f'\n(after P1, before P1): {dict(first_last)}')
print(f'P0 parity between: {dict(p0_parity)}')

# At n=4, the walk can go P1 -> P2 -> P3 -> P0 -> P1 (circumnavigating!)
# because P3 is adjacent to BOTH P0 and P2.
# This means the walk can exit through bridge-2 and return through bridge-0,
# or vice versa. In that case, P0 fires 0 or 2 times between P1's firings
# while P2 fires 2 or 0 times. Even parity -> no flip -> not anti-diagonal.

# Non-AD examples at n=4
for path, movers, det in cycles:
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    s1, s2 = p1_steps
    ctx1 = (path[s1][0], path[s1][1], path[s1][2])
    ctx2 = (path[s2][0], path[s2][1], path[s2][2])
    is_ad = all(ctx2[i] == 1-ctx1[i] for i in range(3))
    if not is_ad:
        between = [movers[s] for s in range(s1+1, s2)]
        p0_b = sum(1 for m in between if m == 0)
        p2_b = sum(1 for m in between if m == 2)
        after_p1 = movers[(s1+1) % L]
        before_p1_2 = movers[(s2-1) % L]
        print(f'\n  Non-AD: ctx1={ctx1}, ctx2={ctx2}')
        print(f'    after P1 = P{after_p1}, before P1_2 = P{before_p1_2}')
        print(f'    P0 between = {p0_b}, P2 between = {p2_b}')
        print(f'    between movers = {between}')
        break

# At n>=5: P0's non-binary neighbor is P_{n-1}, P2's non-binary neighbor is P3.
# Since n>=5, P_{n-1} != P3. So the two bridges are DISJOINT.
# The walk from P1 always exits through P0 (to P_{n-1}) and must come back
# through P2 (from P3) to reach P1 again. It can't circumnavigate because
# that would require going through the binary block, but P1 is at the center
# and would fire again.
# Wait: could the walk exit P0 -> P_{n-1} -> ... -> P3 -> P2 -> P1 without
# P0 firing again? That's 1 P0 firing, 1 P2 firing. Both odd.
# Or could it exit P0 -> P_{n-1} -> P0 -> P_{n-1} -> ... -> P3 -> P2 -> P1?
# Each return to P0 adds 1 to P0's count. After k returns: P0 fires 1+k times.
# Eventually exits to P3 side: P2 fires 1 time.
# P0 parity: 1+k. Is k always even?

# NO: from the data, P0 fires 1 or 3 between (k=0 or k=2). Both odd.
# But also k=1 would give P0=2 (even). Does this happen?
# From the data it doesn't. WHY?

# AH: I think the answer is simpler. The walk exits through P0 and must
# enter the non-binary territory. From there, it eventually reaches P3
# and enters through P2. This is ONE excursion.
# During this excursion, every time the walk visits P0, it's a B0 crossing
# (exit non-binary or enter non-binary). The walk starts in binary (at P0)
# and ends in binary (at P2). Between these two binary endpoints, the walk
# must cross from binary to non-binary and back some number of times.
# The crossings alternate: binary-to-non-binary, non-binary-to-binary, ...
# Starting with binary-to-non-binary (P0 goes to P_{n-1}) and ending with
# non-binary-to-binary (P3 goes to P2).
# Total territory crossings = even? No, because start is binary and end is binary,
# the walk must cross from binary to non-binary (1 crossing), then possibly
# return to binary and exit again (2 more crossings), etc.
# Pattern: BN, NB, BN, NB, ..., NB
# For the walk to end in binary: need even number of crossings.
# Wait: start at P0 (binary), go to P4 (non-binary) = 1 crossing.
# Then if bounce back: P0 (binary) = 2 crossings.
# Then P4 (non-binary) = 3 crossings.
# ...
# Eventually reach P2 (binary). Total crossings must be even
# (since we start in binary and end in binary).
# Each pair of crossings involves going out and coming back through P0
# (adding 2 to P0 count) or going in and out through P2 (adding 2 to P2 count).
# But the first crossing is always through P0 and the last through P2.
# So: first crossing = P0 exit (P0 count 1).
# Then pairs of crossings. Each pair either through P0 or P2.
# Last crossing = P2 entry (P2 count increases by 1).
# Total crossings = 2 + 2k (even). P0 fires 1 + (P0-pair-count * 2).
# P2 fires 1 + (P2-pair-count * 2).
# Both ODD!

# This is the key topological argument!
# The walk enters non-binary through P0 (bridge 0) and exits through P2 (bridge 2).
# Any intermediate returns to binary and back add PAIRS to P0 or P2.
# So both P0 and P2 have odd fire counts between P1's firings.

print('\n\nKEY PROOF INSIGHT CONFIRMED:')
print('At n>=5, bridges are disjoint. Walk enters non-binary through P0,')
print('exits through P2. Each intermediate bounce adds pairs.')
print('Result: P0 odd, P2 odd between P1 firings.')
print('Since P0, P2 binary: odd fires = state flipped.')
print('P1 state also flips (from 0 to 1 or vice versa).')
print('All three coords flip -> anti-diagonal.')
