#!/usr/bin/env python3
"""Test 9: Resolve the seeming contradiction.

The bridge analysis showed B0=1, B2=1 for cycles 0-4.
But P0 fires 3 between for other cycles.
Check if the cycles are ordered so that P0>1 cases are later.
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

ms = (2,2,2,3,4); n = 5
cycles = enum_cycles(ms, 200, 30)

# Check which cycles have P0>1 between
for ci, (path, movers, det) in enumerate(cycles):
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    s1, s2 = p1_steps
    between = [movers[s] for s in range(s1+1, s2)]
    p0_b = sum(1 for m in between if m == 0)
    p2_b = sum(1 for m in between if m == 2)
    if p0_b > 1:
        # Check bridges
        bridges = []
        for m in between:
            if m == 0: bridges.append('B0')
            elif m == 2: bridges.append('B2')
        print(f'  Cycle {ci}: P0={p0_b}, P2={p2_b}, bridges={bridges}')
        print(f'    between={between}')
        if ci > 45:
            break

# AH I see -- bridges ARE just the P0 and P2 firings. So bridges=[B0, B0, B0, B2]
# when P0 fires 3 times. My earlier analysis must have been looking at cycles 0-4
# which all had P0=1.

# The parity argument: between P1's firings, P0 fires odd times and P2 fires odd times.
# WHY is the parity odd?

# TOPOLOGICAL ARGUMENT:
# The mover walk on the ring is a path that starts at P1 and ends at P1.
# Consider the binary block as an "interval" [P0, P1, P2] on the ring.
# The two "bridges" connecting binary to non-binary are edges (P0, P_{n-1}) and (P2, P3).
# Each bridge crossing increments the corresponding endpoint's fire count.
#
# The walk from P1 to P1 (between firings) must visit at least one non-binary proc
# (for fairness). To visit non-binary procs, it must cross a bridge.
#
# CLAIM: The walk crosses bridge-0 an ODD number of times and bridge-2 an ODD number
# of times.
#
# PROOF: Consider the walk restricted to binary processors {0,1,2}.
# When the walk is at P1 (start), it goes to P0 (since we observed P0 always fires
# right after P1). Then it crosses bridge-0 (P0 -> P4). Later it returns, possibly
# bouncing. Finally it crosses bridge-2 (P3 -> P2) and reaches P1.
#
# Actually, the parity comes from a simpler observation:
# P0 fires an even number of times in the FULL cycle (since binary, must return to
# initial state, so fires 2k times).
# P0 fires p0_between times between P1's firings, p0_after in the other segment.
# p0_between + p0_after = 2k (even).
# So p0_between and p0_after have the SAME parity.
#
# We need to show p0_between is ODD, which is the same as p0_after is ODD.
#
# But this doesn't directly help. We need another argument.

# Let me try a different approach: count the number of times the walk crosses
# from binary to non-binary territory and back, in each segment.

print('\n=== Crossing parity analysis ===')
# Define: binary territory = {0, 1, 2}, non-binary = {3, ..., n-1}
# A "crossing" happens when consecutive movers are in different territories.
# Between P1's firings, how many crossings?

crossing_count = Counter()
for path, movers, det in cycles:
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    s1, s2 = p1_steps
    between = [movers[s] for s in range(s1+1, s2)]

    crossings = 0
    for i in range(len(between)-1):
        a_bin = between[i] in {0,1,2}
        b_bin = between[i+1] in {0,1,2}
        if a_bin != b_bin:
            crossings += 1

    # Also count the entry/exit at the boundaries
    # The mover before "between" is P1 (binary), first in between could be anything
    first_bin = between[0] in {0,1,2} if between else True
    last_bin = between[-1] in {0,1,2} if between else True

    # Entry: P1 (binary) -> between[0]
    if between and not first_bin:
        crossings += 1  # crossed from binary to non-binary
    # Exit: between[-1] -> P1 (binary)
    if between and not last_bin:
        crossings += 1  # crossed from non-binary to binary

    crossing_count[crossings] += 1

print(f'  Total crossings between P1 firings: {dict(crossing_count)}')

# Each "excursion" into non-binary territory consists of an exit and a return = 2 crossings.
# So total crossings should be even.
# Each excursion through bridge-0 adds 1 to P0's fire count (exit or return via P0).
# Each excursion through bridge-2 adds 1 to P2's fire count.

# Actually an excursion that exits through bridge-0 and returns through bridge-0
# adds 2 to P0's count (exit + return). An excursion that exits through bridge-0
# and returns through bridge-2 adds 1 to each.

# The between segment starts at P1, goes to P0 (always), exits to non-binary,
# and returns through P2 (always, as the last binary step before P1's second firing).
# So at minimum: 1 P0 crossing + 1 P2 crossing.
# Any additional bounces add PAIRS of crossings through the same bridge.
# Each pair adds 2 to that bridge's count, preserving parity.
# So: P0 crossings = 1 + 2k (odd), P2 crossings = 1 + 2j (odd).

print('\n=== Verify: P0 always first, P2 always last ===')
first_last = Counter()
for path, movers, det in cycles:
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    s1, s2 = p1_steps
    # Mover right after P1's first firing
    after_p1 = movers[s1+1] if s1+1 < s2 else movers[(s1+1) % L]
    # Mover right before P1's second firing
    before_p1_2 = movers[s2-1] if s2 > 0 else movers[L-1]
    first_last[(after_p1, before_p1_2)] += 1

print(f'  (after first P1, before second P1): {dict(first_last)}')
