#!/usr/bin/env python3
"""Test 13: Check for B2 bounces in the between-segment.
With P1 blocking: P0 can only exit through B0. P2 can only exit through B2.
The walk can bounce at either endpoint.

The full crossing sequence between P1's firings:
Start at P0. Mandatory exit through B0.
Non-binary territory. Can reach P0 (return through B0) or P2 (enter through B2).
If at P0: mandatory exit through B0 (B0 bounce).
If at P2: mandatory exit through B2 (to P3).
Then from P3 side, can reach P0 (through B0) or P2 (through B2).
...
Must end at P2 (before P1's second firing).
Last step: P2 fires (entering from P3).

So the walk is a sequence of B0 bounces and B2 bounces,
with the constraint that it starts with a B0 exit and ends with a B2 entry.

Between B0 bounces and B2 bounces, the walk traverses non-binary territory
from one bridge to the other.

Let me track the full crossing sequence.
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

# At n=6 with more non-binary procs, check for B2 bounces
for n, ms in [(5,(2,2,2,3,4)), (6,(2,2,2,3,3,3))]:
    cycles = enum_cycles(ms, 200, 20)
    print(f'\nn={n}, ms={ms}: {len(cycles)} cycles')

    for ci, (path, movers, det) in enumerate(cycles):
        L = len(path)
        p1_steps = [s for s in range(L) if movers[s] == 1]
        s1, s2 = p1_steps
        between = [movers[s] for s in range(s1+1, s2)]

        p0_b = sum(1 for m in between if m == 0)
        p2_b = sum(1 for m in between if m == 2)

        if p2_b > 1:
            print(f'  B2 BOUNCE! Cycle {ci}: P0={p0_b}, P2={p2_b}, between={between}')
            if ci > 10:
                break

    # Summary
    p0_dist = Counter()
    p2_dist = Counter()
    for path, movers, det in cycles:
        L = len(path)
        p1_steps = [s for s in range(L) if movers[s] == 1]
        s1, s2 = p1_steps
        between = [movers[s] for s in range(s1+1, s2)]
        p0_b = sum(1 for m in between if m == 0)
        p2_b = sum(1 for m in between if m == 2)
        p0_dist[p0_b] += 1
        p2_dist[p2_b] += 1

    print(f'  P0 between dist: {dict(sorted(p0_dist.items()))}')
    print(f'  P2 between dist: {dict(sorted(p2_dist.items()))}')

# Also check n=7 with larger non-binary block
for n, ms in [(7, (2,2,2,3,3,3,3))]:
    cycles = enum_cycles(ms, 100, 30)
    print(f'\nn={n}, ms={ms}: {len(cycles)} cycles')
    p2_max = 0
    for path, movers, det in cycles:
        L = len(path)
        p1_steps = [s for s in range(L) if movers[s] == 1]
        if len(p1_steps) != 2:
            print(f'  P1 fires {len(p1_steps)} times!')
            continue
        s1, s2 = p1_steps
        between = [movers[s] for s in range(s1+1, s2)]
        p2_b = sum(1 for m in between if m == 2)
        if p2_b > p2_max:
            p2_max = p2_b

    print(f'  Max P2 between = {p2_max}')

    p0_dist = Counter()
    p2_dist = Counter()
    parity = Counter()
    for path, movers, det in cycles:
        L = len(path)
        p1_steps = [s for s in range(L) if movers[s] == 1]
        if len(p1_steps) != 2: continue
        s1, s2 = p1_steps
        between = [movers[s] for s in range(s1+1, s2)]
        p0_b = sum(1 for m in between if m == 0)
        p2_b = sum(1 for m in between if m == 2)
        p0_dist[p0_b] += 1
        p2_dist[p2_b] += 1
        parity[(p0_b%2, p2_b%2)] += 1

    print(f'  P0 between: {dict(sorted(p0_dist.items()))}')
    print(f'  P2 between: {dict(sorted(p2_dist.items()))}')
    print(f'  Parity: {dict(sorted(parity.items()))}')
