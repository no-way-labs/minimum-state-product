#!/usr/bin/env python3
"""Test 15: Verify the paired crossing structure directly.

For each between-segment, extract the crossing sequence and verify that
paired crossings (C_2=C_3, C_4=C_5, ...) are same-type.
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


for n, ms in [(5,(2,2,2,3,4)), (5,(2,2,2,3,3)), (6,(2,2,2,3,3,3))]:
    cycles = enum_cycles(ms, 200, 20)
    print(f'\nn={n}, ms={ms}: {len(cycles)} cycles')

    pairing_ok = 0
    pairing_fail = 0

    for path, movers, det in cycles:
        L = len(path)
        p1_steps = [s for s in range(L) if movers[s] == 1]
        if len(p1_steps) != 2: continue
        s1, s2 = p1_steps
        between = [movers[s] for s in range(s1+1, s2)]

        # Extract crossing sequence
        crossings = []
        for m in between:
            if m == 0:
                crossings.append('B0')
            elif m == 2:
                crossings.append('B2')

        # Verify: C_1 = B0, C_q = B2
        if not crossings or crossings[0] != 'B0' or crossings[-1] != 'B2':
            print(f'  FAIL: crossings don\'t start B0 or end B2: {crossings}')
            continue

        # Verify: even number of crossings
        q = len(crossings)
        if q % 2 != 0:
            print(f'  FAIL: odd number of crossings: {q}, {crossings}')
            continue

        # Verify: pairs (C_2, C_3), (C_4, C_5), ... are same-type
        ok = True
        for i in range(1, q-1, 2):
            if crossings[i] != crossings[i+1]:
                print(f'  FAIL: pair ({crossings[i]}, {crossings[i+1]}) at positions {i},{i+1}')
                ok = False
                break

        if ok:
            pairing_ok += 1
        else:
            pairing_fail += 1

    print(f'  Pairing OK: {pairing_ok}, FAIL: {pairing_fail}')

# Also check n=4 (should have failures due to merged bridges)
ms4 = (2,2,2,3); n4 = 4
cycles4 = enum_cycles(ms4, 500, 30)
print(f'\nn={n4}, ms={ms4}: {len(cycles4)} cycles')

pairing_ok4 = 0; pairing_fail4 = 0; wrong_start = 0
for path, movers, det in cycles4:
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    if len(p1_steps) != 2: continue
    s1, s2 = p1_steps
    between = [movers[s] for s in range(s1+1, s2)]
    crossings = []
    for m in between:
        if m == 0: crossings.append('B0')
        elif m == 2: crossings.append('B2')

    if not crossings:
        continue
    if crossings[0] != 'B0' or crossings[-1] != 'B2':
        wrong_start += 1
        continue

    q = len(crossings)
    if q % 2 != 0:
        pairing_fail4 += 1
        continue

    ok = True
    for i in range(1, q-1, 2):
        if crossings[i] != crossings[i+1]:
            ok = False
            break

    if ok: pairing_ok4 += 1
    else: pairing_fail4 += 1

print(f'  Pairing OK: {pairing_ok4}, FAIL: {pairing_fail4}, Wrong start/end: {wrong_start}')
