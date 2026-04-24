#!/usr/bin/env python3
"""Test 14: After-segment structure + parity counting."""
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

# Check the after-segment structure
for n, ms in [(5,(2,2,2,3,4))]:
    cycles = enum_cycles(ms, 200, 30)
    print(f'n={n}, ms={ms}: {len(cycles)} cycles')

    for ci, (path, movers, det) in enumerate(cycles[:5]):
        L = len(path)
        p1_steps = [s for s in range(L) if movers[s] == 1]
        s1, s2 = p1_steps

        between = [movers[s] for s in range(s1+1, s2)]
        after_indices = list(range(s2+1, L)) + list(range(0, s1))
        after = [movers[s] for s in after_indices]

        k0_b = sum(1 for m in between if m == 0)
        k2_b = sum(1 for m in between if m == 2)
        k0_a = sum(1 for m in after if m == 0)
        k2_a = sum(1 for m in after if m == 2)

        print(f'\n  Cycle {ci}: len={L}')
        print(f'    between: {between} (k0={k0_b}, k2={k2_b})')
        print(f'    after:   {after} (k0={k0_a}, k2={k2_a})')
        print(f'    Full movers: {movers}')

    # Summary: parities in both segments
    print('\n  === Parity summary ===')
    parity_between = Counter()
    parity_after = Counter()
    for path, movers, det in cycles:
        L = len(path)
        p1_steps = [s for s in range(L) if movers[s] == 1]
        s1, s2 = p1_steps
        between = [movers[s] for s in range(s1+1, s2)]
        after_indices = list(range(s2+1, L)) + list(range(0, s1))
        after = [movers[s] for s in after_indices]

        k0_b = sum(1 for m in between if m == 0) % 2
        k2_b = sum(1 for m in between if m == 2) % 2
        k0_a = sum(1 for m in after if m == 0) % 2
        k2_a = sum(1 for m in after if m == 2) % 2

        parity_between[(k0_b, k2_b)] += 1
        parity_after[(k0_a, k2_a)] += 1

    print(f'    Between (k0%2, k2%2): {dict(parity_between)}')
    print(f'    After   (k0%2, k2%2): {dict(parity_after)}')

# Also verify: are total fire counts always even for P0, P2?
print('\n=== Total fire count parity ===')
for n, ms in [(5,(2,2,2,3,4))]:
    cycles = enum_cycles(ms, 200, 20)
    for pi in [0, 2]:
        total_parity = Counter()
        for path, movers, det in cycles:
            fc = sum(1 for m in movers if m == pi)
            total_parity[fc % 2] += 1
        print(f'  P{pi} total fire parity: {dict(total_parity)}')

# Key: if total is even and between is odd, then after is also odd.
# This gives anti-diagonal in BOTH segments.
# But do we need this? We only claimed AD for the full cycle,
# and the fire contexts are determined by the (L,S,R) at s1 and s2.
