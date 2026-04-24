#!/usr/bin/env python3
"""Debug 4: Check the forward non-AD cycles at n=5, ms=(2,2,2,3,3)."""
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

ms = (2,2,2,3,3); n = 5
cycles = enum_cycles(ms, 500, 60)

print('Forward non-AD cycles:')
for ci, (path, movers, det) in enumerate(cycles):
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    if len(p1_steps) != 2: continue
    s1, s2 = p1_steps
    next_m = movers[(s1+1) % L]
    if next_m != 0: continue  # forward only

    ctx1 = (path[s1][0], path[s1][1], path[s1][2])
    ctx2 = (path[s2][0], path[s2][1], path[s2][2])
    is_ad = all(ctx2[i] == 1-ctx1[i] for i in range(3))
    if not is_ad:
        between = [movers[s] for s in range(s1+1, s2)]
        k0 = sum(1 for m in between if m == 0)
        k2 = sum(1 for m in between if m == 2)
        prev_m = movers[(s2-1) % L]

        print(f'\n  Cycle {ci}: ctx1={ctx1}, ctx2={ctx2}')
        print(f'    movers={movers}')
        print(f'    P1 steps: {s1}, {s2}')
        print(f'    w_{{s1+1}}=P{next_m}, w_{{s2-1}}=P{prev_m}')
        print(f'    between: {between}')
        print(f'    k0={k0}, k2={k2}, parity=({k0%2},{k2%2})')

        # Crossings
        crossings = []
        for m in between:
            if m == 0: crossings.append('B0')
            elif m == 2: crossings.append('B2')
        print(f'    crossings: {crossings}')
