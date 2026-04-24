#!/usr/bin/env python3
"""Debug 3: Under what conditions does AD hold?

From verification:
- n=4, ms=(2,2,2,3): FAILS (86% AD)
- n=5, ms=(2,2,2,3,3): FAILS (98% AD, 6 non-AD)
- n=5, ms=(2,2,2,3,4): PASSES (100% AD)
- n=5, ms=(2,2,2,4,3): PASSES (100% AD)
- n=5, ms=(2,2,2,4,4): PASSES (100% AD)
- n=6, ms=(2,2,2,3,3,3): PASSES (100% AD)
- n=7, ms=(2,2,2,3,3,3,3): PASSES (100% AD)

The non-AD cases at n=5 with (2,2,2,3,3) have a reversed direction
(P2 first, P0 last). This only happens when the two non-binary neighbors
have the same modulus (both 3) AND n=5 (only 2 non-binary procs).

Hypothesis: AD holds whenever:
1. n >= 6 (enough non-binary procs to enforce directional consistency), OR
2. n = 5 and the two non-binary neighbors have DIFFERENT moduli.

Or more precisely: AD holds when the walk direction through the binary
block is forced to be consistent (always the same direction).

Let me check: at n=5, ms=(2,2,2,3,3), do the non-AD cycles have a
reversed direction? And why doesn't reversal happen with (2,2,2,3,4)?
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

# Analyze direction and AD relationship at n=5
for ms in [(2,2,2,3,3), (2,2,2,3,4), (2,2,2,4,3)]:
    n = 5
    cycles = enum_cycles(ms, 500, 30)

    dir_ad = Counter()
    for path, movers, det in cycles:
        L = len(path)
        p1_steps = [s for s in range(L) if movers[s] == 1]
        if len(p1_steps) != 2: continue
        s1, s2 = p1_steps

        # Direction: which side does the walk exit first?
        next_m = movers[(s1+1) % L]
        direction = 'P0_first' if next_m == 0 else 'P2_first' if next_m == 2 else 'other'

        # AD check
        ctx1 = (path[s1][0], path[s1][1], path[s1][2])
        ctx2 = (path[s2][0], path[s2][1], path[s2][2])
        is_ad = all(ctx2[i] == 1-ctx1[i] for i in range(3))

        dir_ad[(direction, is_ad)] += 1

    print(f'\nn=5, ms={ms}: {len(cycles)} cycles')
    for (d, ad), cnt in sorted(dir_ad.items()):
        print(f'  {d}, AD={ad}: {cnt}')

# Now check: does the walk direction depend on the mover word structure?
# At n=5, ms=(2,2,2,3,3): both non-binary procs are P3 and P4 with m=3.
# The walk can go either P0->P4->P3->P2 or P2->P3->P4->P0.
# With symmetric non-binary moduli, both directions are equally valid.

# At n=5, ms=(2,2,2,3,4): P3 has m=3, P4 has m=4.
# The walk prefers one direction (always P0 first).
# Why? Because P4 (with m=4) needs more firings, so the walk spends
# more time on that side, creating an asymmetry.

# Actually: let me check if reversed direction at (2,2,2,3,3) always gives non-AD
# OR if some reversed cycles are still AD.

ms_sym = (2,2,2,3,3)
cycles_sym = enum_cycles(ms_sym, 500, 30)
print(f'\nn=5, ms={ms_sym}: detailed direction analysis')

reversed_ad = 0; reversed_nonad = 0; forward_ad = 0
for path, movers, det in cycles_sym:
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    if len(p1_steps) != 2: continue
    s1, s2 = p1_steps
    next_m = movers[(s1+1) % L]
    ctx1 = (path[s1][0], path[s1][1], path[s1][2])
    ctx2 = (path[s2][0], path[s2][1], path[s2][2])
    is_ad = all(ctx2[i] == 1-ctx1[i] for i in range(3))

    if next_m == 2:  # reversed
        if is_ad: reversed_ad += 1
        else: reversed_nonad += 1
    elif next_m == 0:
        forward_ad += 1  # always AD for forward

print(f'  Forward (P0 first): {forward_ad} AD')
print(f'  Reversed (P2 first): {reversed_ad} AD, {reversed_nonad} non-AD')

# So the key question: WHY do some reversed-direction cycles still have AD?
# Because even with reversed direction, the parity can STILL be (odd, odd)
# if P2 bounces an odd number of times.

# Let me check the parity distribution for reversed cycles
print('\n  Reversed cycles parity:')
for path, movers, det in cycles_sym:
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    if len(p1_steps) != 2: continue
    s1, s2 = p1_steps
    next_m = movers[(s1+1) % L]
    if next_m != 2: continue

    between = [movers[s] for s in range(s1+1, s2)]
    k0 = sum(1 for m in between if m == 0)
    k2 = sum(1 for m in between if m == 2)

    ctx1 = (path[s1][0], path[s1][1], path[s1][2])
    ctx2 = (path[s2][0], path[s2][1], path[s2][2])
    is_ad = all(ctx2[i] == 1-ctx1[i] for i in range(3))
    print(f'    k0={k0}, k2={k2}, parity=({k0%2},{k2%2}), AD={is_ad}')
