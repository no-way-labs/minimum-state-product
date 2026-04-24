#!/usr/bin/env python3
"""Test 2: Understand n=4 non-AD cases, confirm n>=5."""
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

# n=4: the issue is that P3 (with m_3=3) is BOTH left-neighbor of P0 AND right-neighbor of P2
# So P3 is adjacent to both endpoints of the binary block.
# At n>=5 there are separate non-binary neighbors on each side.

# Key insight: at n=4, P_{n-1} = P_3, and P_3 is the right-neighbor of P_2
# AND the left-neighbor of P_0 (ring wraps). So the binary block {P0,P1,P2}
# has the SAME non-binary neighbor on both sides.

# Let's verify: at n=4, ms=(2,2,2,3), check if non-AD happens when
# the non-binary neighbors of P0 and P2 are the same processor.
ms = (2,2,2,3); n = 4
print(f'n=4: P_{n-1} = P3 is left-nbr of P0 AND right-nbr of P2')
print(f'The binary block has ONE non-binary neighbor (P3) on both sides.')
print()

# Now check n=5 with different ms
test_cases = [
    (5, (2,2,2,3,3)),
    (5, (2,2,2,3,4)),
    (5, (2,2,2,4,3)),
    (6, (2,2,2,3,3,3)),
]

for n, ms in test_cases:
    cycles = enum_cycles(ms, 200, 30)
    ad = 0; non_ad = 0
    for path, movers, det in cycles:
        fires = [(path[s][(1-1)%n], path[s][1], path[s][(1+1)%n])
                 for s in range(len(path)) if movers[s]==1]
        fc = len(fires)
        if fc != 2:
            print(f'  n={n}, ms={ms}: P1 fires {fc} times!')
            continue
        (a1,s1,c1),(a2,s2,c2)=fires
        is_ad = (a2==1-a1 and s2==1-s1 and c2==1-c1)
        if is_ad: ad += 1
        else: non_ad += 1
    print(f'n={n}, ms={ms}: {len(cycles)} cycles, AD={ad}, non-AD={non_ad}')

# Also check: does fire count = 2 always hold?
print('\n=== Fire count analysis ===')
for n, ms in [(4,(2,2,2,3)), (5,(2,2,2,3,3)), (5,(2,2,2,3,4)), (6,(2,2,2,3,3,3))]:
    cycles = enum_cycles(ms, 200, 20)
    fc_dist = Counter()
    for path, movers, det in cycles:
        fc = sum(1 for s in range(len(path)) if movers[s]==1)
        fc_dist[fc] += 1
    print(f'n={n}, ms={ms}: P1 fire counts = {dict(fc_dist)}')

# Check ALL binary procs fire count
print('\n=== All binary procs fire count ===')
for n, ms in [(4,(2,2,2,3)), (5,(2,2,2,3,3))]:
    cycles = enum_cycles(ms, 200, 20)
    for pi in range(3):  # P0, P1, P2
        fc_dist = Counter()
        for path, movers, det in cycles:
            fc = sum(1 for s in range(len(path)) if movers[s]==pi)
            fc_dist[fc] += 1
        print(f'n={n}, ms={ms}, P{pi}: fire counts = {dict(fc_dist)}')
