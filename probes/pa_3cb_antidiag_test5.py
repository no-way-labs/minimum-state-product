#!/usr/bin/env python3
"""Test 5: Verify that binary block is always traversed same-direction
and check the broader structure at larger n."""
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

# Check binary block traversal patterns at various n
for n, ms in [(5,(2,2,2,3,3)), (5,(2,2,2,3,4)), (5,(2,2,2,4,3)), (6,(2,2,2,3,3,3))]:
    cycles = enum_cycles(ms, 200, 20)
    block_pats = Counter()
    for path, movers, det in cycles:
        L = len(path)
        # Extract binary mover subsequence
        bin_movers = tuple(m for m in movers if m in {0,1,2})
        block_pats[bin_movers] += 1

    print(f'n={n}, ms={ms}: {len(cycles)} cycles')
    for pat, cnt in sorted(block_pats.items(), key=lambda x: -x[1]):
        print(f'  {pat}: {cnt}')

# Also check n=4 for comparison
print(f'\nn=4, ms=(2,2,2,3):')
cycles4 = enum_cycles((2,2,2,3), 500, 30)
block_pats4 = Counter()
for path, movers, det in cycles4:
    bin_movers = tuple(m for m in movers if m in {0,1,2})
    block_pats4[bin_movers] += 1
for pat, cnt in sorted(block_pats4.items(), key=lambda x: -x[1])[:10]:
    print(f'  {pat}: {cnt}')

# KEY QUESTION: At n>=5, can the binary block be traversed in different directions?
# e.g., (0,1,2) instead of (2,1,0)?
print(f'\n=== Direction analysis ===')
for n, ms in [(5,(2,2,2,3,3)), (6,(2,2,2,3,3,3))]:
    cycles = enum_cycles(ms, 200, 20)
    dir_pats = Counter()
    for path, movers, det in cycles:
        L = len(path)
        runs = []
        current = []
        for s in range(L):
            if movers[s] in {0,1,2}:
                current.append(movers[s])
            else:
                if current:
                    runs.append(tuple(current))
                    current = []
        if current:
            runs.append(tuple(current))
        dir_pats[tuple(runs)] += 1

    print(f'n={n}, ms={ms}: {len(dir_pats)} distinct binary run patterns')
    for pat, cnt in sorted(dir_pats.items(), key=lambda x: -x[1])[:10]:
        print(f'  {pat}: {cnt}')
