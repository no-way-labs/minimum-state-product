#!/usr/bin/env python3
"""Test script for Anti-Diagonal Fire Pattern Lemma."""
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

# n=4 test
ms = (2,2,2,3); n = 4
print(f'=== n={n}, ms={ms} ===')
cycles = enum_cycles(ms, 500, 30)
print(f'Found {len(cycles)} cycles')

ad_types = Counter()
non_ad_types = Counter()
non_ad_examples = []
for path, movers, det in cycles:
    fires = [(path[s][0],path[s][1],path[s][2]) for s in range(len(path)) if movers[s]==1]
    assert len(fires) == 2, f"P1 fires {len(fires)} times"
    (a1,s1,c1),(a2,s2,c2)=fires
    is_ad = (a2==1-a1 and s2==1-s1 and c2==1-c1)
    pat = tuple(sorted([fires[0], fires[1]]))
    if is_ad:
        ad_types[pat] += 1
    else:
        non_ad_types[pat] += 1
        if len(non_ad_examples) < 3:
            non_ad_examples.append((path, movers, fires))

print(f'\nAnti-diagonal patterns ({sum(ad_types.values())} total):')
for pat, cnt in sorted(ad_types.items()):
    print(f'  {pat}: {cnt}')
print(f'\nNon-anti-diagonal patterns ({sum(non_ad_types.values())} total):')
for pat, cnt in sorted(non_ad_types.items()):
    print(f'  {pat}: {cnt}')

# Show non-AD examples
for path, movers, fires in non_ad_examples[:1]:
    print(f'\nNon-AD example: fires={fires}')
    print(f'  Cycle len={len(path)}, movers={movers}')
    for s in range(len(path)):
        c = path[s]
        marker = ' <-- P1 fires' if movers[s]==1 else ''
        print(f'    step {s}: {c} -> P{movers[s]}{marker}')

# Check: what's the (L,R) relationship in non-AD cases?
print('\n\nNon-AD (L,R) analysis:')
for pat, cnt in sorted(non_ad_types.items()):
    (a1,s1,c1),(a2,s2,c2) = pat
    print(f'  ({a1},{s1},{c1}) + ({a2},{s2},{c2}): L-flip={a2==1-a1}, S-flip={s2==1-s1}, R-flip={c2==1-c1}, count={cnt}')

# n=5 test
print(f'\n\n=== n=5, ms=(2,2,2,3,3) ===')
ms5 = (2,2,2,3,3); n5 = 5
cycles5 = enum_cycles(ms5, 200, 30)
print(f'Found {len(cycles5)} cycles')

ad5 = 0; non_ad5 = 0; fc_dist5 = Counter()
non_ad5_pats = Counter()
for path, movers, det in cycles5:
    fires = [(path[s][0],path[s][1],path[s][2]) for s in range(len(path)) if movers[s]==1]
    fc_dist5[len(fires)] += 1
    if len(fires) == 2:
        (a1,s1,c1),(a2,s2,c2)=fires
        is_ad = (a2==1-a1 and s2==1-s1 and c2==1-c1)
        if is_ad: ad5 += 1
        else:
            non_ad5 += 1
            pat = tuple(sorted([fires[0], fires[1]]))
            non_ad5_pats[pat] += 1

print(f'P1 fire count: {dict(fc_dist5)}')
print(f'Anti-diagonal: {ad5}, Non-AD: {non_ad5}')
if non_ad5_pats:
    print(f'Non-AD patterns: {dict(non_ad5_pats)}')
