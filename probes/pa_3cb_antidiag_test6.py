#!/usr/bin/env python3
"""Test 6: Verify parity is the key, not exact count.
Also: prove fire count = 2 for middle binary.

The proof strategy:
1. P1 fires exactly 2 times (m_1 = 2).
2. Between the two firings, P0 fires an odd number of times.
3. Between the two firings, P2 fires an odd number of times.
4. Since P0 binary: odd fires = state flipped. So L flips.
5. Since P2 binary: odd fires = state flipped. So R flips.
6. P1's state flips (from 0 to 1 or vice versa).
7. Hence: all three coordinates flip -> anti-diagonal.

Why (2) and (3)?
- The mover adjacency constraint says between P1's firings (which bracket
  one direction through the binary block), P0 and P2 must each fire.
  P2 fires just before P1 (entering the block from one side), P0 fires
  just after P1 (leaving the block to the other side).
- But this only accounts for 1 firing each. Could there be extra firings?
- If so, they must come in pairs (since binary: each extra pair returns state).
  Wait, they don't need to come in pairs within the between-segment.
  P0 fires k times between and (2-k) times in the other segment.
  But 2 total, so k can be 0, 1, or 2.

Let me check: can P0 fire 0 times between P1's firings?
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

# Verify for n=5 with ms=(2,2,2,3,4) where P0 can fire >2 times
ms = (2,2,2,3,4); n = 5
cycles = enum_cycles(ms, 200, 30)
print(f'n={n}, ms={ms}: {len(cycles)} cycles')

# Full analysis
for pi in range(3):
    fc_dist = Counter()
    parity_between = Counter()
    for path, movers, det in cycles:
        L = len(path)
        # Fire count for proc pi
        fc = sum(1 for m in movers if m == pi)
        fc_dist[fc] += 1

        # Fire parity between P1's firings
        p1_steps = [s for s in range(L) if movers[s] == 1]
        if len(p1_steps) == 2:
            s1, s2 = p1_steps
            between = [movers[s] for s in range(s1+1, s2)]
            pi_b = sum(1 for m in between if m == pi) % 2
            parity_between[pi_b] += 1

    print(f'  P{pi}: fire count = {dict(fc_dist)}, parity between P1 = {dict(parity_between)}')

# Fire count = 2 proof for P1:
# P1 is binary. In a fair cycle, it fires at least once.
# Since binary, it fires once from state 0 and once from state 1 (minimum).
# After 2 firings, it returns to its initial state.
# Could it fire 4 times? That requires 2 more (L,R) contexts.
# Total available: 4 (L,R) pairs. But determinism + ME constrain this.

# Key insight: if P1 fires 4 times, it fires twice from state 0 and twice from state 1.
# From state 0: two different (L,R) pairs -> two different mover entries.
# From state 1: two different (L,R) pairs -> two different mover entries.
# That's 4 mover entries for P1. But also 4 nonmover entries
# (the OTHER (L,R) pairs with each state).
# Total: 8 entries for P1, which is 2^3 = all possible entries.
# Every entry is either mover or nonmover.
# This means P1 is privileged at EXACTLY 4 of 8 triples.
# Is this possible? Yes, it's consistent.
# But the cycle length would need to be much longer...

# Actually: let me check if P1 ever fires >2 at n=5 with bigger m values
print('\n=== Does P1 ever fire > 2? ===')
for n, ms in [(5,(2,2,2,3,4)), (5,(2,2,2,4,4)), (5,(2,2,2,5,5))]:
    P = 1
    for m in ms: P *= m
    if P > 400:
        print(f'  n={n}, ms={ms}: product={P}, skipping (too large)')
        continue
    cycles = enum_cycles(ms, 200, 20)
    fc1_dist = Counter()
    for path, movers, det in cycles:
        fc1 = sum(1 for m in movers if m == 1)
        fc1_dist[fc1] += 1
    print(f'  n={n}, ms={ms}: {len(cycles)} cycles, P1 fc = {dict(fc1_dist)}')

# The adjacency constraint is critical. Check what happens if we DON'T require adjacency
print('\n=== Without adjacency constraint: does P1 fire count change? ===')
# (Skipping - the adjacency constraint is a given for the problem)

# Instead: prove that P1 can't fire >2 via determinism argument
# If P1 fires on (a1,0,c1) -> 1 and (a2,0,c2) -> 1 (two distinct from-0 firings),
# then both (a1,0,c1) and (a2,0,c2) are mover triples.
# At some other step, P1 sees (a1,0,c1) as non-mover -> needs f(a1,0,c1) = 0.
# But we said f(a1,0,c1) = 1. Contradiction.
# WAIT: P1 might never see (a1,0,c1) as non-mover if no other step has P1 in state 0
# with neighbors a1, c1.

# Actually the key constraint: P1 fires ONLY 2 times, so it's in state 0 at some steps
# and state 1 at others. When it's in state 0 and NOT firing, the triple (L,0,R) must
# be a non-mover entry (f=0). When firing from state 0, (L,0,R) is mover (f=1).
# Can there be two different mover triples from state 0?
# Only if P1 encounters two different (L,R) contexts while in state 0 AND needs to fire.
# But if it fires from (a1,0,c1), its state changes to 1. To fire again from state 0,
# it must return to state 0 first (fire from state 1), then encounter another mover triple.

# This is allowed in principle. The question is whether the cycle structure prevents it.

# Let me directly check: how many distinct mover triples does P1 have?
print('\n=== P1 mover triple count ===')
for n, ms in [(4,(2,2,2,3)), (5,(2,2,2,3,3)), (5,(2,2,2,3,4)), (6,(2,2,2,3,3,3))]:
    cycles = enum_cycles(ms, 200, 20)
    mover_count_dist = Counter()
    for path, movers, det in cycles:
        L = len(path)
        mover_triples = set()
        for s in range(L):
            if movers[s] == 1:
                c = path[s]
                mover_triples.add((c[0], c[1], c[2]))
        mover_count_dist[len(mover_triples)] += 1
    print(f'  n={n}, ms={ms}: P1 mover triples = {dict(mover_count_dist)}')
