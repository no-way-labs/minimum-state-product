#!/usr/bin/env python3
"""Test 7: WHY is the parity always odd?

Key structural insight: The binary block {P0,P1,P2} is consecutive.
Due to the mover adjacency constraint, the mover sequence must "enter"
and "leave" the binary block through its endpoints (P0 or P2).

At n>=5, P0's non-binary neighbor is P_{n-1} (≠ P3), and P2's non-binary
neighbor is P3 (≠ P_{n-1}). These are DIFFERENT processors.

When the mover enters the binary block from one side, it must traverse
to the other side (since all three binary procs need to fire).

Hypothesis: Between P1's two firings, the binary block is entered from
one side, P1 fires, and the mover exits from the other side. Then
non-binary procs fire. Then the block is entered from the SAME side
again (since the non-binary path is a semicircle from P0's neighbor
to P2's neighbor or vice versa).

Wait, the data shows the block is always traversed 2,1,0 both times.
That means:
- Enter from P2's side (P3 fires, then P2), traverse to P1, P0.
- Non-binary procs do their thing.
- Enter from P2's side again, traverse 2,1,0 again.

Between P1's two firings (at positions within the 2,1,0 sweeps):
P0 fires exactly once (at the end of the first sweep).
P2 fires exactly once (at the beginning of the second sweep).
P1 fires once per sweep.

So between P1's first firing (mid-sweep-1) and second firing (mid-sweep-2):
- P0 fires once (end of sweep 1)
- Then non-binary procs fire
- P2 fires once (start of sweep 2)
That's 1 firing each. Odd parity confirmed.

But wait: at n=5 with ms=(2,2,2,3,4), P0 can fire more times.
Those extra firings happen during the non-binary segment.
P0 is binary, adjacent to P_{n-1}. If P_{n-1} fires, then P0 could fire.
But P0 is on the boundary of the binary block. P0's non-binary neighbor
is P_{n-1} = P4. If P4 fires and then P0 fires (as a back-and-forth),
then P0 gets extra firings.

These extra firings come in PAIRS (P0 fires, then something, then P0 fires
again). Each pair preserves parity. So parity remains odd.

Actually, let me check: do the extra P0 firings come in pairs?
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

# Detailed look at the extra-P0-firing cases
ms = (2,2,2,3,4); n = 5
cycles = enum_cycles(ms, 200, 30)

print(f'n={n}, ms={ms}: {len(cycles)} cycles')
print('\n=== Cases where P0 fires > 2 ===')

for path, movers, det in cycles:
    p0_fc = sum(1 for m in movers if m == 0)
    if p0_fc > 2:
        L = len(path)
        p1_steps = [s for s in range(L) if movers[s] == 1]
        s1, s2 = p1_steps

        # Between segment
        between_movers = [movers[s] for s in range(s1+1, s2)]
        after_movers = [movers[s] for s in list(range(s2+1, L)) + list(range(0, s1))]

        p0_between = sum(1 for m in between_movers if m == 0)
        p0_after = sum(1 for m in after_movers if m == 0)

        print(f'\n  P0 fires {p0_fc} total, between={p0_between}, after={p0_after}')
        print(f'  Full movers: {movers}')
        print(f'  Between: {between_movers}')
        print(f'  After: {after_movers}')

        # Show the P0 firings in context
        for s in range(L):
            if movers[s] == 0:
                c = path[s]
                segment = 'BETWEEN' if s1 < s < s2 else 'AFTER'
                print(f'    P0 fires at step {s} ({segment}): config={c}')
        break  # just one example

# Now check: is the oddness of P0 between related to the path structure?
# Between P1's firings, the mover path goes from P1 (step s1) to P0 (step s1+1),
# then through non-binary procs, then to P2 (just before s2), then P1 (step s2).
# P0 fires at step s1+1. Any extra P0 firings happen during the non-binary segment.
# Each extra P0 firing requires the mover to bounce back from P0's non-binary neighbor.
# Pattern: ..., P_{n-1}, P0, P_{n-1}, ... -> two extra firings for P0? No, just one extra.
# Wait: P0 fires at step s1+1. Then mover goes to P_{n-1}. If mover returns to P0,
# that's one more P0 firing (total 2 between). Then mover goes back to P_{n-1}.
# If it returns again, that's 3 between. So the pattern is:
# P0, P_{n-1}, P0, P_{n-1}, P0, ... -> P0 fires at positions 0, 2, 4, ...
# This always gives ODD count if the first and last P0 firings are the boundary ones.

# Actually the key: P0 fires once at the START of the between segment (leaving the
# binary block after P1 fires). Then it might bounce with P_{n-1}. Each bounce adds
# 2 more P0 firings (P0 -> P_{n-1} -> P0 is +1 P0 firing, not +2).
# No: P0 -> P_{n-1} -> P0 adds 1 more P0 firing to the total.
# So: base 1, plus k bounces, gives 1+k P0 firings between.
# For parity to be odd, k must be even.

# Let me check
print('\n=== P0 bounce structure between P1 firings ===')
for path, movers, det in cycles:
    p0_fc = sum(1 for m in movers if m == 0)
    L = len(path)
    p1_steps = [s for s in range(L) if movers[s] == 1]
    s1, s2 = p1_steps
    between = [(s, movers[s]) for s in range(s1+1, s2)]
    p0_count = sum(1 for s, m in between if m == 0)
    if p0_count > 1:
        print(f'  P0 fires {p0_count} between, movers={[m for s,m in between]}')
        # Show just the P0 and P_{n-1} part
        boundary = [(s, m) for s, m in between if m in {0, n-1}]
        print(f'    P0/P4 subsequence: {[m for s,m in boundary]}')
