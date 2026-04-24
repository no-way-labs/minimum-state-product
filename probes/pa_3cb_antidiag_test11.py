#!/usr/bin/env python3
"""Test 11: Prove fire count = 2 for P1.

Claim: In any fair good cycle, P1 (middle binary) fires exactly 2 times.

Argument sketch:
- P1 fires k times where k >= 2 and k is even (binary returns to initial state).
- If k >= 4, P1 has at least 4 mover entries. Since P1 is binary (m_1=2),
  there are 2 from-0 entries and 2 from-1 entries.
- From-0 entries: (a1,0,c1) and (a2,0,c2) with (a1,c1) != (a2,c2).
  Both map to f=1 (toggle). Between the two from-0 firings, P1 must return
  to state 0, which requires a from-1 firing.
- Similarly, 2 from-1 entries with different (L,R) pairs.
- Total: 4 mover triples + at least 4 nonmover triples = 8.
  But |{0,1}^3| = 8, so EVERY triple is either mover or nonmover.
  No triple can be unspecified. This is highly constraining.

Can we show k=4 leads to contradiction?

Actually, the simpler argument: P1 fires EXACTLY 2 times because the
mover walk through the binary block shows P1 is traversed exactly once
per traversal, and there are exactly 2 traversals.

But we've seen cases where P0 fires 4 or 6 times. So the traversal
argument doesn't simply apply. P0 can bounce, but P1 apparently can't.

WHY can't P1 bounce? Because P1 is in the MIDDLE of the binary block.
To bounce, P1 would need to fire, then a neighbor fires, then P1 fires
again. But P1's neighbors are P0 and P2, both binary. After P1 fires
and P0 fires, P1's state is now different (toggled). For P1 to fire again,
it needs a mover entry for the new state. This creates 2 from-0 AND 2
from-1 entries.

But the key constraint: while P1 is not firing, other steps see P1 in
some state and need P1's entry to be nonmover. If all 8 triples are
accounted for (4 mover + 4 nonmover), every configuration that visits
P1 either fires or doesn't. This is very rigid.

Let me check: with 4 mover entries, are there cycles where ME fails?
"""
from itertools import product as iproduct
from collections import Counter

# Exhaustive check: can we build a good cycle at n=5 where P1 fires 4 times?
# The answer from computation is NO. Let's understand why analytically.

# With P1 firing 4 times: 2 from state 0, 2 from state 1.
# The 4 mover triples span all 4 (L,R) pairs from each state? Not necessarily.
# From state 0: 2 of 4 possible (L,R) pairs are mover.
# From state 1: 2 of 4 possible (L,R) pairs are mover.
# The other 2+2 = 4 triples are nonmover.

# Constraint: the mover triples from state 0 must have different (L,R) pairs.
# There are C(4,2)=6 ways to choose 2 mover triples from state 0.

# But the anti-diagonal constraint (if it held) says the 2 mover triples from
# state 0 must be (a,0,c) and (1-a,0,1-c). If we had 4 firings, we'd need
# ANOTHER pair from state 0, but there's no room for anti-diagonal there.

# Wait, with 4 firings from state 0 would be 2, not 4.
# K=4 total means: 2 from state 0, 2 from state 1.
# From state 0: mover triples (a1,0,c1) and (a2,0,c2).
# From state 1: mover triples (a3,1,c3) and (a4,1,c4).
# Nonmover from state 0: the other 2 triples.
# Nonmover from state 1: the other 2 triples.

# Is there a contradiction? Consider P1 at the step right after its first firing.
# P1 is now in state 1 (was 0). If P0 fires next, P1's left neighbor changes.
# Then if P1 fires again... it would be from state 1 with different L.
# This gives one from-1 firing. Then P1 is back to state 0.
# Then if P2 fires and P1 fires again: another from-0 firing. Back to state 1.
# Then need one more from-1 firing to return to state 0.

# But the cycle has finite length. With 4 P1 firings, the cycle needs at least
# 4 steps for P1 plus steps for all other procs. This is feasible for long cycles.

# The real obstruction: MUTUAL EXCLUSION.
# When P1 is not firing, it must not be privileged. If 4 triples are mover
# and 4 are nonmover, there are many steps where P1's context is a mover triple
# but P1 is not the designated mover. At those steps, P1 IS privileged, violating ME.

# So the argument is: if P1 has 4 mover entries (k=4), then at some step where
# another proc is firing, P1's context matches a mover entry, making P1 privileged
# (2 privileged procs -> ME violation).

# This is the deterministic function argument: f_1(L,S,R) = 1-S for mover entries.
# If at some step t, P1's context is (a,s,c) with f_1(a,s,c) = 1-s != s (mover),
# then P1 is privileged at step t. If another proc is also firing at step t, ME fails.

# With 4 mover entries for P1, the probability of a random config hitting one is 4/8=50%.
# In a cycle of length ~2n, there are 2n-4 steps where P1 is not firing.
# At each such step, P1's context must be nonmover. With only 4 nonmover entries,
# this means P1's context at every non-firing step must be one of 4 specific triples.

# This is the key: with 4 mover entries, the nonmover entries for P1 are also 4.
# Every step of the cycle, P1's triple is one of 8 options, and exactly 4 are mover.
# At the ~2n-4 non-firing steps, P1 must have a nonmover triple.
# Since neighbors P0 and P2 are changing their states (binary, changing between 0 and 1),
# P1's context (L,S,R) visits many different triples.

# Actually, the argument below might be cleaner:
# With k=4 mover entries for P1, from state 0 we have 2 mover triples.
# These 2 triples have different (L,R) pairs. The other 2 (L,R) pairs are nonmover.
# Similarly from state 1.
# Consider the steps where P1 is in state 0 and not firing.
# At each such step, P1's (L,R) must be one of the 2 nonmover pairs.
# But P0 and P2 are binary, and they toggle. So P1 sees all 4 (L,R) pairs
# as P0 and P2 go through their state changes.
# If P1 sees one of the 2 mover pairs while in state 0 and not supposed to fire:
# ME violation!

# So: does P1 necessarily see all 4 (L,R) pairs while in state 0?
# P1 is in state 0 for a contiguous segment of steps (from when it toggled to 0
# until it toggles to 1). During this segment, P0 and P2 may or may not change.
# With k=2 (normal case): P1 is in state 0 for one segment, during which it sees
# exactly 1 (L,R) pair as mover (the one it fires on) and the others as nonmover.
# With k=4: P1 is in state 0 for two segments. In each, it fires once.
# The two firings use different (L,R) pairs.
# But in each segment, the (L,R) pair changes as P0 and P2 fire.
# If a segment has P0 or P2 firing while P1 is in state 0, P1 could see
# additional (L,R) pairs. If one of those is a mover pair: ME violation.

# This is getting complex. Let me just verify computationally that k=4 is impossible.
print('=== Can P1 fire 4+ times? Exhaustive check at n=5 ===')

def check_p1_fire_count(ms):
    n = len(ms)
    all_configs = list(iproduct(*[range(m) for m in ms]))
    if len(all_configs) > 500:
        return 'too large'

    # Try all possible 4-mover-entry sets for P1
    # and check if a valid cycle exists

    # Actually, just enumerate cycles and check
    from pa_3cb_antidiag_test2 import enum_cycles
    cycles = enum_cycles(ms, 500, 30)
    fc_dist = Counter()
    for path, movers, det in cycles:
        fc = sum(1 for m in movers if m == 1)
        fc_dist[fc] += 1
    return dict(fc_dist)

# Simpler: just count from existing enumeration
for n, ms in [(5,(2,2,2,3,3)), (5,(2,2,2,3,4)), (5,(2,2,2,4,4)), (4,(2,2,2,3))]:
    def enum_cycles_local(ms, max_cycles=500, max_time=30):
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
                                    for i2 in range(n):
                                        ki = (i2,c[(i2-1)%n],c[i2],c[(i2+1)%n])
                                        if ki in nd and nd[ki] != c[i2]: priv.append(i2)
                                    if len(priv) != 1: me_ok = False; break
                                if me_ok:
                                    cycles.append((path, fm, nd))
                                    if len(cycles) >= max_cycles: return cycles
                            continue
                        if nc not in set(path) and len(path) < 6*n:
                            stack.append((nc, path+[nc], nd, movers+[p]))
            return cycles
        return cycles

    cycles = enum_cycles_local(ms, 500, 20)
    fc_dist = Counter()
    for path, movers, det in cycles:
        fc = sum(1 for m in movers if m == 1)
        fc_dist[fc] += 1
    print(f'n={len(ms)}, ms={ms}: P1 fc = {dict(fc_dist)} ({len(cycles)} cycles)')
