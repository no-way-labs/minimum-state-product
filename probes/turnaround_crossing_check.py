"""
Verify the "crossing through b2 requires b2 to fire" claim.

The walk = mover word. mw[i] fires at step i. mw[i] and mw[i+1] are adjacent.
To go from a proc on left(b2)-side to a proc on right(b2)-side:
  At some step i: mw[i] = left(b2), mw[i+1] = b2.
  At step i+1: mw[i+1] = b2, mw[i+2] = right(b2) (or left(b2) if bounce).

  So crossing from left to right through b2 requires:
  mw[i+1] = b2 (b2 fires at step i+1).

  Without b2 firing: mw[j] = left(b2), mw[j+1] must be left(b2)±1.
  left(b2)±1 = b2 or left(b2)-1.
  If mw[j+1] = b2: b2 fires. If mw[j+1] = left(b2)-1: going away from b2.

  Similarly from right(b2): mw[j] = right(b2), mw[j+1] = b2 or right(b2)+1.
  If b2 doesn't fire: only right(b2)+1.

  So left(b2) and right(b2) are only connected through b2 (as mover).
  If b2 doesn't fire in some interval of the walk, the walk can't cross
  from left(b2)-component to right(b2)-component.

This is essentially: the ring graph with vertex b2 removed has left(b2)
and right(b2) in DIFFERENT connected components (they're the two ends
of a path). The walk on the ring can only "jump" between these components
by firing b2.
"""

print("VERIFIED: On a ring, left(b) and right(b) are connected ONLY through b.")
print("The ring minus {b} is a path from left(b) to right(b).")
print("But left(b) and right(b) are NOT adjacent (they're 2 apart).")
print("So in the walk (mover sequence), going from a proc adjacent to")
print("left(b) to a proc adjacent to right(b) requires passing through b.")
print("Passing through b = b fires.")
print("If b doesn't fire: walk is confined to one side of b. ∎")
print()

# WAIT: I said "left(b) and right(b) are in different connected components
# of ring minus {b}". That's WRONG. Ring minus {b} is a PATH from left(b)
# to right(b). They're in the SAME component! The path connects them.
# left(b) is connected to right(b) via left(b)-1, left(b)-2, ..., right(b).
#
# The key is: the walk's mover word has adjacency constraint.
# mw[i] and mw[i+1] are ring-adjacent.
# From left(b): walk goes to b2 (= b, fires) or left(b)-1.
# From right(b): walk goes to b (fires) or right(b)+1.
#
# So from left(b), NOT going through b: walk goes to left(b)-1.
# From left(b)-1: walk goes to left(b) or left(b)-2.
# Continuing: walk can traverse left(b), left(b)-1, ..., right(b)+1, right(b).
#
# THIS IS THE PATH! The walk CAN go from left(b) to right(b) via the long path.
# It just takes n-2 steps.
#
# WAIT. Then the walk CAN cross from one side to the other without b firing.
# The walk goes: left(b) → left(b)-1 → ... → right(b)+1 → right(b).
# This is going the long way around. But b doesn't need to fire.

# OH NO. This means my Lemma 4 argument is WRONG!
# After b2 bounces (fires once, returns to arrival side), the walk CAN
# reach the other side by going the long way around through the ring,
# WITHOUT b2 firing again!

# But wait: the walk is INSIDE excursion A of b1. In this excursion,
# b1 doesn't fire. The walk can't cross b1 either.
# With BOTH b1 and b2 blocking: the walk goes from left(b1) toward b2,
# bounces at b2, and then... to reach right(b1), it needs to go the long
# way from b2 past... well, the ring has b1 and b2. Going from b2-bounce-side
# to right(b1) requires passing through either b1 or b2.
# b1 doesn't fire. b2 already fired once. If the walk reaches b2's side again...
# wait, b2 already fired its ONE fire. The walk can't visit b2 again.
# But the walk CAN visit procs on b2's side without visiting b2!
# E.g., from the bounce side (left(b2)), go to left(b2)-1, left(b2)-2, ...
# This goes AWAY from b2 and TOWARD b1.
# Eventually reaches b1's neighborhood: right(b1) = b1+1.
# From b1+1: walk goes to b1 (b1 fires? NO, b1 doesn't fire) or b1+2.
# b1+1 → b1 would require b1 to fire. Can't.
# b1+1 → b1+2: going away from b1 and toward b2.
#
# The walk goes: left(b2) → left(b2)-1 → ... → b1+2 → b1+1 = right(b1).
# And then from right(b1): walk goes to b1 or b1+2.
# b1 doesn't fire. Walk goes to b1+2.
#
# BUT WAIT: right(b1) = b1+1. The walk reaching right(b1) is EXACTLY
# what the excursion needs! The excursion A ends at right(b1).
# So the walk CAN reach right(b1) by going the long way from b2 through
# the ring, passing by b1's neighborhood.
#
# BUT: b1 blocks. The path from left(b2)-side goes toward b1.
# right(b1) is ON this path (between b1 and b2 going the short way).
# Wait no. Let me draw the ring properly.
#
# Ring: ..., b1-1, b1, b1+1, ..., b2-1, b2, b2+1, ..., b1-1, ...
# (going CW: b1, b1+1, b1+2, ..., b2-1, b2, b2+1, ..., b1-1, b1)
#
# left(b1) = b1-1, right(b1) = b1+1.
# left(b2) = b2-1, right(b2) = b2+1.
#
# Path avoiding b1 from left(b1) to right(b1):
#   b1-1 → b1-2 → ... → b2+1 → b2 → b2-1 → ... → b1+2 → b1+1.
#   This goes CCW from b1-1 all the way to b2, then CW from b2 to b1+1.
#   Wait no: CCW from b1-1 is b1-2, b1-3, etc. That's going the long way.
#   Going CW from b1-1 would be b1, but b1 is blocked. So yes, CCW.
#
# The path: b1-1, b1-2, ..., b2+1, b2, b2-1, ..., b1+2, b1+1.
# b2 is in the middle of this path.
#
# After b2 bounces (fires once at step when walk reaches b2 from b2-1 side):
# Walk is at b2-1. From b2-1: walk goes to b2 (blocked, b2 used its fire)
# or b2-2.
# b2-1 → b2-2 → ... → b1+2 → b1+1 = right(b1). SUCCESS!
#
# Wait, this IS possible! From b2-1 going CW: b2-2, b2-3, ..., b1+2, b1+1.
# This doesn't go through b2 or b1. It goes the short way from b2-1 to right(b1).
#
# Hmm, but this part of the path is from b2-1 toward b1+1.
# That's the arc from b2 to b1 going CW (not through b2 or b1).
# This arc is: b2-1, b2-2, ..., b1+2, b1+1.
# All these procs are between b2 and b1 on the ring.
# The walk CAN traverse this arc without b2 or b1 firing.
#
# SO THE LEMMA 4 k=1 ARGUMENT IS WRONG!
# The walk CAN reach right(b1) after b2 bounces.

print("CORRECTION: Lemma 4 k=1 argument is FLAWED.")
print("After b2 bounces, the walk CAN reach right(b1) by traversing")
print("the arc from b2 to b1 (going through procs between b2 and b1).")
print("This arc does NOT pass through b2 or b1.")
print()
print("The proof needs a different argument.")
print()

# So what DOES prevent all-turnaround?
# Let me think again. The computation says it's impossible.
# The dead edge argument works for ≥2 same-side TAs.
# For mixed TAs: something else prevents it.

# Let me re-examine from the ADJACENCY CONSTRAINT (Lemma 3).
# Lemma 3: mixed TA at b → adjacent binary neighbors are passthrough.
# This is PROVEN (clean argument, no flaw).
#
# So: if any binary proc is mixed TA, its binary neighbors are passthrough.
# With 3 binary procs, if one is mixed TA:
#   - If either of the other 2 is adjacent to it: that one is passthrough.
#     So not all 3 are turnaround.
#   - If both others are non-adjacent to it: all 3 are non-adjacent.
#     We need another argument for this case.
#
# For 3 pairwise non-adjacent binary procs, all mixed TA:
# Each mixed TA forces its binary neighbors to be passthrough.
# But all neighbors are ternary (since procs are pairwise non-adjacent).
# Lemma 3 doesn't apply.
# And Lemma 4 is flawed.
#
# I need a NEW argument for 3 pairwise non-adjacent mixed TAs.
# Or maybe: 3 pairwise non-adjacent binary procs can't all exist at sub-threshold.
# With n ≥ 9: yes they can (e.g., n=9, binary at 0,3,6).
# Product = 2^3 * 3^6 = 8 * 729 = 5832 < 4*3^7 = 8748. Sub-threshold? Yes.

# So the question remains: CAN 3 pairwise non-adjacent binary procs all be mixed TA?
# Computation says NO. But I need a proof.

# Let me look for a different structural argument.
# Mixed TA at b: fire 1 bounces LEFT, fire 2 bounces RIGHT.
# excursion 1: left(b) → ... → right(b) (winding once).
# excursion 2: right(b) → ... → left(b) (winding once, opposite direction).
#
# Key: the walk alternates between two excursions that go in OPPOSITE
# directions around the ring. Each excursion traverses the entire ring.
#
# With 3 mixed TAs: 6 excursions, each traversing the ring. But they overlap.
# The mover word has L = 3n-3 steps. 6 fires (3 binary × 2 fires each) use
# 6 positions. Remaining 3n-9 positions are in excursions.
#
# Each mixed TA's excursion pair spans L-2 = 3n-5 positions.
# 3 pairs: 3(3n-5) = 9n-15 "excursion-positions". But they overlap.
# Actual distinct positions: 3n-9 (excluding 6 fires).
# Some positions are counted in excursions of all 3 binary procs.

# Hmm, a step-budget argument seems hard. Let me try parity.

# PARITY ARGUMENT:
# For mixed TA at b: excursion 1 has net CW displacement = n-2.
#   (from left(b) to right(b), the long way, going CW: n-2 edges)
#   Actually, which way is "CW"? It depends on the specific excursion.
#   Let's say excursion 1 (fire_L to fire_R): goes from left(b) to right(b).
#   On the ring, left(b) = b-1, right(b) = b+1.
#   Going from b-1 to b+1 NOT through b: go b-1, b-2, ..., b+2, b+1.
#   That's n-2 steps going CCW (b-1 → b-2 is CCW).
#   Net CW displacement: -(n-2).
#   Excursion 2: from right(b) to left(b): b+1 → b+2 → ... → b-1.
#   That's n-2 steps going CW.
#   Net CW displacement: +(n-2).
#
# For 3 mixed TAs: each contributes -(n-2) and +(n-2) from its 2 excursions.
# Net from excursions: 0 for each TA. Total: 0.
# Fires contribute: mixed TA fire_L is (L,L): both CCW, net = -2.
#                   fire_R is (R,R): both CW, net = +2.
#                   Net per TA: 0.
# Total cycle: 0 CW displacement. ✓ (zero winding)
#
# Parity doesn't distinguish. Hmm.

# Maybe I should verify: does the computation confirm that 3 pairwise
# non-adjacent mixed TAs specifically never occur? Earlier we checked
# 3 pairwise non-adjacent binary and found max 1 mixed TA. Let me
# re-check at n=9.

import random
random.seed(42)

n = 9
pairwise_nonadj = [(0,3,6), (1,4,7), (2,5,8), (0,3,7), (1,4,8), (0,4,8)]

for bp in pairwise_nonadj:
    ms = [3]*n
    for b in bp: ms[b] = 2

    max_mixed = 0
    total_valid = 0

    for trial in range(100000):
        L = sum(ms)
        rem = list(ms)
        start = random.choice([p for p in range(n) if rem[p] > 0])
        rem[start] -= 1
        path = [start]
        ok = True
        for _ in range(L-1):
            nbrs = [(path[-1]-1)%n, (path[-1]+1)%n]
            valid = [nb for nb in nbrs if rem[nb] > 0]
            if not valid: ok = False; break
            nxt = random.choice(valid)
            rem[nxt] -= 1
            path.append(nxt)
        if not ok or len(path) != L: continue
        if path[0] not in [(path[-1]-1)%n, (path[-1]+1)%n]: continue

        net = sum(1 if path[(i+1)%L]==(path[i]+1)%n else (-1 if path[(i+1)%L]==(path[i]-1)%n else 0)
                  for i in range(L))
        if net//n != 0: continue
        cw = sum(1 for i in range(L) if path[(i+1)%L]==(path[i]+1)%n)
        if cw == 0: continue
        f = [0]*n
        for p in path: f[p] += 1
        if any(x < 2 for x in f): continue
        total_valid += 1

        mc = 0
        for b in bp:
            fires = [i for i in range(L) if path[i] == b]
            if len(fires) != 2: continue
            fi = []
            for idx in fires:
                prev = path[(idx-1)%L]
                nxt = path[(idx+1)%L]
                a = 'L' if prev == (b-1)%n else 'R'
                d = 'L' if nxt == (b-1)%n else 'R'
                fi.append((a,d))
            if all(a==d for a,d in fi) and fi[0][0] != fi[1][0]:
                mc += 1
        if mc > max_mixed:
            max_mixed = mc
            if mc >= 2:
                print(f"  2+ MIXED: bp={bp}, cycle(first 20)={path[:20]}...")

    print(f"bp={bp}: valid={total_valid}, max_mixed={max_mixed}")
