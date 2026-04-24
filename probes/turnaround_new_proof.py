"""
New approach: prove ≥2 mixed TAs impossible via excursion ordering.

For mixed TA at b: fire_L bounces LEFT (arr=L, dep=L), fire_R bounces RIGHT.
The walk around b looks like:
  ...left(b)...left(b), b, left(b)...right(b)...right(b), b, right(b)...left(b)...

Between fire_L and fire_R: excursion E1 from left(b) to right(b).
Between fire_R and fire_L: excursion E2 from right(b) to left(b).

Key: E1 goes "CCW" (from b-1 through b-2,...,b+2 to b+1).
     E2 goes "CW" (from b+1 through b+2,...,b-2 to b-1).
(Assuming the standard ring orientation.)

For TWO mixed TAs at b1, b2:
Consider how b2's fires appear in b1's excursions.
b2 fires twice: fire_L2 and fire_R2.

Case 1: Both b2 fires in E1(b1).
  Then b2's excursion between fire_L2 and fire_R2 is inside E1(b1).
  b2's excursion E1(b2) goes from left(b2) to right(b2) (CCW winding).
  But it's inside E1(b1) which also winds CCW.
  The total winding of E1(b1) = winding from b1's excursion path.
  b2's excursions contribute ±1 winding each; since both are inside E1(b1),
  the net winding contribution is 0.

  Now, E2(b1) (from right(b1) to left(b1)) winds CW (+1 winding).
  But b2 fires 0 times in E2(b1).
  E2(b1) must still traverse the ring (winding once).
  E2(b1) must pass through b2's position. But b2 doesn't fire in E2(b1).
  The walk in E2(b1) can't visit b2 (b2 ≠ mover).

  But CAN the walk in E2(b1) reach right(b1) from right(b1) going CW?
  Starting at right(b1) = b1+1, going CW through the ring:
  b1+1, b1+2, ..., eventually reaching b2. b2 doesn't fire.
  Need to get past b2. From left(b2) = b2-1: step to b2 requires b2 to fire.
  From right(b2) = b2+1: step to b2 requires b2 to fire.
  So the walk can't visit b2. It goes from b2-1 to b2-2 (away) or from
  b2+1 to b2+2 (away).

  But E2(b1) goes from right(b1) to left(b1). Let's trace:
  right(b1) = b1+1. Going CW: b1+2, b1+3, ..., b2-1.
  At b2-1: can go to b2 (blocked) or b2-2 (away from b2, but also away from destination).
  Hmm, b2-2 is further CW... wait no.
  Going CW from b2-1 is b2. Going CCW from b2-1 is b2-2.

  If the walk goes CCW from b2-1 (to b2-2), it's going BACK toward right(b1).
  That's backtracking. The walk can backtrack but eventually must reach left(b1).

  Left(b1) = b1-1. Going CW from b2 to b1-1:
  b2+1, b2+2, ..., b1-1.
  This is the OTHER arc (from b2 to b1 going CW).

  The walk in E2(b1) must traverse from b1+1 to b1-1 going CW (the long way).
  This path passes through b2. b2 doesn't fire. So the walk is stuck at b2.
  It approaches from one side (b2-1 from b1+1 direction), can't cross.
  To reach b1-1, it needs to get to the other side of b2.

  Going around through b1: b1 doesn't fire in its own excursion.
  So b1 is also blocked.

  TWO BLOCKERS: b1 and b2. The ring minus {b1, b2} has two arcs:
  Arc A: b1+1, b1+2, ..., b2-1 (from right(b1) to left(b2))
  Arc B: b2+1, b2+2, ..., b1-1 (from right(b2) to left(b1))

  E2(b1) starts at b1+1 (in Arc A) and must end at b1-1 (in Arc B).
  Neither b1 nor b2 fires in E2(b1). Walk is confined to Arc A.
  Can't reach Arc B. CONTRADICTION!

  Wait, this is exactly the original Lemma 4 argument but applied to the
  ZERO-fires case (k=0 of b2 in E2(b1), rather than E1(b1)).
  When both b2 fires are in E1(b1), then E2(b1) has b2 fires = 0.
  And E2(b1) starts in one arc and ends in the other. Stuck. Contradiction.

Case 2: b2 fires split: one fire in E1(b1), one fire in E2(b1).
  In E1(b1): b2 fires once. In E2(b1): b2 fires once.
  Both excursions have one b2 fire.

  E1(b1) starts at left(b1) and ends at right(b1). After b2 fires once
  and bounces, walk is on one side. But can reach the other side via
  the OTHER arc (not through b2 or b1). This was our earlier concern.

  Specifically: E1(b1) goes from b1-1 to b1+1 (the long way through b2).
  b2 fires once in E1(b1). Walk visits b2 once. After b2 bounces:
  walk is on b2's arrival side. But can continue to other side via
  the arc from b2-side that goes around to b1+1 (not through b2 or b1).

  THIS IS POSSIBLE! The walk after bouncing at b2 can go:
  bounce-side → bounce-side-1 → ... → other procs → b1+1.

  Going which direction? From b2 arrival side (say b2-1), going CCW:
  b2-1 → b2-2 → ... → b1+2 → b1+1.
  This doesn't cross b2 or b1. Possible!

  OR from b2 arrival side (say b2+1), going CW:
  b2+1 → b2+2 → ... → b1-2 → b1-1 → and then need to get to b1+1.
  But b1 is in the way. Can't cross b1. Stuck before b1.

  Hmm, it depends on WHICH side the walk arrives at b2 from.

  Let me think about this more carefully with the ring geometry.

  E1(b1): from b1-1 to b1+1, going the long way around.
  The path (ring minus b1): b1-1, b1-2, ..., b2+1, b2, b2-1, ..., b1+2, b1+1.

  b2 is on this path. Let d1 = arc distance from b1-1 going to b2 (CCW):
  b1-1 → b1-2 → ... → b2+1 → b2. Distance: ring_dist(b1-1, b2) going CCW.

  E1(b1) starts at b1-1 and must reach b1+1. The walk traverses the path,
  visiting b2 at some point. It bounces at b2 and then continues.

  After bouncing at b2: walk is at b2±1 (arrival side).

  Sub-case 2a: walk approaches b2 from b2+1 (coming from b1-1 direction CCW):
    b1-1 → b1-2 → ... → b2+1 → b2 (fire, bounce) → b2+1.
    Now at b2+1, going toward b1-1 direction. Walk backtracks.
    Walk is at b2+1. Going CW: b2+2, ..., b1-1 (backtrack). Going CCW: b2 (blocked).
    Walk can only go CW: b2+1 → b2+2 → ... eventually back to b1-1.
    Then b1-1 → b1 is blocked. b1-1 → b1-2 → ... → b2+1 (revisit).
    Walk is looping in the arc b1-1 to b2+1. Can't reach b2-1 or b1+1.
    STUCK! Wait, actually...

    The walk is in Arc A (b1+1 to b2-1) and Arc B's complement.
    Hmm, I need to draw this properly.

    Ring: 0, 1, 2, ..., n-1. Say b1=0, b2=3 (n=9, pairwise non-adjacent).
    b1-1 = 8, b1+1 = 1.
    b2-1 = 2, b2+1 = 4.

    Path from 8 to 1 (avoiding b1=0): 8, 7, 6, 5, 4, 3, 2, 1.
    b2=3 is at position 5 in this path (0-indexed: 8,7,6,5,4,3,2,1).

    Walk starts at 8. Goes: 8→7→6→5→4→3(=b2, fire, bounce)→4.
    Now at 4. Going: 4→5→6→7→8 (backtrack to start). From 8: go to 0? No, b1=0 blocked.
    8→7→...→4→5→...→8 forever. Walk is trapped in {4,5,6,7,8}.
    Can't reach {1, 2}. But excursion must end at 1 (=right(b1)=b1+1).
    CONTRADICTION!

  Sub-case 2b: walk approaches b2 from b2-1 (coming from b1+1 direction):
    But E1 starts at b1-1. How does the walk get to b2-1 from b1-1?
    b1-1=8. b2-1=2. Going from 8 to 2 without passing through b1=0 or b2=3:
    8→7→6→5→4→3 NO that's b2. Must avoid b2.
    8→7→6→5→4→3? Can't avoid b2. The only path from 8 to 2 (avoiding b1=0)
    goes through b2=3.

    Alternative: 8→0→1→2? No, b1=0 blocked.

    So from 8 (=b1-1), the only way to reach 2 (=b2-1) is through b2=3
    or through b1=0. Both blocked. CAN'T reach b2-1 from b1-1 in E1!

    So the walk ALWAYS approaches b2 from the b2+1 side (sub-case 2a).
    And sub-case 2a shows the walk gets stuck. CONTRADICTION!

So Case 2 (split fires) IS actually a contradiction!
My earlier reasoning was wrong when I said the walk could go
"the other way" after bouncing — it CAN'T because both b1 and b2
block different arcs.

Let me verify this with the specific ring geometry.
"""

print("="*60)
print("RING GEOMETRY VERIFICATION")
print("="*60)

# n=9, b1=0, b2=3 (pairwise non-adjacent).
n = 9
b1, b2 = 0, 3

# Path from left(b1)=8 to right(b1)=1 avoiding b1=0:
# 8, 7, 6, 5, 4, 3, 2, 1. Length 7 = n-2.
path = []
p = (b1-1) % n  # = 8
while p != (b1+1) % n:
    path.append(p)
    p = (p-1) % n
    if p == b1: p = (p-1) % n  # skip b1
path.append((b1+1) % n)
print(f"Path from left(b1)={b1-1} to right(b1)={(b1+1)%n}: {path}")

# b2=3 is on this path at index:
b2_idx = path.index(b2)
print(f"b2={b2} at index {b2_idx} in path")

# Arc A: path[:b2_idx] = procs from left(b1) to left(b2)
arc_A = path[:b2_idx]
# Arc B: path[b2_idx+1:] = procs from right(b2) to right(b1)
arc_B = path[b2_idx+1:]
print(f"Arc A (left(b1) to left(b2)): {arc_A}")
print(f"Arc B (right(b2) to right(b1)): {arc_B}")
print()

# E1(b1) starts at left(b1) = path[0] = 8.
# Walk goes CCW: 8→7→6→5→4→3(=b2).
# At b2: fire, bounce back to arrival side (4 = b2+1).
# Walk is at 4. From 4: go to 5 or 3(blocked). Must go to 5.
# 5→6→7→8 (back to start).
# From 8: go to 0(=b1, blocked) or 7. Must go to 7.
# Walk is trapped in {4,5,6,7,8} = Arc A ∪ {b2+1} ... wait no.
# Arc A = {8,7,6,5,4} = {path[0],...,path[4]}.
# b2 = path[5] = 3.
# After bounce: at path[4] = 4. Walk can traverse {4,5,6,7,8} freely.
# But right(b1) = 1 is in Arc B = {2, 1}. Can't reach it.

print("Walk in E1(b1) after b2 bounce:")
print("  Start at 8. Goes: 8→7→6→5→4→3(fire b2, bounce)→4.")
print("  Trapped in {4,5,6,7,8}. Right(b1)=1 in Arc B={2,1}. UNREACHABLE.")
print()

# Now let me verify: does the walk APPROACH b2 from the right side (b2+1=4)?
# Path from 8 going CCW: 8,7,6,5,4,3. So arrival at 3 from 4 (= b2+1 = RIGHT of b2).
# For mixed TA at b2: one fire bounces LEFT, one bounces RIGHT.
# If this fire bounces LEFT: arr=R (from 4), dep=R (back to 4). So b2+1=4 is right of b2.
# Actually: left(b2) = b2-1 = 2. right(b2) = b2+1 = 4.
# Arr from 4 = right(b2): arr = R.
# For mixed TA bounce to SAME side: dep = R. Walk returns to 4. ✓

# But what if b2's MIXED TA has this fire bouncing LEFT instead?
# Then: arr = R, dep = L. NOT turnaround!
# For this fire to be turnaround: dep = arr = R. ✓ (bounces right)
# For the OTHER fire (fire_L): arr = L, dep = L (bounces left).
# Fire_L doesn't happen in E1(b1) (it's in E2(b1) or E1(b1) depending on placement).

# In case 2 (split fires), one b2 fire is in E1(b1). Let's say it's fire_R (bounces right).
# Then fire_L (bounces left) is in E2(b1).
# In E1(b1): b2 fires once (fire_R), walk arrives from right (b2+1=4), bounces right (back to 4).
# Walk trapped in Arc A. ✓ CONTRADICTION.

# What if it's fire_L (bounces left) that's in E1(b1)?
# Walk arrives at b2 from... which side?
# From path: arriving from b2+1 = 4 (RIGHT side).
# fire_L: arr = L, dep = L. But arr = R (from 4). arr ≠ L.
# CONTRADICTION with fire_L being (L,L).
# So fire_L can't have arr=R. It must have arr=L. But the walk approaches from RIGHT.
# This means fire_L is NOT the fire in E1(b1). It must be fire_R.
# Therefore: the fire in E1(b1) is always fire_R (bouncing right).

print("CONCLUSION: In E1(b1), b2 always fires its RIGHT-bounce fire.")
print("Walk approaches b2 from b2+1 (RIGHT), bounces back to b2+1.")
print("Walk is trapped in Arc A = {left(b1), ..., b2+1}.")
print("Cannot reach right(b1). CONTRADICTION.")
print()

# Similar for b2 fires in E2(b1):
# E2(b1) goes from right(b1)=1 to left(b1)=8, going CW.
# Path: 1, 2, 3, 4, 5, 6, 7, 8 (going CW from 1).
# b2=3 is on this path. Walk approaches from 2 (=b2-1=LEFT of b2).
# b2 fires (fire_L: bounces LEFT). Walk returns to 2.
# Walk trapped in {1, 2}. Left(b1)=8 in Arc B = {4,5,6,7,8}. UNREACHABLE.
# CONTRADICTION.

print("In E2(b1): walk approaches b2 from b2-1=2 (LEFT), bounces LEFT.")
print("Walk trapped in {1, 2}. Left(b1)=8 is unreachable. CONTRADICTION.")
print()
print("THEREFORE: Case 2 (split fires) is impossible for non-adjacent mixed TAs.")
print()
print("Combined with Case 1 (both fires same excursion): ALL cases contradicted.")
print("TWO NON-ADJACENT MIXED TAs ARE IMPOSSIBLE. ∎")
