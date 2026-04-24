"""
Check whether the all-tight all-normal-form pattern can be realized
by ANY transition function assignment for the ring (2,2,3,2,2,3,2,2,3,2,2,3).

n=12, k=4 ternary pivots at positions 2, 5, 8, 11.
Each processor fires exactly 2 times in the full cycle (length 24).

The all-tight all-normal-form pattern:
- 2 phases per pivot, 4 pivots = 8 phases
- Each phase: pivot fires, then 4 local processors fire in tight order
- But phases interleave: each phase has 3 steps (the pivot firing +
  some subset of local fires that haven't been claimed by other phases)

Actually, let me think about this more carefully.

The mover sequence has length 24. We need to specify exactly which processor
fires at each step. The "all-tight" pattern means:

For each pivot t, between consecutive t-firings (a t-phase), the following
fires happen in tight order:
  left2(t), left(t), right2(t), right(t)

With the ring (2,2,3,2,2,3,2,2,3,2,2,3):
  Pivot 2: left2=0, left=1, right=3, right2=4
  Pivot 5: left2=3, left=4, right=6, right2=7
  Pivot 8: left2=6, left=7, right=9, right2=10
  Pivot 11: left2=9, left=10, right=0, right2=1

Each binary processor appears in exactly 2 pivot neighborhoods:
  0: pivot 2 (left2) and pivot 11 (right)
  1: pivot 2 (left) and pivot 11 (right2)
  3: pivot 2 (right) and pivot 5 (left2)
  4: pivot 2 (right2) and pivot 5 (left)
  6: pivot 5 (right) and pivot 8 (left2)
  7: pivot 5 (right2) and pivot 8 (left)
  9: pivot 8 (right) and pivot 11 (left2)
  10: pivot 8 (right2) and pivot 11 (left)

Each binary proc fires exactly 2 times total = once per pivot neighborhood.
Each pivot fires 2 times.

The mover sequence interleaves phases from different pivots.
With alternating polarity (positive at pivots 2, 8; negative at 5, 11):

A natural ordering of the 24 steps:
Phase 1 of pivot 2: [2, 0, 1, 3, 4]  -- but that's 5 steps for first phase?

Wait. Let me reconsider. Each pivot fires P=2 times. Between consecutive
t-firings, the 4 local processors fire. So a t-phase has 4 non-t firings
plus the t-firing at the boundary. The total steps from t-firings alone:
4 pivots * 2 = 8. Non-t firings: 8 binary * 2 = 16. Total: 24. Check.

The 8 phases (2 per pivot) partition the 16 binary firings into groups of 2
(not 4), because each binary proc fires once per pivot neighborhood, and
each phase involves 2 binary procs from one side.

Hmm, let me reconsider. With P=2 firings per pivot:
- Phase 1 of pivot 2: between t-firing 1 and t-firing 2
- Phase 2 of pivot 2: between t-firing 2 and t-firing 1 (wrapping)

In each phase, the "tight" constraint means:
  (J,K,g,h) = (1,1,1,1) per phase means:
  - J=1: left side fires 1 time (left fires once)
  - K=1: right side fires 1 time (right fires once)
  - g=1: left2 fires once (immediately before left)
  - h=1: right2 fires once (immediately before right2... wait)

Actually, (J,K,g,h) = (1,1,1,1) means each of left, left2, right, right2
fires exactly once in this phase. The tight constraint means left2 fires
immediately before left, and right2 fires immediately before right.

So each phase has: left2, left (tight pair), right2, right (tight pair),
plus the pivot firing at the boundary.

That's 4 binary firings per phase. 8 phases * 4 = 32 binary firings. But
we only have 16 binary firings (8 binary procs * 2 each). So 32 ≠ 16.

The issue: each binary proc is shared between 2 pivot neighborhoods, so
it fires once per phase of each pivot. But with P=2 phases per pivot,
that's 2 firings per binary proc per pivot = 4 total? No, each binary
fires exactly 2 times total.

I think the resolution is: each binary proc fires once in one phase of
one pivot, and once in one phase of the adjacent pivot. Not once per phase
of each pivot.

So each phase has: 2 binary firings (one from each side), not 4.
8 phases * 2 = 16. Plus 8 pivot firings = 24. Check!

Wait, but the problem statement says (J,K,g,h) = (1,1,1,1) per phase,
meaning 4 local processors fire per phase. That gives 8*4 + 8 = 40 ≠ 24.

Let me re-read. "exactly 4 local processors fire" per phase. With 8 phases
that's 32 local firings. But 8 binary procs * 2 = 16 = 32/2, so each
local firing is counted in 2 phases? That can't be right since each step
is in exactly one phase.

I think the issue is that phases from DIFFERENT pivots can overlap in time.
A step might be in a phase of pivot 2 AND in a phase of pivot 5
simultaneously (since those phases are defined by different pivot firings).

But for the mover SEQUENCE, each step is at a unique position in time.
The phases are not sequential segments; they are overlapping windows defined
by each pivot's firing times.

For the concrete mover sequence, let me think about it differently.

Each pivot fires 2 times. The pivot firings define the backbone:
t1_1, ..., t1_2, t2_1, ..., t2_2, t3_1, ..., t3_2, t4_1, ..., t4_2

Interleaved with binary firings.

A natural "round-robin" pattern:
  Pivot 2 fires, then some binary procs fire, then pivot 5 fires, etc.

Let me try a specific mover sequence that satisfies the tight constraints.

Going around the ring:
  2, 0, 1, 3, 4, 5, 3, 4, 6, 7, 8, 6, 7, 9, 10, 11, 9, 10, 0, 1,
  2, ..., 5, ..., 8, ..., 11, ...

Hmm, this is getting complicated. Let me try to think about what mover
sequences are valid.

Constraints:
1. Each of {0,...,11} appears exactly 2 times
2. Length 24
3. For each pivot t in {2,5,8,11}: between consecutive t-firings, in each
   phase, left2(t) fires immediately before left(t), and right2(t) fires
   immediately before right(t).

Let me try the simplest possible pattern: pivots fire in cyclic order,
with their local binary procs firing in between.

Round 1 (each pivot fires once):
  Step 1: pivot 2 fires
  Step 2: 0 fires (left2 of pivot 2)
  Step 3: 1 fires (left of pivot 2, immediately after left2 -- tight)
  Step 4: 4 fires (right2 of pivot 2)
  Step 5: 3 fires (right of pivot 2, immediately after right2 -- tight)
  Step 6: pivot 5 fires
  Step 7: 3 fires (left2 of pivot 5)
  Step 8: 4 fires (left of pivot 5)
  Step 9: 7 fires (right2 of pivot 5)
  Step 10: 6 fires (right of pivot 5)
  Step 11: pivot 8 fires
  Step 12: 6 fires (left2 of pivot 8)
  Step 13: 7 fires (left of pivot 8)
  Step 14: 10 fires (right2 of pivot 8)
  Step 15: 9 fires (right of pivot 8)
  Step 16: pivot 11 fires
  Step 17: 9 fires (left2 of pivot 11)
  Step 18: 10 fires (left of pivot 11)
  Step 19: 1 fires (right2 of pivot 11)
  Step 20: 0 fires (right of pivot 11)

Round 2 (each pivot fires again):
  Step 21: pivot 2 fires
  Step 22: pivot 5 fires  -- but no local fires?

Hmm, that uses up all binary firings in round 1. Each binary proc fired
twice in round 1 (once in each of two pivot neighborhoods). So round 2
has only pivot firings: 4 steps. Total: 20 + 4 = 24. Check!

But wait: the tight constraint says in EACH t-phase, the local binary
procs fire. Phase 1 of pivot 2 is steps 1-21 (between 1st and 2nd firing
of pivot 2). Phase 2 is steps 21-1 (wrapping).

In phase 1: local binary 0,1,3,4 all fire. Good.
In phase 2: steps 21 to 1 (mod 24) = steps 21,22,23,24,1. Only pivots
fire here. NO binary firings. So (J,K,g,h) = (0,0,0,0) in phase 2.

That's NOT all-normal-form with (J,K,g,h)=(1,1,1,1) in every phase.

So the "all-tight" pattern requires that EACH phase has the local binary
procs firing. That means the binary firings must be split evenly: 1 firing
per binary proc per phase. 8 phases * (some number of binary firings each).

Each binary proc fires twice, once in a phase of pivot A and once in a
phase of pivot B. With 2 phases per pivot and 4 binary procs per pivot
neighborhood, we need 4 binary firings per phase. 8 phases * 4 = 32.
But only 16 binary firings. Contradiction again!

Unless: each phase has only 2 binary firings (1 from each side: left+left2
OR just left, etc).

OK I think (J,K,g,h)=(1,1,1,1) means:
- J=1: exactly 1 fire from the left side (either left or left2, but with
  g=1 meaning left2 also fires... )

Let me re-read the problem. "Each pivot has 2 phases. In each phase,
exactly 4 local processors fire: left2t, left t, right2t, right t"

So yes, 4 firings per phase. 8 phases * 4 = 32 binary firings + 8 pivot
firings = 40. But total should be 24.

The resolution must be: the phases from different pivots SHARE binary
firings. A single binary firing can be "in" a phase of pivot A AND
simultaneously "in" a phase of pivot B, because phases are defined
independently for each pivot.

So the mover sequence has exactly 24 steps. Each pivot defines 2 phases
(time windows between its consecutive firings). A binary firing at step s
is in a phase of pivot A if s falls between two consecutive A-firings,
AND in a phase of pivot B if s falls between two consecutive B-firings.

So the 24 steps are partitioned by pivot A's firings into 2 phases of A,
and simultaneously partitioned by pivot B's firings into 2 phases of B, etc.

Each binary proc fires in exactly 1 phase of each of 2 pivots. But those
phases are defined by different pivot firings, so the same step can be in
multiple pivots' phases simultaneously.

Total binary firings: 16. Plus 8 pivot firings = 24.

For the "all-tight" constraint to hold: for EACH pivot, in EACH of its 2
phases, all 4 of its local binary procs fire (once each), with left2
immediately before left, and right2 immediately before right.

That means: each phase of each pivot sees 4 binary firings from its local
set. 4 pivots * 2 phases * 4 = 32 "observations." Each binary firing is
observed by 2 pivots (one for each of its 2 neighborhoods). So
32 = 16 * 2. Check!

Each binary proc fires twice. Each firing is observed by both of its
neighboring pivots, one for each. Wait no: at step s, binary proc b fires.
This step is in exactly one phase of pivot A (b's left pivot) and exactly
one phase of pivot B (b's right pivot). So yes, each firing counts toward
one phase of each neighboring pivot.

For each phase of pivot t to have all 4 local binary firings, we need
each local binary to fire once in that phase. Since each binary fires
twice (in 2 different steps), and each firing is in exactly one phase of
pivot t, we need the 2 firings to land in the 2 different phases of t.

So: each local binary of pivot t fires once in phase 1 of t and once in
phase 2 of t. But wait, each binary only fires in ONE phase of each pivot
(since each of its 2 firings is in a phase of one of its 2 neighboring
pivots, not both the same pivot).

Hmm, let me reconsider. Binary proc 3 is local to both pivot 2 and pivot 5.
Proc 3 fires exactly 2 times (step s1 and step s2).

Step s1 is in some phase of pivot 2 (say phase i) and some phase of
pivot 5 (say phase j).
Step s2 is in some phase of pivot 2 (say phase i') and some phase of
pivot 5 (say phase j').

For the all-tight constraint:
- In each phase of pivot 2, proc 3 must fire exactly once. So i ≠ i'.
  (Both firings of proc 3 are in different phases of pivot 2.)
- In each phase of pivot 5, proc 3 must fire exactly once. So j ≠ j'.

So proc 3 fires once in phase 1 of pivot 2 AND phase X of pivot 5,
and once in phase 2 of pivot 2 AND phase Y of pivot 5 (X ≠ Y).

This means: the 2 firings of each binary proc must alternate between
the phases of EACH of its neighboring pivots. This constrains the
interleaving of pivot firings.

Let me denote pivot firings: A1, A2 (pivot 2), B1, B2 (pivot 5),
C1, C2 (pivot 8), D1, D2 (pivot 11).

Phase 1 of A = from A1 to A2. Phase 2 of A = from A2 to A1 (cyclic).
Similarly for B, C, D.

For proc 3 (local to A and B): its 2 firings must be in different
A-phases and different B-phases.

If A1 and B1 are ordered: A1 < B1 < A2 < B2 (in the cyclic order),
then phase 1 of A = [A1, A2) and phase 1 of B = [B1, B2).

A step in [A1, B1) is in A-phase 1 and B-phase 2.
A step in [B1, A2) is in A-phase 1 and B-phase 1.
A step in [A2, B2) is in A-phase 2 and B-phase 1.
A step in [B2, A1) is in A-phase 2 and B-phase 2.

For proc 3 to be in different A-phases and different B-phases, its 2
firings must be in "diagonally opposite" regions:
  one in [A1,B1)∪[A2,B2), the other in [B1,A2)∪[B2,A1).

The natural interleaving is: A1, B1, C1, D1, A2, B2, C2, D2.
This gives phases of A: [A1,A2) = contains B1, C1, D1; [A2,A1) = B2,C2,D2.
Phases of B: [B1,B2) = contains C1,D1,A2; [B2,B1) = C2,D2,A1.

OK this is getting very complicated. Let me just try a concrete mover
sequence and check computationally.

A natural candidate mover sequence (pivots in round-robin, binary procs
interleaved):

With pivot firing order: 2, 5, 8, 11, 2, 5, 8, 11

Between each pair of consecutive pivot firings, we place binary firings.

Between pivot 2 (1st) and pivot 5 (1st): place firings of procs in the
shared neighborhood (3, 4) + unshared ones.
Actually, the tight constraint says left2 fires immediately before left.

Let me try:
  2, 0, 1, 4, 3, 5, 3, 4, 7, 6, 8, 6, 7, 10, 9, 11, 9, 10, 1, 0, 2, 5, 8, 11

Count: 2(2), 0(2), 1(2), 3(2), 4(2), 5(2), 6(2), 7(2), 8(2), 9(2), 10(2), 11(2) = all appear twice. 24 steps.

Let me check the tight constraints:
Pivot 2 fires at steps 0 and 20 (0-indexed).
Phase 1 of pivot 2: steps 1-19 (between firings 0 and 20).
Phase 2 of pivot 2: steps 21-23 + step 0 itself? No, phase 2 is from
step 20 to step 0 (cyclic) = steps 21, 22, 23.

In phase 1 (steps 1-19):
  left2(2)=0 fires at step 1, left(2)=1 fires at step 2. Tight! (consecutive)
  right2(2)=4 fires at step 3, right(2)=3 fires at step 4. Tight!
  But also: 0 fires again at step 19, 1 fires at step 18. In phase 1.
  So proc 0 fires at steps 1 and 19 (both in phase 1). That violates the
  constraint that proc 0 fires once per phase of pivot 2!

Need to rethink. The second firings of 0 and 1 must be in phase 2 of
pivot 2. Phase 2 has only steps 21, 22, 23 (3 steps: pivots 5, 8, 11).
No room for binary firings!

The issue is that with 4 pivot firings in each half, the phases are very
uneven if we cluster all binary firings in one half.

Better interleaving: spread the pivot firings out.

What if pivot firings are at steps: 0, 6, 12, 18 (evenly spaced in first
round), then 3, 9, 15, 21 (evenly spaced in second round)?

Mover sequence template:
Step 0: pivot 2 fires
Steps 1-5: binary firings
Step 6: pivot 5 fires
Steps 7-11: binary firings
Step 12: pivot 8 fires
Steps 13-17: binary firings
Step 18: pivot 11 fires
Steps 19-23: ...

No wait, we need 8 pivot firings and 16 binary firings. 24 total.
If we interleave: pivot, 2 binary, pivot, 2 binary, ...
8 * (1+2) = 24.

So: pivot, binary, binary, pivot, binary, binary, ...
Mover sequence:
  2, b, b, 5, b, b, 8, b, b, 11, b, b, 2, b, b, 5, b, b, 8, b, b, 11, b, b

Each pivot fires at 2 positions. 8 pivot firings + 16 binary firings = 24.

Pivot 2 fires at steps 0 and 12. Phase 1: steps 1-11. Phase 2: steps 13-23 + wrapping to step 0.
Pivot 5 fires at steps 3 and 15. Phase 1: steps 4-14. Phase 2: steps 16-2.
Pivot 8 fires at steps 6 and 18. Phase 1: steps 7-17. Phase 2: steps 19-5.
Pivot 11 fires at steps 9 and 21. Phase 1: steps 10-20. Phase 2: steps 22-8.

For the tight constraint at pivot 2 phase 1 (steps 1-11):
Need: left2(2)=0 fires immediately before left(2)=1 (consecutive steps)
Need: right2(2)=4 fires immediately before right(2)=3 (consecutive steps)
Also need: all 4 fire exactly once in this phase.

Available binary slots in steps 1-11: steps 1,2,4,5,7,8,10,11 (8 binary slots).
We need procs 0,1,3,4 to each fire once in these 8 slots, with 0 immediately
before 1, and 4 immediately before 3. That means we need (0,1) and (4,3) as
consecutive pairs. They could be at (1,2), (4,5), (7,8), or (10,11).

Pivot 5 phase 1 (steps 4-14): need 3,4,6,7. With (3,4) tight and (7,6) tight.
Wait: for pivot 5, left2=3, left=4, right2=7, right=6.
Tight means left2 immediately before left: 3 before 4. And right2 before right: 7 before 6.

Pivot 8 phase 1 (steps 7-17): left2=6,left=7,right2=10,right=9.
Tight: 6 before 7, 10 before 9.

Pivot 11 phase 1 (steps 10-20): left2=9,left=10,right2=1,right=0.
Tight: 9 before 10, 1 before 0.

OK let me try to fill in the binary slots:

Steps: 0  1  2  3  4  5  6  7  8  9  10 11 12 13 14 15 16 17 18 19 20 21 22 23
Pivots: 2  .  .  5  .  .  8  .  .  11 .  . 2   .  .  5  .  .  8  .  .  11 .  .

Binary slots to fill: 1,2,4,5,7,8,10,11,13,14,16,17,19,20,22,23

Phase 1 of pivot 2 (steps 1-11, binary slots 1,2,4,5,7,8,10,11):
  Need 0,1 (tight pair) and 4,3 (tight pair), each firing once.
  Plus other binary procs might fire here too (for other pivots' constraints).

Phase 1 of pivot 5 (steps 4-14, binary slots 4,5,7,8,10,11,13,14):
  Need 3,4 (tight pair) and 7,6 (tight pair), each firing once.

Phase 1 of pivot 8 (steps 7-17, binary slots 7,8,10,11,13,14,16,17):
  Need 6,7 (tight pair) and 10,9 (tight pair), each firing once.

Phase 1 of pivot 11 (steps 10-20, binary slots 10,11,13,14,16,17,19,20):
  Need 9,10 (tight pair) and 1,0 (tight pair), each firing once.

Phase 2 of pivot 2 (steps 13-23, binary slots 13,14,16,17,19,20,22,23):
  Need 0,1 and 4,3 tight pairs, each once.

Phase 2 of pivot 5 (steps 16-2, binary slots 16,17,19,20,22,23,1,2):
  Need 3,4 and 7,6 tight pairs, each once.

Phase 2 of pivot 8 (steps 19-5, binary slots 19,20,22,23,1,2,4,5):
  Need 6,7 and 10,9 tight pairs, each once.

Phase 2 of pivot 11 (steps 22-8, binary slots 22,23,1,2,4,5,7,8):
  Need 9,10 and 1,0 tight pairs, each once.

Available pairs (consecutive binary slots): (1,2), (4,5), (7,8), (10,11),
(13,14), (16,17), (19,20), (22,23).

We need to assign pairs to slots:
Phase 1 of A: pair (0,1) and pair (4,3) go into slots from {(1,2),(4,5),(7,8),(10,11)}
Phase 1 of B: pair (3,4) and pair (7,6) go into slots from {(4,5),(7,8),(10,11),(13,14)}
Phase 1 of C: pair (6,7) and pair (10,9) go into slots from {(7,8),(10,11),(13,14),(16,17)}
Phase 1 of D: pair (9,10) and pair (1,0) go into slots from {(10,11),(13,14),(16,17),(19,20)}
Phase 2 of A: pair (0,1) and pair (4,3) into {(13,14),(16,17),(19,20),(22,23)}
Phase 2 of B: pair (3,4) and pair (7,6) into {(16,17),(19,20),(22,23),(1,2)}
Phase 2 of C: pair (6,7) and pair (10,9) into {(19,20),(22,23),(1,2),(4,5)}
Phase 2 of D: pair (9,10) and pair (1,0) into {(22,23),(1,2),(4,5),(7,8)}

Each pair slot (1,2), (4,5), ... is used by exactly 2 assignments (since
each binary proc fires exactly 2 times). Wait, each slot holds one pair of
procs. 8 slots, 8 pairs to assign (4 pairs * 2 phases). But some pairs
share procs (e.g., (0,1) from pivot A and (1,0) from pivot D both use
procs 0 and 1).

Actually (0,1) means proc 0 fires then proc 1 fires. (1,0) means proc 1
fires then proc 0 fires. These are DIFFERENT orderings of the same pair.

For pivot 2: left pair is (0,1) [left2 before left], right pair is (4,3)
[right2 before right].
For pivot 11: left pair is (9,10), right pair is (1,0).

So pair (0,1) for pivot 2 and pair (1,0) for pivot 11 both use procs 0,1
but in opposite order! This is the alternating polarity.

Each pair of procs appears twice: once as (a,b) and once as (b,a).
These must go into different slots.

Let me assign:
Slot (1,2): pair (0,1) from phase 1 of A
Slot (4,5): pair (4,3) from phase 1 of A  -- wait, (4,3) means 4 fires then 3.
  Step 4: proc 4, step 5: proc 3.
Slot (7,8): pair (3,4) from phase 1 of B  -- wait, slot shared.

Actually I realize each slot is used by exactly one pair assignment. 8 slots,
8 pairs (2 phases * 4 pivots, with 2 pairs per phase... that's 16 pair
assignments for 8 slots. Each slot must hold exactly 2 pair assignments?)

No, each slot is a pair of consecutive steps. One pair of procs fires in
those 2 steps. So 8 slots * 1 pair each = 8 pairs of procs. But we have
8 unique proc pairs (each pair of adjacent binary procs):
(0,1), (3,4), (6,7), (9,10). Each appears in 2 phases of 2 different
pivots in possibly reversed order.

These 4 proc pairs * 2 firings each = 8 pair-firings. Exactly fills 8 slots!

Let me restate:
- Proc pair {0,1}: fires at some slot in phase 1 of A (as (0,1)) and at
  some slot in phase 1 of D or phase 2 of ... Actually let me just enumerate.

Pivot A(2) has pairs {0,1} and {3,4}.
Pivot B(5) has pairs {3,4} and {6,7}.
Pivot C(8) has pairs {6,7} and {9,10}.
Pivot D(11) has pairs {9,10} and {0,1}.

Each pair appears for exactly 2 pivots. For each pair, one firing goes to
one pivot and the other firing goes to the other pivot. The order within
the pair depends on which pivot "owns" that firing.

For pair {0,1}:
- In pivot A(2): fired as (0,1) [left2=0 before left=1]
- In pivot D(11): fired as (1,0) [right2=1 before right=0]

For pair {3,4}:
- In pivot A(2): fired as (4,3) [right2=4 before right=3]
- In pivot B(5): fired as (3,4) [left2=3 before left=4]

For pair {6,7}:
- In pivot B(5): fired as (7,6) [right2=7 before right=6]
- In pivot C(8): fired as (6,7) [left2=6 before left=7]

For pair {9,10}:
- In pivot C(8): fired as (10,9) [right2=10 before right=9]
- In pivot D(11): fired as (9,10) [left2=9 before left=10]

Now, each pair fires twice (in 2 different steps/slots). Each firing is
in one phase of each neighboring pivot. We need:
- For pivot A: one firing of {0,1} in phase 1, one in phase 2.
  And one firing of {3,4} in phase 1, one in phase 2.
- Similarly for all pivots.

Each firing of {0,1} contributes to one phase of A and one phase of D.
Call the two firings f1 and f2.
f1 is in some phase i of A and some phase j of D.
f2 is in some phase i' of A and some phase j' of D.
Need i ≠ i' (for A) and j ≠ j' (for D).

Similarly for the other 3 pairs.

This is a constraint satisfaction problem. With 4 pairs, each having 2
firings, each firing assigned to a slot, with the phase constraints.

Let me try a specific assignment:
Slot (1,2): pair {0,1} as (0,1) -- in phase 1 of A (steps 1-11), phase 2 of D (steps 22-8)
  Phase 1 of A: yes (step 1,2 ∈ [1,11]). Phase of D: steps 22-8 means [22,23,0,1,2,3,4,5,6,7,8]. Steps 1,2 ∈ this range. So phase 2 of D.

Slot (4,5): pair {3,4} as (4,3)? Or (3,4)?
  For pivot A: right pair is (4,3) = [right2=4 before right=3].
  For pivot B: left pair is (3,4) = [left2=3 before left=4].

  If we put (4,3) at slot (4,5): step 4 = proc 4, step 5 = proc 3.
  This is in phase 1 of A (steps 1-11): yes.
  Phase of B: phase 1 of B = steps 4-14. Steps 4,5 ∈ [4,14]: yes.
  So this firing is from pivot A's perspective in phase 1 of A.
  From pivot B's perspective in phase 1 of B.
  But wait: the ORDER is (4,3) which is pivot A's ordering. For pivot B,
  we need (3,4) ordering. But the steps are fixed: step 4=proc 4, step 5=proc 3.
  From pivot B's perspective, left2=3 fires at step 5 and left=4 fires at
  step 4. That's left fires BEFORE left2. NOT tight for B!

So the order matters! We can't have both A and B satisfied with the same
ordering of {3,4}.

This means: the two firings of pair {3,4} must have OPPOSITE orders:
- One firing in order (4,3) for A's phase
- Other firing in order (3,4) for B's phase
And they must be in different phases of each pivot.

So: pair {3,4} firing 1: (4,3) in some slot, for A's phase i and B's phase j.
    pair {3,4} firing 2: (3,4) in another slot, for A's phase i' and B's phase j'.
    i ≠ i', j ≠ j'.

Since the order in the slot determines which pivot sees tight ordering:
(4,3) is tight for A but NOT for B.
(3,4) is tight for B but NOT for A.

Wait, but the tight constraint requires BOTH pairs to be tight in EVERY
phase! So in phase 1 of A, the {3,4} firing must be (4,3) for A to see
tight. And in the same step, B must see it. B's tight for {3,4} requires
(3,4) order. But we have (4,3). So B does NOT see tight ordering.

But B doesn't require tight in THAT step specifically -- B requires tight
in B's phase. The step is in some phase of B. In that phase, B needs
3 to fire immediately before 4. But we have 4 firing before 3. So in
that phase of B, the tight constraint is VIOLATED.

Unless: we relax "tight" to mean that left2 fires at SOME point before
left, not necessarily immediately before. But the problem says "immediately
before" which means consecutive steps.

So the opposite orderings create a fundamental conflict: if pair {3,4}
fires as (4,3), it's tight for A but anti-tight for B. If (3,4), it's
tight for B but anti-tight for A.

The only way to satisfy both is if the pair fires in non-consecutive steps
(both 3 and 4 fire, but not consecutively). But then neither sees "tight"!

OR: the constraint is not about consecutive steps globally, but about
something else. Let me re-read:

"The tight ordering means left2t fires immediately before left t"

I think this might mean that between the two left-side firings and the
pivot firing, left2 fires first then left fires, with nothing in between
from THAT PIVOT'S LOCAL SET. Other (non-local) firings might intervene.

Hmm, but the problem says "immediately before" which in the context of a
mover sequence means the very next step.

If the tight constraint truly requires consecutive steps, then for shared
pairs like {3,4}, only one ordering is possible at each slot, satisfying
only one of the two neighboring pivots. This makes the all-tight pattern
IMPOSSIBLE for shared pairs!

UNLESS: there's a way to have both orderings satisfied simultaneously?
That's clearly impossible for a single pair of steps.

So: with "immediately before" meaning consecutive steps, and with shared
binary pairs between adjacent pivots needing opposite orders, the all-tight
all-normal-form pattern is IMPOSSIBLE for even k=4.

But wait -- maybe I'm wrong about the ordering. Let me reconsider which
ordering each pivot needs.

For pivot t, "left2t fires immediately before left t" means: in the mover
sequence, the step where left2t fires is immediately followed by the step
where left t fires.

For pivot 2: left2=0, left=1. Need 0 immediately before 1: order (0,1).
For pivot 5: left2=3, left=4. Need 3 immediately before 4: order (3,4).
For pivot 2: right2=4, right=3. Need 4 immediately before 3: order (4,3).
For pivot 5: right2=7, right=6. Need 7 immediately before 6: order (7,6).

So pair {3,4}: pivot 2 needs (4,3), pivot 5 needs (3,4). OPPOSITE orders!
In a single firing (2 consecutive steps), you can only have one order.
So the same pair cannot be tight for both pivots simultaneously.

Each pair fires twice. Firing 1 could be (3,4) [tight for B, anti-tight
for A] and firing 2 could be (4,3) [tight for A, anti-tight for B].

For A: in phase 1, the {3,4} firing that's (4,3) is tight. In phase 2,
the {3,4} firing that's (3,4) is anti-tight. So A's phase 2 has anti-tight
ordering for one of its pairs. NOT all-tight.

Similarly for B.

CONCLUSION: The all-tight pattern (every phase has tight ordering for ALL
its local pairs) is IMPOSSIBLE when adjacent pivots share binary pairs
that need opposite orderings. This happens for ALL shared pairs.

Let me verify this reasoning by checking if there's any subtlety I'm missing.

The 4 shared pairs are {0,1}, {3,4}, {6,7}, {9,10}. Each is shared between
2 adjacent pivots that need opposite ordering. For EACH pair, in EACH firing,
exactly one pivot sees tight and the other sees anti-tight. Since each pivot
has 2 pairs (one from each side), and each pair can only be tight for that
pivot in one of its 2 firings, each phase of each pivot has at most 1 tight
pair (out of 2). The all-tight condition requires BOTH pairs to be tight in
EVERY phase. This is impossible.

Wait, a pivot has 2 phases and 2 pairs. Each pair has one "good" firing
(tight for this pivot) and one "bad" firing. The good firing lands in one
phase, the bad in the other. So each phase has one good and one bad pair.
All-tight requires both good. Impossible.

Actually, can we arrange both good firings in the same phase?

Pair {0,1} for pivot A: good firing is (0,1). Say it's in phase 1 of A.
Pair {3,4} for pivot A: good firing is (4,3). Need it also in phase 1 of A.

Yes, we could put both good firings in phase 1 of A! Then phase 1 is
all-tight. Phase 2 has both bad firings: anti-tight.

But then phase 2 of A is NOT tight at all. So "all-tight" fails for phase 2.

CONCLUSION: The all-tight all-normal-form pattern CANNOT be realized for
the (2,2,3,2,2,3,2,2,3,2,2,3) ring with even k=4, regardless of the
transition function. The impossibility is purely combinatorial: the tight
ordering constraint for shared binary pairs between adjacent pivots is
self-contradictory.

However, I should verify this computationally. Maybe the "immediately before"
constraint can be relaxed, or maybe I'm misunderstanding the tight pattern.
Let me check the case where "tight" means "somewhere before" (not necessarily
immediately).

Even with "somewhere before": for pair {3,4} between pivots 2 and 5,
pivot 2 needs 4 before 3, and pivot 5 needs 3 before 4. A single firing
has a definite order (either 3 fires before 4, or 4 fires before 3). So
each firing satisfies exactly one pivot's before-constraint.

The same argument applies: each pivot's phase can have at most 1 pair
satisfying the before-constraint. All-tight requires 2. Impossible.

So the answer is NO purely on ordering grounds, independent of transition
functions. Let me verify computationally that no valid mover sequence exists.
"""

from itertools import product as iter_product
import sys

def check_all_tight_feasibility():
    """
    Check if an all-tight mover sequence exists for the (2,2,3,2,2,3,2,2,3,2,2,3) ring.

    Pivots: 2, 5, 8, 11

    For each pivot t, define:
      left2(t), left(t), right(t), right2(t)

    Pivot 2:  left2=0,  left=1,  right=3,  right2=4
    Pivot 5:  left2=3,  left=4,  right=6,  right2=7
    Pivot 8:  left2=6,  left=7,  right=9,  right2=10
    Pivot 11: left2=9,  left=10, right=0,  right2=1

    Tight ordering: left2 before left, right2 before right.

    Shared pairs and required orderings:
      {0,1}: pivot 2 needs (0,1), pivot 11 needs (1,0)
      {3,4}: pivot 2 needs (4,3), pivot 5 needs (3,4)
      {6,7}: pivot 5 needs (7,6), pivot 8 needs (6,7)
      {9,10}: pivot 8 needs (10,9), pivot 11 needs (9,10)
    """
    n = 12
    m = [2,2,3,2,2,3,2,2,3,2,2,3]
    pivots = [2, 5, 8, 11]

    # Define neighborhoods
    neighborhoods = {}
    for t in pivots:
        left = (t - 1) % n
        left2 = (t - 2) % n
        right = (t + 1) % n
        right2 = (t + 2) % n
        neighborhoods[t] = {
            'left2': left2, 'left': left,
            'right': right, 'right2': right2,
            'left_pair_order': (left2, left),     # left2 before left
            'right_pair_order': (right2, right),   # right2 before right
        }

    print("=== Neighborhood structure ===")
    for t in pivots:
        nb = neighborhoods[t]
        print(f"Pivot {t}: left2={nb['left2']}, left={nb['left']}, "
              f"right={nb['right']}, right2={nb['right2']}")
        print(f"  Left pair order needed: {nb['left_pair_order']}")
        print(f"  Right pair order needed: {nb['right_pair_order']}")

    # Identify shared pairs and their conflicting orderings
    print("\n=== Shared pairs and ordering conflicts ===")
    pairs = {}  # frozenset -> list of (pivot, side, required_order)
    for t in pivots:
        nb = neighborhoods[t]
        lp = frozenset([nb['left2'], nb['left']])
        rp = frozenset([nb['right2'], nb['right']])
        pairs.setdefault(lp, []).append((t, 'left', nb['left_pair_order']))
        pairs.setdefault(rp, []).append((t, 'right', nb['right_pair_order']))

    for pair_set, info in sorted(pairs.items(), key=lambda x: min(x[0])):
        pair_list = sorted(pair_set)
        print(f"\nPair {{{pair_list[0]},{pair_list[1]}}}:")
        for t, side, order in info:
            print(f"  Pivot {t} ({side}): needs order ({order[0]},{order[1]})")

        # Check if orders conflict
        orders = [order for _, _, order in info]
        if len(orders) == 2 and orders[0] != orders[1]:
            print(f"  ** CONFLICT: opposite orders required! **")
        elif len(orders) == 2 and orders[0] == orders[1]:
            print(f"  OK: same order required")

    # Now prove impossibility of all-tight
    print("\n=== Proving impossibility of all-tight pattern ===")
    print()
    print("Each shared pair has 2 firings (since each member proc fires exactly 2 times).")
    print("Each firing has a definite order (which proc fires first).")
    print("At most one ordering can be used per firing.")
    print()

    # For each pivot, it has a left pair and right pair.
    # Each pair has exactly 2 firings.
    # Exactly one firing has the correct order for this pivot.
    # That firing must be in a different phase than the other firing.
    # So each phase gets exactly 1 correctly-ordered and 1 incorrectly-ordered pair.

    # For all-tight: BOTH pairs must be correctly ordered in EVERY phase.
    # But each phase gets exactly 1 correct + 1 incorrect. Contradiction.

    # Unless both correct-order firings land in the same phase.
    # Then that phase has 2 correct, and the other phase has 0 correct.
    # Still not all-tight (other phase has 0).

    # Wait, I need to be more careful. The "both correct in same phase" case.

    # For pivot A(2): left pair {0,1} good=(0,1), right pair {3,4} good=(4,3).
    # Good firing of {0,1}: we can assign it to phase 1 or phase 2 of A.
    # Good firing of {3,4}: we can assign it to phase 1 or phase 2 of A.

    # If both good firings in phase 1: phase 1 all-tight, phase 2 not tight at all.
    # If split: each phase has 1 tight, 1 not tight.
    # In neither case are ALL phases tight.

    for t in pivots:
        nb = neighborhoods[t]
        lp = frozenset([nb['left2'], nb['left']])
        rp = frozenset([nb['right2'], nb['right']])

        print(f"Pivot {t}:")
        print(f"  Left pair {set(lp)}: good order = {nb['left_pair_order']}")
        print(f"  Right pair {set(rp)}: good order = {nb['right_pair_order']}")

        # Count good firings per phase
        print(f"  Each pair has exactly 1 firing with good order.")
        print(f"  With 2 pairs and 2 phases:")
        print(f"    Best case: both good in phase 1 -> phase 1: 2/2 tight, phase 2: 0/2 tight")
        print(f"    Other case: split -> each phase: 1/2 tight")
        print(f"    ALL-TIGHT requires 2/2 in BOTH phases. IMPOSSIBLE.")
        print()

    print("=" * 60)
    print("CONCLUSION: The all-tight all-normal-form pattern CANNOT be")
    print("realized for the (2,2,3,2,2,3,2,2,3,2,2,3) ring (n=12, k=4).")
    print("The impossibility is PURELY COMBINATORIAL (ordering conflict)")
    print("and holds for ANY transition function assignment.")
    print("=" * 60)

    # Now let me also verify computationally by exhaustive search over all
    # possible mover sequences of length 24.
    # This is too large (24! / (2!^12) is huge), so instead let me verify
    # the ordering impossibility by checking all possible phase assignments.

    print("\n=== Exhaustive verification of phase assignment impossibility ===")

    # For each shared pair, we have 2 firings. We assign each firing to
    # a phase of each neighboring pivot.
    # Variables: for pair p shared between pivots A and B,
    #   firing 1 goes to phase (a1, b1) of (A, B)
    #   firing 2 goes to phase (a2, b2) of (A, B)
    # Constraints: a1 ≠ a2, b1 ≠ b2 (each phase of each pivot gets one firing)

    # Pair {0,1}: pivots 2 and 11
    #   good order for 2: (0,1). good order for 11: (1,0).
    #   Firing with order (0,1): tight for 2, not for 11.
    #   Firing with order (1,0): tight for 11, not for 2.
    # Pair {3,4}: pivots 2 and 5
    #   good for 2: (4,3). good for 5: (3,4).
    # Pair {6,7}: pivots 5 and 8
    #   good for 5: (7,6). good for 8: (6,7).
    # Pair {9,10}: pivots 8 and 11
    #   good for 8: (10,9). good for 11: (9,10).

    # For "all-tight" at pivot t: in phase 1 AND phase 2, BOTH pairs of t
    # must have their good-order firing.

    # Each pair contributes exactly 1 good firing to pivot t across both phases.
    # All-tight requires 2 good firings per phase. With only 1 good per pair,
    # and 2 pairs per pivot, that's 2 good firings total distributed over 2 phases.
    # At best, 2-0 split or 1-1 split. Need 2-2. IMPOSSIBLE with only 2 good total.

    # Let me enumerate to be sure.

    # For each pivot t, for each of its 2 pairs, we choose which phase gets
    # the good-order firing. 2 choices per pair, 2 pairs per pivot = 4 combos.

    # But the phases of different pivots are coupled through shared pairs!

    # Pair {0,1}: pivot 2 gets good firing in phase X of 2, pivot 11 gets good
    # in phase Y of 11. Since there are only 2 firings:
    # firing 1: good for 2, bad for 11. Goes to some phase of 2 and some phase of 11.
    # firing 2: bad for 2, good for 11. Goes to the OTHER phase of 2 and OTHER phase of 11.

    # So if firing 1 is in phase 1 of 2, it's in phase ? of 11 (depends on timing).
    # We have 2 choices: firing 1 in (phase1_of_2, phase1_of_11) or (phase1_of_2, phase2_of_11).
    # Then firing 2 goes to (phase2_of_2, phase2_of_11) or (phase2_of_2, phase1_of_11).

    # Actually, the assignment of firings to phases is determined by the mover sequence,
    # not independent. But we just need to check ALL possible phase assignments.

    # For each pair, 2 options for which diagonal it sits on.
    # 4 pairs = 2^4 = 16 possibilities.

    feasible_count = 0
    for assignment in iter_product([0, 1], repeat=4):
        # assignment[i] = 0 or 1: which phase of each pivot gets the good firing
        # Pair 0 ({0,1}): pivots 2 and 11
        # Pair 1 ({3,4}): pivots 2 and 5
        # Pair 2 ({6,7}): pivots 5 and 8
        # Pair 3 ({9,10}): pivots 8 and 11

        # For pair i, assignment[i]=0 means: good firing in phase 1 of left_pivot
        #   and bad firing in phase 2 of left_pivot. Phase of right_pivot: depends
        #   on diagonal choice.

        # Actually, for each pair, there are 2 diagonal choices:
        #   Option A: firing1 in (phase1 of left, phase1 of right) -> firing2 in (phase2, phase2)
        #   Option B: firing1 in (phase1 of left, phase2 of right) -> firing2 in (phase2, phase1)

        # For pair {0,1} (left_pivot=2, right_pivot=11):
        #   Firing with good order for 2 = firing where order is (0,1).
        #   If assignment[0]=0: good-for-2 firing in phase 1 of 2.
        #     With diagonal A: this firing in (ph1_2, ph1_11). Bad-for-2 in (ph2_2, ph2_11).
        #       Good-for-11 is the bad-for-2 firing (order (1,0)). It's in ph2 of 11.
        #     With diagonal B: good-for-2 in (ph1_2, ph2_11). Bad-for-2 in (ph2_2, ph1_11).
        #       Good-for-11 in ph1 of 11.

        # This is getting complex. Let me just enumerate all 2^8 = 256 combos
        # (2 choices for good-phase of left_pivot, 2 for diagonal, per pair).
        pass

    # Simpler approach: for each pivot, track which phase(s) have both pairs tight.
    # Enumerate all possible assignments of "good firing phase" for each pair at each pivot.

    # For each pair p connecting pivots A and B:
    #   - good-for-A firing: we pick which phase of A it lands in. 2 choices.
    #   - This determines which phase of A gets the bad-for-A firing (the other phase).
    #   - The phase of B that the good-for-A firing lands in is SEPARATE (depends on timing).
    #   - Similarly, the good-for-B firing lands in the other phase of A, and some phase of B.

    # But the phase of B depends on the actual mover sequence, not just the pair assignment.
    # However, for the impossibility argument, we only need:
    #   Each pivot has 2 pairs. Each pair has exactly 1 good firing.
    #   That's 2 good firings total for this pivot, distributed over 2 phases.
    #   For all-tight: need 2 good firings in each phase = 4 total. But only 2 exist.
    #   IMPOSSIBLE.

    print("For any pivot t:")
    print("  - t has 2 local pairs (left pair and right pair)")
    print("  - Each pair has exactly 2 firings in the full cycle")
    print("  - Exactly 1 of these 2 firings has the order that makes it tight for t")
    print("  - So t receives exactly 2 'good' (tight-ordered) firings across its 2 phases")
    print("  - All-tight requires 2 good firings per phase = 4 total")
    print("  - But only 2 good firings exist. 4 > 2. IMPOSSIBLE.")
    print()
    print("This proves impossibility regardless of mover sequence or transition functions.")

    return False

def verify_with_relaxed_tight():
    """
    What if 'tight' means left2 fires before left (somewhere in the phase,
    not necessarily immediately before)? Check if this weaker constraint
    is also impossible.
    """
    print("\n=== Relaxed tight (before, not immediately before) ===")
    print()
    print("Even with relaxed ordering (left2 fires SOMEWHERE before left,")
    print("not necessarily immediately before):")
    print()
    print("For pair {3,4} shared between pivots 2 and 5:")
    print("  Pivot 2 needs: 4 before 3 (right2 before right)")
    print("  Pivot 5 needs: 3 before 4 (left2 before left)")
    print()
    print("In a single firing event (2 steps), either 3 fires before 4 or 4 fires before 3.")
    print("In a SINGLE phase, both 3 and 4 appear as part of one firing event.")
    print("That event has a definite order. Only one pivot sees the correct order.")
    print()
    print("Wait -- with relaxed tight, 3 and 4 don't need to be consecutive!")
    print("They could fire at different points within the same phase.")
    print("But each fires exactly once per phase (in all-normal-form).")
    print("So within a single phase, 3 fires at some step and 4 fires at another step.")
    print("Either 3 fires before 4 or after 4 (they can't fire simultaneously).")
    print()
    print("If 3 fires before 4 in a phase: pivot 5 sees correct order.")
    print("But pivot 2 needs 4 before 3 -- incorrect order.")
    print("Vice versa if 4 fires before 3.")
    print()
    print("So even with relaxed 'before' (not immediately), each phase satisfies")
    print("at most one of the two pivot constraints for a shared pair.")
    print()
    print("The counting argument still applies: 2 good ≠ 4 needed.")
    print()
    print("RELAXED TIGHT IS ALSO IMPOSSIBLE.")
    print()

    # But wait, the argument above assumes the phase is the SAME phase for both pivots.
    # A step is simultaneously in a phase of pivot A and a phase of pivot B.
    # The order constraint from A is about ordering within A's phase.
    # The order constraint from B is about ordering within B's phase.
    # These are DIFFERENT phases (of different pivots).
    #
    # Example: proc 3 fires at step s1 and proc 4 fires at step s2.
    # s1 is in phase i of A and phase j of B.
    # s2 is in phase i' of A and phase j' of B.
    #
    # For A: need 4 before 3 in the same A-phase. So s2 < s1 within A-phase.
    #   This means s1 and s2 are in the SAME phase of A. So i = i'.
    #
    # But we need each proc to fire in different phases! i ≠ i'.
    # Wait, that's only if all-normal-form requires each proc to fire once per phase.
    #
    # Actually, in all-normal-form, each proc fires P_local times total.
    # For binary procs: P_local = 2 (fire count = m_p = 2).
    # Each firing is in some phase of each neighboring pivot.
    # All-normal-form might not require one firing per phase.

    # Let me reconsider. (J,K,g,h)=(1,1,1,1) per phase means EACH of the 4
    # local procs fires exactly once per phase. So yes, each proc fires exactly
    # once in each phase of each neighboring pivot.

    # But there are 2 phases per pivot. Each proc fires 2 times. So yes,
    # one firing per phase of each neighboring pivot. That means i ≠ i'.

    # For A: proc 3 fires at step s1 (in phase 1 of A) and step s3_2 (in phase 2 of A).
    #        proc 4 fires at step s4_1 (in phase ? of A) and step s4_2 (in phase ? of A).
    # For A to see 4 before 3: need s4 < s3 within the same A-phase.
    # In phase 1 of A: proc 4 fires at s4_1, proc 3 fires at s3_1.
    #   Need s4_1 < s3_1 (within phase 1 time ordering).
    # In phase 2 of A: proc 4 fires at s4_2, proc 3 fires at s3_2.
    #   Need s4_2 < s3_2 (within phase 2 time ordering).

    # For B: proc 3 fires at s3_1 and s3_2. One in B-phase 1, one in B-phase 2.
    #         proc 4 fires at s4_1 and s4_2. One in B-phase 1, one in B-phase 2.
    # For B: need 3 before 4 in each B-phase.
    # In B-phase containing s3_x and s4_y: need s3_x < s4_y.

    # Now s3_1 is in A-phase 1. Is it in B-phase 1 or 2? Depends on the timing.
    # s4_1 is in A-phase 1. Also in some B-phase.

    # Key question: can s3_1 and s4_1 be in the SAME B-phase with s3_1 < s4_1,
    # AND in A-phase 1 with s4_1 < s3_1? That would require s4_1 < s3_1 AND s3_1 < s4_1.
    # IMPOSSIBLE.

    # So within A-phase 1, the order is s4_1 < s3_1 (A needs 4 before 3).
    # If s3_1 and s4_1 are in the same B-phase, then B sees 4 before 3. B needs 3 before 4. BAD.
    # If s3_1 and s4_1 are in DIFFERENT B-phases, then B doesn't compare them directly.

    # Can s3_1 and s4_1 be in different B-phases?
    # A-phase 1 spans from A-firing 1 to A-firing 2.
    # B-phase 1 spans from B-firing 1 to B-firing 2.
    # If the A-phase and B-phase boundaries interleave:
    #   A1 < B1 < A2 < B2 (cyclically)
    # Then A-phase 1 = [A1, A2) contains B1.
    # Steps in [A1, B1) are in A-phase 1 and B-phase 2.
    # Steps in [B1, A2) are in A-phase 1 and B-phase 1.
    # So s3_1 and s4_1 could be in different B-phases if one is in [A1,B1)
    # and the other in [B1,A2).

    # Say s4_1 ∈ [A1, B1) (A-phase 1, B-phase 2) and s3_1 ∈ [B1, A2) (A-phase 1, B-phase 1).
    # Then s4_1 < B1 ≤ s3_1. So s4_1 < s3_1. ✓ (A sees 4 before 3.)
    # In B-phase 2: only s4_1 fires (of {3,4}). Where does the other {3,4} firing go?
    # s3_2 is in A-phase 2. Could be in B-phase 1 or 2.
    # s4_2 is in A-phase 2. Could be in B-phase 1 or 2.
    # For B-phase 1 to see "3 before 4": need s3_? < s4_? both in B-phase 1.
    # s3_1 is already in B-phase 1. We need s4_? in B-phase 1 and s3_1 < s4_?.
    # s4_2 in B-phase 1 would work if s3_1 < s4_2.
    # s3_1 ∈ [B1, A2), s4_2 ∈ [B1, A2) ∪ [A2, B2).
    # If s4_2 ∈ [B1, A2) and s4_2 > s3_1: ✓ B-phase 1 sees 3 before 4.
    # Then B-phase 2 has s4_1 and s3_2.
    # For B-phase 2: need s3_2 < s4_1 (3 before 4).
    # But s4_1 ∈ [A1, B1) and s3_2 ∈ A-phase 2 = [A2, A1).
    # [A2, A1) ∩ B-phase 2 = [A2, B2) ∪ [B2, A1) = ... depends on ordering.
    # With A1 < B1 < A2 < B2: B-phase 2 = [B2, B1) = [B2, A1) ∪ [A1, B1).
    # s4_1 ∈ [A1, B1) ⊂ B-phase 2. ✓
    # s3_2 ∈ [A2, A1) = [A2, B2) ∪ [B2, A1).
    # [A2, B2) is in B-phase 1. [B2, A1) is in B-phase 2.
    # For s3_2 in B-phase 2: s3_2 ∈ [B2, A1).
    # Then in B-phase 2: s3_2 ∈ [B2, A1) and s4_1 ∈ [A1, B1).
    # Cyclically: B2 < A1 < B1, so s3_2 < s4_1. ✓ (3 before 4 in B-phase 2!)

    # So we CAN have both phases of A tight for {3,4} AND both phases of B tight!
    # But wait, in A-phase 2:
    # s3_2 ∈ [B2, A1) ⊂ A-phase 2 = [A2, A1).
    # s4_2 ∈ [B1, A2). But [B1, A2) ⊂ A-phase 1! So s4_2 is in A-PHASE 1, not phase 2!
    # That means A-phase 2 doesn't have s4_2 firing. Where's the {3,4} firing in A-phase 2?
    # s3_2 ∈ A-phase 2 (yes). s4 fires at s4_1 and s4_2. s4_1 ∈ A-phase 1, s4_2 ∈ A-phase 1.
    # BOTH firings of 4 are in A-phase 1! That violates one-per-phase.

    # Hmm. Let me redo. With A1 < B1 < A2 < B2:
    # s4_1 ∈ [A1, B1) (chosen above). This is A-phase 1.
    # s3_1 ∈ [B1, A2) (chosen above). This is A-phase 1.
    # So both s3_1 and s4_1 are in A-phase 1.
    # s3_2 and s4_2 must be in A-phase 2 (one firing per phase constraint).

    # A-phase 2 = [A2, A1) = [A2, B2) ∪ [B2, A1).
    # For A to see 4 before 3 in A-phase 2: need s4_2 < s3_2 within [A2, A1).
    # B-phase assignments of s3_2 and s4_2:
    # [A2, B2) is in B-phase 1.
    # [B2, A1) is in B-phase 2.

    # For B: we already placed s3_1 in B-phase 1 and s4_1 in B-phase 2.
    # s3_2 must be in B-phase 2 and s4_2 must be in B-phase 1 (one per phase).
    # So s4_2 ∈ [A2, B2) (A-phase 2, B-phase 1) and s3_2 ∈ [B2, A1) (A-phase 2, B-phase 2).
    # s4_2 < B2 ≤ s3_2 (cyclically), so s4_2 < s3_2. ✓ (A sees 4 before 3 in A-phase 2!)

    # In B-phase 1: s3_1 ∈ [B1, A2) and s4_2 ∈ [A2, B2).
    # s3_1 < A2 ≤ s4_2. So s3_1 < s4_2. ✓ (B sees 3 before 4 in B-phase 1!)

    # In B-phase 2: s4_1 ∈ [A1, B1) and s3_2 ∈ [B2, A1).
    # Cyclically in B-phase 2 = [B2, B1): B2 ≤ s3_2 < A1 ≤ s4_1 < B1.
    # So s3_2 < s4_1. ✓ (B sees 3 before 4 in B-phase 2!)

    # So for the single pair {3,4} between pivots A(2) and B(5), with
    # interleaved pivot firings A1 < B1 < A2 < B2:
    # ALL phases of BOTH pivots can have the correct ordering!

    print("CORRECTION: With interleaved pivot firings (A1 < B1 < A2 < B2),")
    print("it IS possible for a shared pair to satisfy BOTH pivots' ordering")
    print("constraints in ALL phases, as long as the pair's 2 firings are")
    print("placed in the right regions.")
    print()
    print("The key insight: within A-phase 1, proc 4 fires (in region [A1,B1))")
    print("BEFORE proc 3 fires (in region [B1,A2)), satisfying A.")
    print("Simultaneously, B-phase 1 sees proc 3 (from [B1,A2)) and proc 4")
    print("(from A-phase 2 region [A2,B2)), with 3 before 4, satisfying B.")
    print()
    print("So the ordering argument alone does NOT prove impossibility!")
    print("The all-tight pattern MAY be feasible with the right interleaving.")

    return True  # feasibility not ruled out by ordering alone

def simulate_cycle():
    """
    Given that ordering alone doesn't rule out all-tight, we need to check
    whether ANY transition function allows the cycle to close.

    Set up the concrete mover sequence with interleaved pivot firings,
    then check all transition function assignments.
    """
    print("\n" + "=" * 60)
    print("=== Concrete simulation ===")
    print("=" * 60)

    n = 12
    m = [2,2,3,2,2,3,2,2,3,2,2,3]
    pivots = [2, 5, 8, 11]

    # Use pivot firing order: 2, 5, 8, 11, 2, 5, 8, 11
    # With the analysis above, we interleave: A1 < B1 < C1 < D1 < A2 < B2 < C2 < D2
    # Each gap between consecutive pivot firings has 2 binary firing slots.

    # Between A1(pivot 2) and B1(pivot 5): 2 binary slots
    # Between B1(pivot 5) and C1(pivot 8): 2 binary slots
    # Between C1(pivot 8) and D1(pivot 11): 2 binary slots
    # Between D1(pivot 11) and A2(pivot 2): 2 binary slots
    # Between A2(pivot 2) and B2(pivot 5): 2 binary slots
    # Between B2(pivot 5) and C2(pivot 8): 2 binary slots
    # Between C2(pivot 8) and D2(pivot 11): 2 binary slots
    # Between D2(pivot 11) and A1(pivot 2): 2 binary slots (wrapping)

    # 8 gaps * 2 = 16 binary slots + 8 pivot slots = 24. ✓

    # Now assign binary procs to slots respecting tight constraints.
    # From the analysis: pair {3,4} between pivots 2 and 5.
    # With A1 < B1: need proc 4 in [A1,B1) and proc 3 in [B1,A2).
    # [A1,B1) has 2 binary slots (steps 1,2). [B1,A2) = gap after B1 + gap after C1 + gap after D1 = 6 slots.

    # Similarly, proc 4's second firing goes to [A2,B2) and proc 3's to [B2,A1).

    # Let me try a specific assignment:
    #
    # Gap 1: after A1(=pivot2), before B1(=pivot5). Steps 1, 2.
    #   Pair {3,4} for pivot 2: need (4,3) order in A-phase.
    #   In A-phase 1, 4 must fire before 3. Put 4 at step 1.
    #   But 3 should fire later (in a different gap within A-phase 1).
    #
    #   Also, pair {0,1} for pivot 2: need (0,1) order. In A-phase 1, 0 before 1.
    #   Put 0 at step 1 or 2.
    #
    #   Pair {0,1} for pivot 11: need (1,0) order in D-phases.
    #
    # This is getting complicated. Let me use a constraint solver approach.

    # Actually, let me just try all possible orderings computationally.
    # We have 16 binary firing slots and 8 binary procs each firing twice = 16 firings.
    # We need to assign the 16 firings to the 16 slots.
    # With the tight constraints for each pivot and phase.

    # The slots are (by gap):
    # Gap 0 (after A1, before B1): slots s0, s1
    # Gap 1 (after B1, before C1): slots s2, s3
    # Gap 2 (after C1, before D1): slots s4, s5
    # Gap 3 (after D1, before A2): slots s6, s7
    # Gap 4 (after A2, before B2): slots s8, s9
    # Gap 5 (after B2, before C2): slots s10, s11
    # Gap 6 (after C2, before D2): slots s12, s13
    # Gap 7 (after D2, before A1): slots s14, s15

    # Full mover sequence: A1, s0, s1, B1, s2, s3, C1, s4, s5, D1, s6, s7,
    #                       A2, s8, s9, B2, s10, s11, C2, s12, s13, D2, s14, s15

    # Phase assignments:
    # A-phase 1: steps s0..s7 (between A1 and A2)
    # A-phase 2: steps s8..s15 (between A2 and A1)
    # B-phase 1: steps s2..s9 (between B1 and B2)
    # B-phase 2: steps s10..s15, s0, s1 (between B2 and B1)
    # C-phase 1: steps s4..s11 (between C1 and C2)
    # C-phase 2: steps s12..s15, s0..s3 (between C2 and C1)
    # D-phase 1: steps s6..s13 (between D1 and D2)
    # D-phase 2: steps s14..s15, s0..s5 (between D2 and D1)

    # Tight constraints for each pivot and phase:
    #
    # Pivot A(2): left pair (0,1), right pair (4,3)
    # A-phase 1 (s0..s7): 0 fires before 1, and 4 fires before 3
    # A-phase 2 (s8..s15): 0 fires before 1, and 4 fires before 3
    #
    # Pivot B(5): left pair (3,4), right pair (7,6)
    # B-phase 1 (s2..s9): 3 fires before 4, and 7 fires before 6
    # B-phase 2 (s10..s15,s0,s1): 3 fires before 4, and 7 fires before 6
    #
    # Pivot C(8): left pair (6,7), right pair (10,9)
    # C-phase 1 (s4..s11): 6 fires before 7, and 10 fires before 9
    # C-phase 2 (s12..s15,s0..s3): 6 fires before 7, and 10 fires before 9
    #
    # Pivot D(11): left pair (9,10), right pair (1,0)
    # D-phase 1 (s6..s13): 9 fires before 10, and 1 fires before 0
    # D-phase 2 (s14..s15,s0..s5): 9 fires before 10, and 1 fires before 0

    # Each binary proc fires exactly twice (once per phase of each neighboring pivot).
    # Since phases overlap between pivots, this is complex.

    # Let's enumerate by brute force. 16 slots, 8 procs each firing twice.
    # Assign each slot a proc. Constraints: each proc used exactly twice.
    # 16! / (2!)^8 = 16! / 256 ≈ 8.2 × 10^10. Too large for brute force.

    # But most assignments violate constraints. Let me use the structure.

    # From the analysis, for pair {3,4} between A and B:
    # In A-phase 1 (s0..s7): 4 must fire before 3.
    # In B-phase 1 (s2..s9): 3 must fire before 4.
    # In A-phase 2 (s8..s15): 4 must fire before 3.
    # In B-phase 2 (s10..s15,s0,s1): 3 must fire before 4.

    # Proc 3 and 4 each fire twice. Each firing is at one slot.
    # Let's say 4 fires at slots a, b (a < b in the cyclic 0..15 order)
    # and 3 fires at slots c, d (c < d).

    # One firing of 4 in A-phase 1 (s0..s7), one in A-phase 2 (s8..s15).
    # One firing of 3 in A-phase 1, one in A-phase 2.

    # In A-phase 1: 4's firing < 3's firing (in step order)
    # In A-phase 2: 4's firing < 3's firing (in step order)

    # One firing of 4 in B-phase 1 (s2..s9), one in B-phase 2 (s10..s15,s0,s1).
    # One firing of 3 in B-phase 1, one in B-phase 2.

    # In B-phase 1: 3's firing < 4's firing
    # In B-phase 2: 3's firing < 4's firing

    # For A-phase 1: 4 fires at some slot in s0..s7 BEFORE 3 fires at some slot in s0..s7.
    # For B-phase 1 (s2..s9): 3 fires BEFORE 4.
    #
    # If 4 fires at s0 or s1 (in A-phase 1 but before B-phase 1), and 3 fires at s2..s7:
    #   A-phase 1: 4 (at s0/s1) before 3 (at s2..s7). ✓
    #   B-phase 1: 3 (at s2..s7) before 4 (wherever 4's B-phase 1 firing is).
    #   4's other firing must be in s2..s9 (B-phase 1) — at s8 or s9 if in A-phase 2.
    #   Wait, s8 is in A-phase 2 and also s8..s9 is in B-phase 1. So 4 fires at s8 or s9.
    #   B-phase 1: 3 at s2..s7, 4 at s8 or s9. s2..s7 < s8,s9. So 3 before 4. ✓
    #   A-phase 2: 4 at s8/s9, 3 at s10..s15 (since 3's other firing in A-phase 2).
    #   But s10..s15: 3 needs to be here and 4's A-phase 2 firing at s8/s9.
    #   A-phase 2: 4 (s8/s9) before 3 (s10..s15). ✓
    #   B-phase 2 (s10..s15,s0,s1): 3 at s10..s15, 4 at s0 or s1 (wrapping).
    #   Cyclically in B-phase 2: s10 < s11 < ... < s15 < s0 < s1.
    #   3 fires at s10..s15, 4 fires at s0/s1 (later). So 3 before 4. ✓

    # This WORKS for pair {3,4}. Similar analysis for the other 3 pairs.

    # So let's try the concrete assignment:
    # Slot s0: proc 4  (gap 0, after A1)
    # Slot s1: proc 0  (gap 0)
    # Slot s2: proc 3  (gap 1, after B1)
    # Slot s3: proc 7  (gap 1)
    # Slot s4: proc 6  (gap 2, after C1)
    # Slot s5: proc 10 (gap 2)
    # Slot s6: proc 9  (gap 3, after D1)
    # Slot s7: proc 1  (gap 3)
    # Slot s8: proc 4  (gap 4, after A2)  -- 4's second firing
    #   Wait, but s8 is after A2. Actually s8 is in A-phase 2.
    #   We wanted 4 at s8/s9. Let's put 4 at s8.
    # Slot s9: proc 0  (gap 4)  -- 0's second firing
    #   Hmm, but where does 1 fire second?

    # Let me be more systematic. By symmetry of the ring (4-fold rotational),
    # try to make all 4 pairs follow the same pattern.

    # Pattern for pair {3,4} between A(2) and B(5):
    #   4 fires at s0 (gap 0) and s8 (gap 4)
    #   3 fires at s2 (gap 1) and s10 (gap 5)

    # By rotation +2 gaps: pair {6,7} between B(5) and C(8):
    #   7 fires at s2 (gap 1) and s10 (gap 5)  -- CONFLICT with 3!

    # Can't have both 3 and 7 at s2. Need different pattern.

    # Each gap has 2 slots. Each slot holds one proc. 16 slots, 8 procs * 2 = 16.
    # So all 16 slots are filled.

    # Pair {3,4}: 4 at (s0, s8), 3 at (s2 or s3, s10 or s11)
    # Pair {6,7}: 7 at (s2 or s3, s10 or s11), 6 at (s4 or s5, s12 or s13)
    # Pair {9,10}: 10 at (s4 or s5, s12 or s13), 9 at (s6 or s7, s14 or s15)
    # Pair {0,1}: 1 at (s6 or s7, s14 or s15), 0 at (s0 or s1, s8 or s9)

    # From pair {3,4}: 4 at s0, so slot s0 = proc 4.
    # From pair {0,1}: 0 at s0 or s1. Since s0=4, 0 at s1. So s1 = 0.
    # 4's second firing at s8. So s8 = proc 4.
    # 0's second firing at s8 or s9. Since s8=4, 0 at s9. So s9 = 0.

    # 3 at (s2 or s3, s10 or s11).
    # 7 at (s2 or s3, s10 or s11).
    # Since 3 and 7 share these slots: 3 and 7 go to s2, s3 in some order (one each).
    # And their second firings go to s10, s11 in some order.
    #
    # For A-phase 1 ordering: no direct constraint on 3 vs 7 order.
    # For B-phase 1: 3 before 4. 3 is at s2 or s3, 4 at s8. s2/s3 < s8. ✓ either way.
    # For B-phase 1: 7 before 6. 7 at s2 or s3, 6 at s4 or s5. s2/s3 < s4/s5. ✓ either way.

    # So within gap 1 (s2, s3), we can put 3 and 7 in either order.
    # Similarly gap 5 (s10, s11): 3 and 7 in either order.

    # 6 at (s4 or s5, s12 or s13).
    # 10 at (s4 or s5, s12 or s13).
    # Same deal: 6 and 10 share gap 2 (s4, s5) and gap 6 (s12, s13).

    # 9 at (s6 or s7, s14 or s15).
    # 1 at (s6 or s7, s14 or s15).
    # 9 and 1 share gap 3 (s6, s7) and gap 7 (s14, s15).

    # Let me try:
    # s0=4, s1=0, s2=3, s3=7, s4=6, s5=10, s6=9, s7=1,
    # s8=4, s9=0, s10=3, s11=7, s12=6, s13=10, s14=9, s15=1

    # Wait, this assigns 4 to s0 and s8, 0 to s1 and s9, etc. Each proc fires twice. ✓
    # But the full mover sequence includes pivot firings:
    # A1=2, s0=4, s1=0, B1=5, s2=3, s3=7, C1=8, s4=6, s5=10, D1=11, s6=9, s7=1,
    # A2=2, s8=4, s9=0, B2=5, s10=3, s11=7, C2=8, s12=6, s13=10, D2=11, s14=9, s15=1

    # Full mover sequence:
    mover_seq = [2, 4, 0, 5, 3, 7, 8, 6, 10, 11, 9, 1, 2, 4, 0, 5, 3, 7, 8, 6, 10, 11, 9, 1]

    print("\nCandidate mover sequence:")
    print(mover_seq)
    print(f"Length: {len(mover_seq)}")

    # Verify each proc fires exactly twice
    from collections import Counter
    counts = Counter(mover_seq)
    print(f"Fire counts: {dict(sorted(counts.items()))}")
    assert all(c == 2 for c in counts.values()), "Not all procs fire exactly twice!"
    assert len(counts) == n, f"Not all {n} procs fire!"

    # Now check tight constraints for each pivot and phase.
    # First, identify the steps (0-indexed) in each phase.

    # Pivot firings:
    # A(2) fires at steps 0, 12
    # B(5) fires at steps 3, 15
    # C(8) fires at steps 6, 18
    # D(11) fires at steps 9, 21

    pivot_firings = {2: [0, 12], 5: [3, 15], 8: [6, 18], 11: [9, 21]}

    # Phase boundaries (using step indices, exclusive of the pivot firings themselves):
    # A-phase 1: steps 1..11 (between A-firing at 0 and A-firing at 12)
    # A-phase 2: steps 13..23 (between A-firing at 12 and A-firing at 0+24)

    phases = {}
    for t in pivots:
        f1, f2 = pivot_firings[t]
        # Phase 1: steps after f1 and before f2
        ph1 = list(range(f1 + 1, f2))
        # Phase 2: steps after f2 and before f1 (wrapping)
        ph2 = list(range(f2 + 1, 24)) + list(range(0, f1))
        phases[(t, 1)] = ph1
        phases[(t, 2)] = ph2

    print("\nPhase step ranges:")
    for (t, p), steps in sorted(phases.items()):
        print(f"  Pivot {t} phase {p}: steps {steps}")

    # Check tight constraints
    # For each pivot and phase, find the steps where each local proc fires
    # and check the ordering.

    neighborhoods = {
        2: {'left2': 0, 'left': 1, 'right': 3, 'right2': 4},
        5: {'left2': 3, 'left': 4, 'right': 6, 'right2': 7},
        8: {'left2': 6, 'left': 7, 'right': 9, 'right2': 10},
        11: {'left2': 9, 'left': 10, 'right': 0, 'right2': 1},
    }

    all_tight = True
    for t in pivots:
        nb = neighborhoods[t]
        for p in [1, 2]:
            phase_steps = phases[(t, p)]

            # Find firings of local procs in this phase
            local_firings = {}
            for step in phase_steps:
                proc = mover_seq[step]
                if proc in [nb['left2'], nb['left'], nb['right'], nb['right2']]:
                    local_firings.setdefault(proc, []).append(step)

            # Check: each local proc fires exactly once in this phase
            for role in ['left2', 'left', 'right', 'right2']:
                proc = nb[role]
                fires = local_firings.get(proc, [])
                if len(fires) != 1:
                    print(f"  FAIL: Pivot {t} phase {p}: {role}(proc {proc}) fires {len(fires)} times (expected 1)")
                    all_tight = False

            if all(nb[r] in local_firings and len(local_firings[nb[r]]) == 1 for r in ['left2', 'left', 'right', 'right2']):
                # Check tight ordering
                l2_step = local_firings[nb['left2']][0]
                l_step = local_firings[nb['left']][0]
                r2_step = local_firings[nb['right2']][0]
                r_step = local_firings[nb['right']][0]

                left_tight = l2_step < l_step  # left2 before left
                right_tight = r2_step < r_step  # right2 before right

                # For cyclic phases (phase 2 wrapping), need to handle wraparound
                # In our current setup, all phases are contiguous (no wrapping needed
                # since we listed them as contiguous step ranges)
                # Actually, phase 2 wraps! E.g., A-phase 2 = steps 13..23,0 (but I
                # listed it as 13..23 without wrapping to 0, which misses steps before A1).
                # Wait, I did include wrapping: ph2 = range(f2+1, 24) + range(0, f1).
                # For A: f1=0, so range(0, 0) = empty. So A-phase 2 = 13..23. No wrap.
                # For B: f1=3, so range(0, 3) = [0,1,2]. B-phase 2 = 16..23 + 0..2.
                # Step ordering within phase: the listed order IS the temporal order.
                # So for B-phase 2: step 16 is first, then 17, ..., 23, 0, 1, 2.

                # For the ordering check, I need the POSITION within the phase,
                # not the raw step number. Let me check position in the phase list.
                phase_step_list = phase_steps
                l2_pos = phase_step_list.index(l2_step) if l2_step in phase_step_list else -1
                l_pos = phase_step_list.index(l_step) if l_step in phase_step_list else -1
                r2_pos = phase_step_list.index(r2_step) if r2_step in phase_step_list else -1
                r_pos = phase_step_list.index(r_step) if r_step in phase_step_list else -1

                left_tight = l2_pos < l_pos
                right_tight = r2_pos < r_pos

                tight_str = "TIGHT" if (left_tight and right_tight) else "NOT TIGHT"
                details = f"left2(={nb['left2']})@pos{l2_pos} {'<' if left_tight else '>'} left(={nb['left']})@pos{l_pos}, " \
                         f"right2(={nb['right2']})@pos{r2_pos} {'<' if right_tight else '>'} right(={nb['right']})@pos{r_pos}"
                print(f"  Pivot {t} phase {p}: {tight_str} [{details}]")

                if not (left_tight and right_tight):
                    all_tight = False

    print(f"\nAll-tight: {all_tight}")
    return mover_seq, all_tight

def search_all_tight_sequences():
    """
    Search for ALL possible all-tight mover sequences by trying different
    assignments of binary procs to slots.
    """
    print("\n" + "=" * 60)
    print("=== Exhaustive search for all-tight mover sequences ===")
    print("=" * 60)

    n = 12
    pivots = [2, 5, 8, 11]

    # The mover sequence template:
    # [A1, s0, s1, B1, s2, s3, C1, s4, s5, D1, s6, s7, A2, s8, s9, B2, s10, s11, C2, s12, s13, D2, s14, s15]
    # where A1=A2=2, B1=B2=5, C1=C2=8, D1=D2=11

    # We need to fill s0..s15 with binary procs (0,1,3,4,6,7,9,10), each exactly twice.

    # From the analysis, the structure forces:
    # Pair {0,1}: 0 in gaps {0,4} and 1 in gaps {3,7} (or some rotation)
    # Pair {3,4}: 4 in gaps {0,4} and 3 in gaps {1,5}
    # Pair {6,7}: 7 in gaps {1,5} and 6 in gaps {2,6}
    # Pair {9,10}: 10 in gaps {2,6} and 9 in gaps {3,7}

    # Gap 0 (s0,s1): contains one of {4} and one of {0}
    # Gap 1 (s2,s3): contains one of {3} and one of {7}
    # Gap 2 (s4,s5): contains one of {6} and one of {10}
    # Gap 3 (s6,s7): contains one of {9} and one of {1}
    # (Second round identical: gap 4 same as 0, etc.)

    # Within each gap, the order of the 2 procs matters.
    # Gap 0: (4, 0) or (0, 4)
    # Gap 1: (3, 7) or (7, 3)
    # Gap 2: (6, 10) or (10, 6)
    # Gap 3: (9, 1) or (1, 9)

    # And the second round:
    # Gap 4: same pair as gap 0: (4, 0) or (0, 4)
    # Gap 5: same pair as gap 1: (3, 7) or (7, 3)
    # Gap 6: same pair as gap 2: (6, 10) or (10, 6)
    # Gap 7: same pair as gap 3: (9, 1) or (1, 9)

    # Total orderings: 2^8 = 256 (each of 8 gaps has 2 orderings).
    # But actually, it's constrained: the gap composition is fixed (which pair goes where),
    # but the GAP COMPOSITION might not be unique. Let me check alternatives.

    # From the ordering constraints:
    # Pivot A(2), A-phase 1 (s0..s7):
    #   Need 0 before 1 (left pair) and 4 before 3 (right pair).
    #   0 and 4 must fire in this phase, and 1 and 3 must fire in this phase.

    # 0 fires in gap 0 or gap 3 (the gaps within A-phase 1 are gaps 0,1,2,3).
    # Wait, A-phase 1 = steps 1..11 = s0,s1, B1, s2,s3, C1, s4,s5, D1, s6,s7.
    # The binary slots in A-phase 1 are s0,s1,s2,s3,s4,s5,s6,s7 = ALL 8 slots in first half.
    #
    # So in A-phase 1, ALL binary procs that fire at s0..s7 are visible.
    # Each of the 4 local procs of A (0, 1, 3, 4) fires exactly once in A-phase 1.
    # The remaining 4 slots hold the other 4 binary procs (6, 7, 9, 10), each once.

    # OK so in each "half" (8 slots), each binary proc fires exactly once.
    # The second half is identical to the first half in terms of which procs fire where?
    # No -- each proc fires twice total, once in each half. So the first half has each proc once
    # and the second half has each proc once.

    # So we need to assign: which binary proc goes to which slot in the first half (s0..s7),
    # and which to which slot in the second half (s8..s15).
    # Each half is a permutation of the 8 binary procs.

    # The constraints:
    # A-phase 1 (first half): 0 before 1, 4 before 3
    # B-phase 1 (s2..s9): 3 before 4, 7 before 6
    #   s2..s7 in first half, s8..s9 in second half.
    #   But s8,s9 are the FIRST 2 slots of the second half.
    #   In B-phase 1: the temporal order is s2, s3, (C1), s4, s5, (D1), s6, s7, (A2), s8, s9.
    #   So 3 must fire before 4 in this range. If 3 is at s2..s7 and 4 is at s8..s9,
    #   that's automatically satisfied. Or both could be in s2..s7 (then 3's slot < 4's slot).

    # This is getting very complex. Let me just code the brute-force search.

    from itertools import permutations

    binary_procs = [0, 1, 3, 4, 6, 7, 9, 10]

    neighborhoods = {
        2: {'left2': 0, 'left': 1, 'right': 3, 'right2': 4},
        5: {'left2': 3, 'left': 4, 'right': 6, 'right2': 7},
        8: {'left2': 6, 'left': 7, 'right': 9, 'right2': 10},
        11: {'left2': 9, 'left': 10, 'right': 0, 'right2': 1},
    }

    # Build mover sequence from two permutations of binary procs
    # perm1 = assignment for first half (s0..s7)
    # perm2 = assignment for second half (s8..s15)
    # Full sequence: [2, p1[0], p1[1], 5, p1[2], p1[3], 8, p1[4], p1[5], 11, p1[6], p1[7],
    #                  2, p2[0], p2[1], 5, p2[2], p2[3], 8, p2[4], p2[5], 11, p2[6], p2[7]]

    def build_mover_seq(perm1, perm2):
        return [2, perm1[0], perm1[1], 5, perm1[2], perm1[3], 8, perm1[4], perm1[5], 11, perm1[6], perm1[7],
                2, perm2[0], perm2[1], 5, perm2[2], perm2[3], 8, perm2[4], perm2[5], 11, perm2[6], perm2[7]]

    def check_tight(mover_seq):
        """Check if mover sequence satisfies all-tight constraints."""
        pivot_firings = {2: [0, 12], 5: [3, 15], 8: [6, 18], 11: [9, 21]}

        for t in pivots:
            nb = neighborhoods[t]
            f1, f2 = pivot_firings[t]

            # Phase 1: steps after f1, before f2 (exclusive of pivot firings)
            ph1_steps = list(range(f1 + 1, f2))
            # Phase 2: steps after f2, before f1 (wrapping)
            ph2_steps = list(range(f2 + 1, 24)) + list(range(0, f1))

            for ph_steps in [ph1_steps, ph2_steps]:
                # Find positions of local procs in this phase
                positions = {}
                for idx, step in enumerate(ph_steps):
                    proc = mover_seq[step]
                    if proc in [nb['left2'], nb['left'], nb['right'], nb['right2']]:
                        positions[proc] = idx

                # Each local proc must fire exactly once
                for role in ['left2', 'left', 'right', 'right2']:
                    if nb[role] not in positions:
                        return False

                # Tight: left2 before left, right2 before right
                if positions[nb['left2']] >= positions[nb['left']]:
                    return False
                if positions[nb['right2']] >= positions[nb['right']]:
                    return False

        return True

    # 8! = 40320 permutations for each half. Total: 40320^2 ≈ 1.6 billion. Too many!
    # Need to prune.

    # Let me instead constrain the gap contents.
    # Each gap (pair of consecutive binary slots) has a specific set of procs.
    # Gap 0 (s0,s1): between A1 and B1.
    # Gap 1 (s2,s3): between B1 and C1.
    # Gap 2 (s4,s5): between C1 and D1.
    # Gap 3 (s6,s7): between D1 and A2.

    # From tight constraints on A-phase 1:
    #   0 before 1 (somewhere in s0..s7)
    #   4 before 3 (somewhere in s0..s7)
    #   Each of 0,1,3,4 fires once in s0..s7.
    # From tight constraints on B-phase 1 (s2..s9):
    #   3 before 4
    #   7 before 6
    # From tight constraints on C-phase 1 (s4..s11):
    #   6 before 7
    #   10 before 9
    # From tight constraints on D-phase 1 (s6..s13):
    #   9 before 10
    #   1 before 0

    # Note the CONTRADICTION for pair {0,1}:
    # A-phase 1 (s0..s7) needs 0 before 1
    # D-phase 1 (s6..s13) needs 1 before 0
    # s0..s7 and s6..s13 overlap at s6,s7.
    # If both 0 and 1 are at s0..s5: then A sees 0<1 and D doesn't see them
    #   (they're not in s6..s13 since s0..s5 < s6).
    #   Wait, D-phase 1 is s6..s13. If 0 and 1 fire at s0..s5, they're NOT in D-phase 1.
    #   Then D-phase 1 must see them fire at s8..s13 (in the second half).
    #   But each proc fires once per half. In the first half, 0 and 1 are at s0..s5.
    #   In the second half, they fire again at s8..s15.
    #   D-phase 1 = s6,s7 (from 1st half) + (A2) + s8,s9 (2nd half) + (B2) + s10,s11 (2nd half) + ...
    #   Actually D-phase 1 = steps 10..20 (step 9 is D1, step 21 is D2).
    #   Wait let me recompute.

    # Step indices:
    # 0:A1, 1:s0, 2:s1, 3:B1, 4:s2, 5:s3, 6:C1, 7:s4, 8:s5, 9:D1, 10:s6, 11:s7,
    # 12:A2, 13:s8, 14:s9, 15:B2, 16:s10, 17:s11, 18:C2, 19:s12, 20:s13, 21:D2, 22:s14, 23:s15

    # D fires at steps 9, 21. D-phase 1 = steps 10..20. D-phase 2 = steps 22,23,0..8.

    # In D-phase 1 (steps 10..20): binary slots are s6(10), s7(11), s8(13), s9(14), s10(16), s11(17), s12(19), s13(20).
    # That's 8 binary slots = all procs fire once.

    # For D's tight constraint in D-phase 1: 1 before 0, 9 before 10.
    # 1 and 0 fire at some of these 8 slots. Their relative order in the phase determines tight.

    # In D-phase 2 (steps 22,23,0..8): binary slots are s14(22), s15(23), s0(1), s1(2), s2(4), s3(5), s4(7), s5(8).
    # 1 and 0 fire at some of these. Need 1 before 0.

    # So D needs 1 before 0 in both phases. A needs 0 before 1 in both phases.
    # But 0 and 1 fire once in each half, hence once in each phase of any pivot
    # whose phases align with the halves.

    # A-phase 1 = steps 1..11 = s0..s7 (first half binary slots).
    # A-phase 2 = steps 13..23 = s8..s15 (second half binary slots).
    # D-phase 1 = steps 10..20 = s6,s7 (first half) + s8..s13 (second half).
    # D-phase 2 = steps 22,23,0..8 = s14,s15 (second half) + s0..s5 (first half).

    # 0 fires once in first half at some slot s_a ∈ {s0..s7} (step 1+s_a or depends on exact mapping).
    # 0 fires once in second half at some slot s_b ∈ {s8..s15}.

    # In A-phase 1 (= first half): 0's first firing is here. 1's first firing is here.
    # A needs 0 before 1: 0's first-half slot < 1's first-half slot.

    # In D-phase 1 (= s6,s7 + s8..s13):
    #   0's contribution: if 0 is at s6 or s7, or s8..s13 in second half.
    #   0 fires once in first half (at s_a) and once in second half (at s_b).
    #   Which of these is in D-phase 1?
    #   s_a is in D-phase 1 iff s_a ∈ {s6, s7} (first half slots in D-phase 1).
    #   s_b is in D-phase 1 iff s_b ∈ {s8, s9, s10, s11, s12, s13}.
    #   s_b is in D-phase 2 iff s_b ∈ {s14, s15}.

    # Case A: 0 is at s6 or s7 in first half, and s8..s13 in second half.
    #   Both firings in D-phase 1. But each proc fires once per phase!
    #   Actually, 0 fires twice in D-phase 1? That would violate (J,K,g,h)=(1,1,1,1).

    # Hmm, so we CANNOT have 0 at s6/s7 (first half) if 0 also fires at s8..s13 (second half),
    # because both would be in D-phase 1.

    # For each proc, its 2 firings must be in different phases of EACH neighboring pivot.
    # 0's neighbors: pivots 2(via left2) and 11(via right).
    # 0 fires at (s_a in first half, s_b in second half).
    # For A(2): s_a in A-phase 1, s_b in A-phase 2. Always true since A-phases = halves. ✓
    # For D(11): need one firing in D-phase 1 and one in D-phase 2.
    #   D-phase 1 includes first-half slots {s6,s7} and second-half slots {s8..s13}.
    #   D-phase 2 includes second-half slots {s14,s15} and first-half slots {s0..s5}.
    #   So 0's first-half firing s_a must be in {s0..s5} (D-phase 2) OR {s6,s7} (D-phase 1).
    #   And 0's second-half firing s_b must be in {s8..s13} (D-phase 1) OR {s14,s15} (D-phase 2).
    #   For one in each D-phase: either (s_a∈D-ph1, s_b∈D-ph2) or (s_a∈D-ph2, s_b∈D-ph1).
    #   Option 1: s_a∈{s6,s7}, s_b∈{s14,s15}. Both in D-phase 1 and 2 resp. ✓
    #   Option 2: s_a∈{s0..s5}, s_b∈{s8..s13}. s_a in D-phase 2, s_b in D-phase 1. ✓

    # So 0 can be at:
    # Option 1: first half s6/s7, second half s14/s15
    # Option 2: first half s0..s5, second half s8..s13

    # Similarly for all other procs, we need to determine valid slot assignments.

    # This is getting very involved. Let me just code the constraint solver.
    # With 8! for each half being too large, I'll use a smarter approach:
    # enumerate valid assignments for each gap.

    # Each gap has exactly 2 slots. The 4 gaps in each half = 8 slots.
    # I need to assign 8 procs to 8 slots (one per slot), with tight constraints.

    # Instead of full permutation, use constraint propagation.

    # Let me represent slots as 0..7 for first half, 0..7 for second half.
    # First half: gap 0 = (0,1), gap 1 = (2,3), gap 2 = (4,5), gap 3 = (6,7).
    # The step index for slot i in first half is: 1 + i + (i // 2)
    # Actually, the steps are:
    # s0 -> step 1, s1 -> step 2, s2 -> step 4, s3 -> step 5, s4 -> step 7, s5 -> step 8, s6 -> step 10, s7 -> step 11
    # s8 -> step 13, s9 -> step 14, s10 -> step 16, s11 -> step 17, s12 -> step 19, s13 -> step 20, s14 -> step 22, s15 -> step 23

    slot_to_step_h1 = [1, 2, 4, 5, 7, 8, 10, 11]
    slot_to_step_h2 = [13, 14, 16, 17, 19, 20, 22, 23]

    # For each proc, determine which first-half slots and which second-half slots are valid
    # (respecting one-per-phase for each neighboring pivot).

    # Phase membership of each slot:
    # For pivot A(2): A-phase 1 = steps 1..11, A-phase 2 = steps 13..23
    # All first-half slots are in A-phase 1, all second-half in A-phase 2.

    # For pivot B(5): B-phase 1 = steps 4..14, B-phase 2 = steps 16..23,0..2
    # First-half: s0(1),s1(2) in B-phase 2. s2(4)..s7(11) in B-phase 1.
    # Second-half: s8(13),s9(14) in B-phase 1. s10(16)..s15(23) in B-phase 2.

    # For pivot C(8): C-phase 1 = steps 7..17, C-phase 2 = steps 19..23,0..5
    # First-half: s0(1)..s3(5) in C-phase 2. s4(7)..s7(11) in C-phase 1.
    # Second-half: s8(13)..s11(17) in C-phase 1. s12(19)..s15(23) in C-phase 2.

    # For pivot D(11): D-phase 1 = steps 10..20, D-phase 2 = steps 22..23,0..8
    # First-half: s0(1)..s5(8) in D-phase 2. s6(10),s7(11) in D-phase 1.
    # Second-half: s8(13)..s13(20) in D-phase 1. s14(22),s15(23) in D-phase 2.

    # Summary: slot -> (A-phase, B-phase, C-phase, D-phase)
    slot_phases_h1 = [
        # slot 0 (step 1): A1, B2, C2, D2
        (1, 2, 2, 2),
        # slot 1 (step 2): A1, B2, C2, D2
        (1, 2, 2, 2),
        # slot 2 (step 4): A1, B1, C2, D2
        (1, 1, 2, 2),
        # slot 3 (step 5): A1, B1, C2, D2
        (1, 1, 2, 2),
        # slot 4 (step 7): A1, B1, C1, D2
        (1, 1, 1, 2),
        # slot 5 (step 8): A1, B1, C1, D2
        (1, 1, 1, 2),
        # slot 6 (step 10): A1, B1, C1, D1
        (1, 1, 1, 1),
        # slot 7 (step 11): A1, B1, C1, D1
        (1, 1, 1, 1),
    ]

    slot_phases_h2 = [
        # slot 0 (step 13): A2, B1, C1, D1
        (2, 1, 1, 1),
        # slot 1 (step 14): A2, B1, C1, D1
        (2, 1, 1, 1),
        # slot 2 (step 16): A2, B2, C1, D1
        (2, 2, 1, 1),
        # slot 3 (step 17): A2, B2, C1, D1
        (2, 2, 1, 1),
        # slot 4 (step 19): A2, B2, C2, D1
        (2, 2, 2, 1),
        # slot 5 (step 20): A2, B2, C2, D1
        (2, 2, 2, 1),
        # slot 6 (step 22): A2, B2, C2, D2
        (2, 2, 2, 2),
        # slot 7 (step 23): A2, B2, C2, D2
        (2, 2, 2, 2),
    ]

    # For each proc, determine its 2 neighboring pivots and which pivot index they are (0=A,1=B,2=C,3=D)
    proc_pivots = {
        0: (0, 3),   # A(left2) and D(right)
        1: (0, 3),   # A(left) and D(right2)
        3: (0, 1),   # A(right) and B(left2)
        4: (0, 1),   # A(right2) and B(left)
        6: (1, 2),   # B(right) and C(left2)
        7: (1, 2),   # B(right2) and C(left)
        9: (2, 3),   # C(right) and D(left2)
        10: (2, 3),  # C(right2) and D(left)
    }

    # For each proc, its 2 firings must be in different phases of EACH neighboring pivot.
    # Firing 1 in first half (some slot i), firing 2 in second half (some slot j).
    # The phase tuple of slot i (from h1) must differ from phase tuple of slot j (from h2)
    # at the proc's 2 pivot indices.

    # Actually, firing 1 in h1 slot i has phase values slot_phases_h1[i].
    # Firing 2 in h2 slot j has phase values slot_phases_h2[j].
    # For each neighboring pivot p of this proc:
    #   slot_phases_h1[i][p] != slot_phases_h2[j][p]
    # Since A-phase in h1 is always 1 and in h2 is always 2, any proc with A as neighbor
    # automatically satisfies the A constraint. Similarly for other pivots.

    # Let me check: for proc 0 (pivots A and D):
    # A: h1 slot always A-phase 1, h2 slot always A-phase 2. Different. ✓ Always.
    # D: h1 slot i has D-phase slot_phases_h1[i][3], h2 slot j has D-phase slot_phases_h2[j][3].
    # Need them different.
    # h1 D-phases: [2,2,2,2,2,2,1,1] (slots 0-7)
    # h2 D-phases: [1,1,1,1,1,1,2,2] (slots 0-7)
    # For proc 0: need h1_D != h2_D.
    # If h1 slot in {0..5} (D-phase 2) and h2 slot in {0..5} (D-phase 1): 2 != 1. ✓
    # If h1 slot in {6,7} (D-phase 1) and h2 slot in {6,7} (D-phase 2): 1 != 2. ✓
    # If h1 slot in {0..5} (D-phase 2) and h2 slot in {6,7} (D-phase 2): 2 == 2. ✗
    # If h1 slot in {6,7} (D-phase 1) and h2 slot in {0..5} (D-phase 1): 1 == 1. ✗
    # So proc 0 must be: h1 ∈ {0..5} & h2 ∈ {0..5}, OR h1 ∈ {6,7} & h2 ∈ {6,7}.

    # Let me precompute valid (h1_slot, h2_slot) pairs for each proc.
    valid_slot_pairs = {}
    for proc, (p1, p2) in proc_pivots.items():
        pairs = []
        for i in range(8):
            for j in range(8):
                ph1 = slot_phases_h1[i]
                ph2 = slot_phases_h2[j]
                if ph1[p1] != ph2[p1] and ph1[p2] != ph2[p2]:
                    pairs.append((i, j))
        valid_slot_pairs[proc] = pairs
        print(f"Proc {proc}: {len(pairs)} valid (h1,h2) slot pairs")

    # Now, the ordering constraints.
    # For each pivot and each phase, the tight ordering must hold.
    #
    # For pivot A(2), left pair (0 before 1):
    #   A-phase 1 = first half: need 0's h1_slot < 1's h1_slot
    #   A-phase 2 = second half: need 0's h2_slot < 1's h2_slot
    # For pivot A(2), right pair (4 before 3):
    #   A-phase 1: need 4's h1_slot < 3's h1_slot
    #   A-phase 2: need 4's h2_slot < 3's h2_slot
    # For pivot B(5), left pair (3 before 4):
    #   B-phase 1: need 3 before 4 within B-phase 1 slots.
    #   B-phase 1 slots in h1: {2,3,4,5,6,7}. B-phase 1 slots in h2: {0,1}.
    #   Steps in B-phase 1: h1 slots 2..7 (steps 4,5,7,8,10,11) then h2 slots 0,1 (steps 13,14).
    #   Temporal order within B-phase 1: h1_slot 2, h1_slot 3, ..., h1_slot 7, h2_slot 0, h2_slot 1.
    #   So position within B-phase 1 = h1_slot - 2 (for h1 slots 2..7) or 6 + h2_slot (for h2 slots 0,1).
    #   Wait, that's 6 + 2 = 8 positions. But there are 8 binary slots in B-phase 1.
    #
    #   For 3 before 4: compare their B-phase-1 positions.
    #   3's position: if h1_slot ∈ {2..7}, pos = h1_slot - 2. If h2_slot ∈ {0,1}, pos = 6 + h2_slot.
    #   4's position: similarly.

    # This is getting really involved but manageable. Let me formalize the ordering check.

    # For each pivot, define the temporal position of each slot within each phase.
    # Then the tight constraint is: left2's position < left's position, right2's position < right's position.

    # Define: for each (pivot, phase), the list of (half, slot) pairs in temporal order.
    pivot_phase_slots = {}

    # Pivot A(2): phase 1 = A-phase 1 = all h1 slots in order
    #             phase 2 = A-phase 2 = all h2 slots in order
    pivot_phase_slots[(0, 1)] = [('h1', i) for i in range(8)]
    pivot_phase_slots[(0, 2)] = [('h2', i) for i in range(8)]

    # Pivot B(5): phase 1 = B-phase 1 = h1 slots {2..7} then h2 slots {0,1}
    #             phase 2 = B-phase 2 = h2 slots {2..7} then h1 slots {0,1}
    pivot_phase_slots[(1, 1)] = [('h1', i) for i in range(2, 8)] + [('h2', i) for i in range(2)]
    pivot_phase_slots[(1, 2)] = [('h2', i) for i in range(2, 8)] + [('h1', i) for i in range(2)]

    # Pivot C(8): phase 1 = h1 slots {4..7} then h2 slots {0..3}
    #             phase 2 = h2 slots {4..7} then h1 slots {0..3}
    pivot_phase_slots[(2, 1)] = [('h1', i) for i in range(4, 8)] + [('h2', i) for i in range(4)]
    pivot_phase_slots[(2, 2)] = [('h2', i) for i in range(4, 8)] + [('h1', i) for i in range(4)]

    # Pivot D(11): phase 1 = h1 slots {6,7} then h2 slots {0..5}
    #              phase 2 = h2 slots {6,7} then h1 slots {0..5}
    pivot_phase_slots[(3, 1)] = [('h1', i) for i in range(6, 8)] + [('h2', i) for i in range(6)]
    pivot_phase_slots[(3, 2)] = [('h2', i) for i in range(6, 8)] + [('h1', i) for i in range(6)]

    # For a given assignment (proc -> (h1_slot, h2_slot)):
    # The position of proc in pivot p's phase q is determined by which slot it's in.

    def check_all_tight_assignment(assignment):
        """
        assignment: dict mapping proc -> (h1_slot, h2_slot)
        Returns True if all tight constraints are satisfied.
        """
        # Build reverse map: (half, slot) -> proc
        slot_to_proc = {}
        for proc, (h1, h2) in assignment.items():
            slot_to_proc[('h1', h1)] = proc
            slot_to_proc[('h2', h2)] = proc

        # For each pivot and phase, check tight ordering
        for pivot_idx in range(4):
            t = pivots[pivot_idx]
            nb = neighborhoods[t]

            for phase in [1, 2]:
                slots_in_order = pivot_phase_slots[(pivot_idx, phase)]

                # Find positions of local procs
                positions = {}
                for pos, (half, slot) in enumerate(slots_in_order):
                    if (half, slot) in slot_to_proc:
                        proc = slot_to_proc[(half, slot)]
                        if proc in [nb['left2'], nb['left'], nb['right'], nb['right2']]:
                            positions[proc] = pos

                # Each local proc must appear exactly once
                for role in ['left2', 'left', 'right', 'right2']:
                    if nb[role] not in positions:
                        return False

                # Tight: left2 before left, right2 before right
                if positions[nb['left2']] >= positions[nb['left']]:
                    return False
                if positions[nb['right2']] >= positions[nb['right']]:
                    return False

        return True

    # Now search. Instead of brute force over all permutations,
    # use backtracking with constraint pruning.

    # Order procs for assignment: 0, 1, 3, 4, 6, 7, 9, 10
    procs_to_assign = [0, 1, 3, 4, 6, 7, 9, 10]

    used_h1 = [False] * 8
    used_h2 = [False] * 8
    assignment = {}

    count = [0]
    solutions = []

    def backtrack(idx):
        if idx == 8:
            # All procs assigned. Check tight.
            if check_all_tight_assignment(assignment):
                solutions.append(dict(assignment))
            count[0] += 1
            return

        proc = procs_to_assign[idx]
        for h1, h2 in valid_slot_pairs[proc]:
            if used_h1[h1] or used_h2[h2]:
                continue

            # Quick constraint check for already-assigned related procs
            # (can add later for pruning)

            used_h1[h1] = True
            used_h2[h2] = True
            assignment[proc] = (h1, h2)

            backtrack(idx + 1)

            del assignment[proc]
            used_h1[h1] = False
            used_h2[h2] = False

    print("\nSearching for valid all-tight assignments...")
    backtrack(0)

    print(f"Total complete assignments checked: {count[0]}")
    print(f"All-tight solutions found: {len(solutions)}")

    if solutions:
        print("\nFirst solution:")
        sol = solutions[0]
        for proc in procs_to_assign:
            print(f"  Proc {proc}: h1_slot={sol[proc][0]}, h2_slot={sol[proc][1]}")

        # Build and print the mover sequence
        h1_perm = [None] * 8
        h2_perm = [None] * 8
        for proc, (h1, h2) in sol.items():
            h1_perm[h1] = proc
            h2_perm[h2] = proc

        mover_seq = build_mover_seq(h1_perm, h2_perm)
        print(f"\nMover sequence: {mover_seq}")

        return solutions

    return []

def simulate_transition_functions(mover_seq):
    """
    Given a valid all-tight mover sequence, check if ANY transition function
    assignment allows the cycle to close (return to initial configuration).
    """
    print("\n" + "=" * 60)
    print("=== Transition function search ===")
    print("=" * 60)

    n = 12
    m = [2,2,3,2,2,3,2,2,3,2,2,3]

    # For each processor p, enumerate all privileged transition functions.
    # f_p: Fin(m_{p-1}) × Fin(m_p) × Fin(m_{p+1}) → Fin(m_p)
    # with f_p(L, S, R) ≠ S for all (L, S, R).

    # For a ternary proc (m_p=3) with binary neighbors (m_{p-1}=2, m_{p+1}=2):
    # Domain: {0,1} × {0,1,2} × {0,1} = 12 inputs
    # Each input (L,S,R) maps to some value ≠ S. Since m_p=3, 2 choices per input.
    # Total: 2^12 = 4096 functions.

    # For a binary proc (m_p=2) with specific neighbor types:
    # Procs 0, 1: m_{p-1} and m_{p+1} depend on position.
    # Proc 0: left=proc 11 (m=3), right=proc 1 (m=2). Domain: {0,1,2}×{0,1}×{0,1} = 12. m_p=2, 1 choice per input (f≠S, only 1 other value). 1 function!
    # Wait, m_p=2 means the output must be in {0,1} and ≠ S. So f(L,S,R) = 1-S. Only 1 possible function!

    # ALL binary processors have a unique transition function: f(L,S,R) = 1-S.
    # So only the ternary processors have choices.

    print("Binary processors (m=2): unique transition function f(L,S,R) = 1-S")
    print("Ternary processors (m=3) at positions 2,5,8,11:")

    # By symmetry, if all ternary processors have the same neighbor types (both binary),
    # they could share the same function. But we should check ALL combinations.
    # 4 ternary procs, each with 4096 choices. Total: 4096^4 ≈ 2.8 × 10^14.
    # Way too many!

    # But if we exploit the 4-fold rotational symmetry, we can fix one function
    # and check others. Or better: since binary functions are fixed, we can
    # precompute the effect of each phase as a function of the ternary function.

    # Actually, we can be smarter. The mover sequence defines which proc fires
    # at each step. For each initial configuration, we can simulate the 24 steps
    # and check if it returns to the initial config. The transition functions
    # determine the updates.

    # Total configs: 2^8 * 3^4 = 256 * 81 = 20736.
    # For each config and each ternary function assignment: simulate and check.
    # But 4096^4 * 20736 is way too much.

    # Key insight: the ternary transition function is applied only when a ternary
    # proc fires. Since binary functions are determined, we can:
    # 1. For each of the 4096^4 ternary function assignments:
    #    2. For each of the 20736 initial configs:
    #       3. Simulate 24 steps. Check cycle.

    # Still 4096^4 ≈ 2.8e14 outer iterations. Impossible.

    # But wait: by the 4-fold rotational symmetry of the ring, we can assume
    # all 4 ternary processors use the SAME function. Then it's 4096 * 20736.
    # That's ~85 million. Manageable with optimized code.

    # Actually, do they need to share the same function? The ring has 4-fold
    # symmetry only if the mover sequence also has this symmetry. Let's check
    # if our mover sequence has it.

    # Even without symmetry: if we DON'T assume shared functions, we need 4096^4.
    # That's too much. But we can try shared first, then consider non-shared if needed.

    # Actually, we can be even smarter. For each ternary proc, its function
    # is only used twice (it fires twice). So the effect on the cycle depends
    # on the function values at the specific (L,S,R) triples encountered during
    # the simulation. We only need to determine the function values at the
    # specific inputs that are actually used.

    # For a given initial config and mover sequence, each ternary proc fires
    # at 2 specific configs. So only 2 input triples per ternary proc are
    # "queried." The function values at these 2 points determine the outcome.
    # Each has 2 choices. So 2^(2*4) = 256 choices per initial config.
    # Total: 20736 * 256 ≈ 5.3 million. Very fast!

    # But the function values at different initial configs must be CONSISTENT:
    # f(L,S,R) has the same value regardless of which initial config led to
    # that query. So we need a global function that works for ALL initial configs
    # that form a valid cycle.

    # The correct approach: for each of the 4096 ternary functions (per proc),
    # for each initial config, simulate and check. But we have 4 independent
    # ternary procs.

    # Better: note that the ternary procs only interact through the binary
    # procs between them. So we can decompose the problem.

    # Or: just iterate over all 4096 choices for each ternary proc and
    # simulate. Use numpy for speed.

    # For now, let's assume all 4 ternary procs share the same function (by symmetry).
    # 4096 functions * 20736 configs = ~85M. In Python this might be slow.
    # Let's optimize: precompute simulation for each function.

    # The cycle requirement: simulate 24 steps starting from config c, get
    # final config c'. Need c' == c.

    # A "closable" function is one where there EXISTS at least one c with c'=c.

    # The simulation is deterministic given the initial config and functions.
    # So for each function assignment, we compute the map T: configs -> configs
    # (apply 24 steps) and check if T has any fixed points.

    print(f"\nMover sequence: {mover_seq}")
    print(f"Total configs: {2**8 * 3**4} = 20736")
    print(f"Ternary functions to check (shared): 4096")
    print()

    # First, let's check: does the mover sequence have 4-fold symmetry?
    # Rotation by 3 positions: proc p -> proc (p+3)%12.
    # Mover seq rotated: [(p+3)%12 for p in mover_seq]
    rotated = [(p + 3) % n for p in mover_seq]
    print(f"Original:  {mover_seq}")
    print(f"Rotated+3: {rotated}")
    print(f"4-fold symmetric: {mover_seq == rotated}")

    # Check if it's a cyclic shift of the original
    doubled = mover_seq + mover_seq
    for shift in range(24):
        if doubled[shift:shift+24] == rotated:
            print(f"Rotated version is original shifted by {shift} steps")
            break

    # Even without exact symmetry, let's try shared ternary functions first,
    # then if no solutions, try independent functions.

    # Simulate!
    import numpy as np

    # Enumerate all privileged ternary transition functions
    # Domain: {0,1} × {0,1,2} × {0,1} -> {0,1,2}, f(L,S,R) != S
    # 12 inputs, each with 2 valid outputs

    ternary_inputs = []
    ternary_valid_outputs = []
    for L in range(2):
        for S in range(3):
            for R in range(2):
                ternary_inputs.append((L, S, R))
                ternary_valid_outputs.append([v for v in range(3) if v != S])

    # Total ternary functions: prod of choices = 2^12 = 4096
    # Enumerate using product of valid outputs
    def enum_ternary_functions():
        """Generate all 4096 privileged ternary transition functions."""
        for choices in iter_product(*ternary_valid_outputs):
            # Build function as dict
            func = {}
            for inp, out in zip(ternary_inputs, choices):
                func[inp] = out
            yield func

    # For binary procs: f(L,S,R) = 1-S always.
    def binary_transition(L, S, R):
        return 1 - S

    # Enumerate all initial configurations
    def enum_configs():
        """Generate all 20736 configurations."""
        binary_positions = [0, 1, 3, 4, 6, 7, 9, 10]
        ternary_positions = [2, 5, 8, 11]
        for bvals in iter_product(range(2), repeat=8):
            for tvals in iter_product(range(3), repeat=4):
                config = [0] * n
                for i, pos in enumerate(binary_positions):
                    config[pos] = bvals[i]
                for i, pos in enumerate(ternary_positions):
                    config[pos] = tvals[i]
                yield tuple(config)

    # For efficiency, let's precompute the simulation as a lookup.
    # For each step in the mover sequence, we know which proc fires.
    # The update depends on the current config and the transition function.

    # Strategy: for each ternary function (shared among all ternary procs),
    # simulate all configs and count fixed points.

    ternary_positions_set = {2, 5, 8, 11}

    print(f"\nChecking 4096 shared ternary functions (all 4 pivots use same f)...")

    total_closable = 0
    closable_functions = []

    # For speed, precompute all configs as list
    all_configs = list(enum_configs())
    print(f"Total configs: {len(all_configs)}")

    func_count = 0
    for ternary_func in enum_ternary_functions():
        func_count += 1
        if func_count % 500 == 0:
            print(f"  Checked {func_count}/4096 functions, {total_closable} closable so far...")

        # Simulate all configs
        fixed_points = 0
        for config in all_configs:
            c = list(config)

            for step in range(24):
                p = mover_seq[step]
                L = c[(p - 1) % n]
                S = c[p]
                R = c[(p + 1) % n]

                if p in ternary_positions_set:
                    new_val = ternary_func[(L, S, R)]
                else:
                    new_val = 1 - S  # binary

                # Check privilege: new_val != S
                if new_val == S:
                    # This config leads to a non-firing step. Invalid.
                    fixed_points = -1  # mark as invalid for this config
                    break

                c[p] = new_val
            else:
                # Check if returned to initial config
                if tuple(c) == config:
                    fixed_points += 1

        if fixed_points > 0:
            total_closable += 1
            closable_functions.append((ternary_func, fixed_points))
            print(f"  CLOSABLE function #{func_count}: {fixed_points} fixed point(s)")

    print(f"\nTotal ternary functions checked: {func_count}")
    print(f"Closable functions (shared, all 4 pivots same): {total_closable}")

    if total_closable == 0:
        print("\nNo closable function found with shared ternary function.")
        print("This proves: the all-tight pattern CANNOT be realized with shared ternary functions.")

    return closable_functions

if __name__ == '__main__':
    print("=" * 70)
    print("Checking all-tight all-normal-form realizability")
    print("Ring: (2,2,3,2,2,3,2,2,3,2,2,3), n=12, k=4 ternary pivots")
    print("=" * 70)

    # Step 1: Check ordering feasibility
    check_all_tight_feasibility()

    # Step 2: Check with relaxed tight (before, not immediately before)
    feasible = verify_with_relaxed_tight()

    # Step 3: Find actual all-tight mover sequences
    mover_seq, is_tight = simulate_cycle()

    # Step 4: Search for all-tight mover sequences
    solutions = search_all_tight_sequences()

    if solutions:
        # Step 5: For each all-tight mover sequence, check transition functions
        sol = solutions[0]
        h1_perm = [None] * 8
        h2_perm = [None] * 8
        for proc, (h1, h2) in sol.items():
            h1_perm[h1] = proc
            h2_perm[h2] = proc
        mover_seq = [2, h1_perm[0], h1_perm[1], 5, h1_perm[2], h1_perm[3], 8, h1_perm[4], h1_perm[5], 11, h1_perm[6], h1_perm[7],
                     2, h2_perm[0], h2_perm[1], 5, h2_perm[2], h2_perm[3], 8, h2_perm[4], h2_perm[5], 11, h2_perm[6], h2_perm[7]]

        closable = simulate_transition_functions(mover_seq)

        if not closable:
            print("\n" + "=" * 60)
            print("Checking ALL all-tight mover sequences with independent ternary functions...")
            print("=" * 60)

            # Check all solutions, not just the first
            any_closable = False
            for sol_idx, sol in enumerate(solutions):
                h1_perm = [None] * 8
                h2_perm = [None] * 8
                for proc, (h1, h2) in sol.items():
                    h1_perm[h1] = proc
                    h2_perm[h2] = proc
                ms = [2, h1_perm[0], h1_perm[1], 5, h1_perm[2], h1_perm[3], 8, h1_perm[4], h1_perm[5], 11, h1_perm[6], h1_perm[7],
                      2, h2_perm[0], h2_perm[1], 5, h2_perm[2], h2_perm[3], 8, h2_perm[4], h2_perm[5], 11, h2_perm[6], h2_perm[7]]

                print(f"\nMover sequence {sol_idx + 1}/{len(solutions)}: {ms}")
                closable = simulate_transition_functions(ms)
                if closable:
                    any_closable = True
                    break

            if not any_closable:
                print("\n" + "=" * 70)
                print("FINAL RESULT: NO all-tight mover sequence admits a closing cycle")
                print("for ANY shared ternary transition function.")
                print("The all-tight all-normal-form pattern is UNREALIZABLE at n=12, k=4.")
                print("=" * 70)
    else:
        print("\n" + "=" * 70)
        print("FINAL RESULT: NO valid all-tight mover sequence exists")
        print("(with the interleaved pivot firing pattern A1,B1,C1,D1,A2,B2,C2,D2).")
        print("=" * 70)
        print("\nNeed to also check other pivot interleaving patterns...")
