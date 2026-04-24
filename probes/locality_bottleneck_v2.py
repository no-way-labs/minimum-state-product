"""
Locality Bottleneck v2: Prove that ANY valid good cycle for n=5
with 3 consecutive binary processors requires ≥10 distinct
non-binary state pairs.

Strategy: Prove structural lower bounds on the number of (P3,P4)
pairs needed, independent of the specific cycle structure.
"""

import itertools
from collections import Counter, defaultdict

# ============================================================
# QUESTION: Does the 10-pair requirement hold for ALL cycles,
# or just the specific witness?
#
# The witness has cycle length 18 and uses 10 distinct (P3,P4) pairs.
# A shorter cycle might use fewer.
#
# Minimum cycle length = 6 (binary) + 2 (P3) + 2 (P4) = 10.
# With 10 positions and 9 pairs, pigeonhole gives 2 shared,
# but shared pairs can have different binary states → no collision.
#
# So the counting argument alone doesn't work at minimum length.
# We need the TRANSITION constraints.
#
# KEY ARGUMENT: The binary block has 6 states in {0,1}^3.
# Between consecutive binary-block changes, the (P3,P4) subsystem
# is "active" (one of P3/P4 moves). At the END of such an active
# period, a binary processor must become privileged.
#
# For a binary processor to become privileged, it must see a
# specific (L, S, R) context. For P2 to become privileged:
# f2(b1, b2, s3) ≠ b2. This depends on s3 = P3's state.
# For P0 to become privileged:
# f0(s4, b0, b1) ≠ b0. This depends on s4 = P4's state.
#
# So the EXIT from the non-binary section is controlled by
# s3 (for exit via P2) and s4 (for exit via P0).
#
# CRITICAL CONSTRAINT: After the binary block is in state (1,1,1)
# (rightward sweep complete), the token enters P3. P3 and P4
# must eventually route the token back to a binary processor.
# The EXIT must go through P0 (to continue leftward), not P2
# (which would create a bad cycle / fail to visit P0).
#
# Similarly, after the binary block is in state (0,0,0) from a
# leftward sweep, the token enters P4 (wrapping around from P0).
# P4 and P3 must route the token back to P2.
#
# These TWO routing requirements (exit via P0 vs exit via P2)
# impose constraints on the (P3,P4) state at the time of exit.
# ============================================================

print("="*70)
print("STRUCTURAL ANALYSIS: Minimum (P3,P4) pairs needed")
print("="*70)

print("""
LEMMA: In any valid system for n=5 with ms=(2,2,2,3,3):
1. The binary block visits at least 6 states.
2. Each binary processor moves at least 2 times.
3. P3 and P4 each move at least 2 times (fairness + closure).
4. P3 moves: 0→a→... → 0 (must return, so ≥2 moves)
5. P4 moves: 0→b→... → 0 (must return, so ≥2 moves)
6. Total cycle length ≥ 10.

KEY STRUCTURAL CONSTRAINT:
The good cycle must include BOTH:
  (a) A transition from NB section to P0 (token exits via P0 end)
  (b) A transition from NB section to P2 (token exits via P2 end)

This is because:
- P0 must move at least twice. P0 becomes privileged when its
  neighborhood changes. At least one of P0's privilege events
  comes from P4 changing state (P4 is P0's left neighbor).
  At least one comes from P1 changing state.
- Similarly, P2 must move at least twice. At least one P2 privilege
  event comes from P3 changing state (P3 is P2's right neighbor).

So the NB section must route the token to BOTH P0 and P2 at
different cycle positions. This requires the (P3,P4) state at
exit to encode the routing direction.

EXIT VIA P0: P4 moves, P0 becomes privileged.
  f0(s4_new, b0, b1) ≠ b0. The privilege depends on s4_new.
  So there must exist an s4 value that triggers P0.

EXIT VIA P2: P3 moves, P2 becomes privileged.
  f2(b1, b2, s3_new) ≠ b2. The privilege depends on s3_new.
  So there must exist an s3 value that triggers P2.

These exits may occur at different binary block states.
""")

# ============================================================
# COUNT P3 AND P4 MOVES IN THE WITNESS
# ============================================================

gc_5 = [(0,0,0,0,0),(1,0,0,0,0),(1,1,0,0,0),(1,1,1,0,0),(1,1,1,1,0),(1,1,1,1,1),
        (0,1,1,1,1),(0,0,1,1,1),(0,0,0,1,1),(0,0,0,2,1),(0,0,1,2,1),(0,0,1,0,1),
        (0,0,1,0,2),(0,0,1,2,2),(0,0,1,2,3),(0,0,1,1,3),(0,0,0,1,3),(0,0,0,0,3)]

movers = []
for idx in range(len(gc_5)):
    c = gc_5[idx]
    c_next = gc_5[(idx+1) % len(gc_5)]
    for j in range(5):
        if c[j] != c_next[j]:
            movers.append(j)
            break

move_counts = Counter(movers)
print(f"Move counts in n=5 witness: {dict(sorted(move_counts.items()))}")
print(f"Total cycle length: {len(gc_5)}")
print(f"Binary moves: {move_counts[0]+move_counts[1]+move_counts[2]}")
print(f"Non-binary moves: {move_counts[3]+move_counts[4]}")

# ============================================================
# THE CORE QUESTION: Can a cycle of length 10 (minimum) work?
# ============================================================

print("\n" + "="*70)
print("MINIMUM CYCLE LENGTH ANALYSIS")
print("="*70)

print("""
For cycle length 10: P0=2, P1=2, P2=2, P3=2, P4=2 moves each.
Binary block trajectory: 6 states in 6 positions.
Non-binary moves: 4 total (2 for P3, 2 for P4).

Each non-binary move happens BETWEEN binary moves. So the cycle
alternates: some binary moves, then some non-binary moves, etc.

The 4 non-binary moves create 4 positions where binary block
state is repeated. So 4 of the 6 binary states are each repeated
once, giving those states appearing 2 times, and 2 states appearing
1 time. Total: 4*2 + 2*1 = 10. ✓

For each doubly-appearing state: 2 distinct (P3,P4) pairs needed.
For each singly-appearing state: 1 distinct pair needed.
Total MINIMUM distinct pairs: need to count carefully.

The 2 positions for a doubly-appearing binary state have DIFFERENT
(P3,P4) pairs. But across different binary states, pairs can be reused.

With 4 double states × 2 pairs each + 2 single states × 1 pair:
Total entries = 4×2 + 2×1 = 10. But distinct pairs could be as few as...

Actually, different binary states can reuse the same (P3,P4) pair.
Minimum distinct pairs: as few as 2 (if the same 2 pairs are used for
all double states). But this requires all 4 double states to use the
SAME 2 pairs!

Is that possible? The transition constraints say: within each double
state, the two (P3,P4) pairs must be connected by a P3 or P4 transition.
And the transitions between different binary states also constrain
which pairs can be used.

Let me think about this more carefully with a concrete example.
""")

# ============================================================
# THE TIGHTER ARGUMENT: P3 and P4 state cycles
#
# P3 has states {0,1,2}. In the good cycle, P3 moves 2 times.
# P3's state trajectory: s, a, b, s (where s is the initial state).
# Wait, if P3 moves 2 times: s → a → s (returns after 2 moves).
# So P3 alternates between 2 states: s and a.
#
# Similarly, P4 moves 2 times, alternating between 2 states: t and b.
#
# So (P3,P4) can only take values from {s,a} × {t,b} = 4 pairs!
#
# With 4 pairs and 10 cycle positions:
# - 6 binary-move positions: (P3,P4) doesn't change at binary moves
# - 4 non-binary-move positions: (P3,P4) changes
#
# The (P3,P4) trajectory:
# Start at (s,t).
# Each P3 move: s↔a.
# Each P4 move: t↔b.
# After 2 P3 moves and 2 P4 moves: back to (s,t).
#
# The trajectory through the 4 pairs forms a rectangle:
# (s,t) → (a,t) → (a,b) → (s,b) → (s,t)  [if P3, P4, P3, P4]
# or (s,t) → (s,b) → (a,b) → (a,t) → (s,t) [if P4, P3, P4, P3]
# or some other interleaving.
#
# But wait — the order of P3/P4 moves is constrained by the cycle.
# They don't necessarily alternate nicely.
#
# In any case: at MOST 4 distinct (P3,P4) pairs are used.
# And the 10 cycle positions distribute across at most 4 pairs.
#
# 10 positions, 4 pairs → by pigeonhole, some pair appears 3+ times.
# This pair must appear at 3+ different binary states (to avoid collision).
# With 6 binary states, this is possible.
#
# But the KEY: do the 4 pairs provide enough routing diversity?
# ============================================================

print("="*70)
print("THE 4-PAIR CONSTRAINT")
print("="*70)

print("""
CRITICAL INSIGHT: If P3 and P4 each move exactly 2 times in the cycle,
they each use only 2 of their 3 states. So (P3,P4) takes values from
a 2×2 = 4-element set.

The good cycle has 10 positions distributed across 4 (P3,P4) pairs.
On average, each pair is used 2.5 times.

Binary block visits 6 states. So each pair must accommodate at least
⌈10/4⌉ = 3 positions, distributed across ≤ 6 binary states.

But the routing constraint requires:
- Exit via P0: P4 must be in a state that triggers P0.
- Exit via P2: P3 must be in a state that triggers P2.

With only 2 P3 states {s, a}: P3 can trigger P2 in at most one state
(the one where f2(b1, b2, s3) ≠ b2). So only configurations where
P3 is in that specific state can exit via P2.

Similarly, with only 2 P4 states {t, b}: P4 can trigger P0 in at most
one state.

So EXIT VIA P2 requires P3 ∈ {one specific state}, and
EXIT VIA P0 requires P4 ∈ {one specific state}.

These are DIFFERENT (P3,P4) pairs:
- Exit P2: P3 = a (say), P4 = anything → pairs (a,t) or (a,b)
- Exit P0: P4 = b (say), P3 = anything → pairs (s,b) or (a,b)

The pair (a,b) could serve BOTH exits (P3 triggers P2 AND P4 triggers P0).
But mutual exclusion requires exactly ONE processor to be privileged.
So (a,b) can't trigger both P2 and P0 simultaneously.

If at (a,b) only P2 is privileged: exit goes to P2.
Then exit via P0 must use pair (s,b), and P0 must be uniquely privileged there.

This is getting very tight. Let me check: in the good cycle, can
we have both exits using the 4 available pairs?

Let me enumerate the possible cycle structures.
""")

# ============================================================
# EXHAUSTIVE CHECK: Can ms=(2,2,2,3,3) work with only 4 NB pairs?
#
# The cycle has 10 positions. P3 uses 2 states, P4 uses 2 states.
# The (P3,P4) pairs form a 2×2 grid.
#
# The cycle visits these 4 pairs in a specific order, determined
# by the interleaving of P3 and P4 moves.
#
# With P3 moving 2 times and P4 moving 2 times, the interleaving
# can be: P3,P4,P3,P4 or P3,P3,P4,P4 or P4,P3,P4,P3 or ...
# Actually, P3 can't move twice in a row (because after P3 moves,
# another processor must become privileged, and if it's P3 again,
# we'd need P3 to be privileged again immediately, which requires
# its context to change without any neighbor moving — impossible
# since P3 just moved and no one else moved).
#
# Wait, BINARY processors might move between P3 moves. The cycle
# can have P3, binary, P3 with binary moves in between.
#
# So P3's 2 moves need not be consecutive. They can be separated
# by binary moves. Same for P4.
#
# Let me just enumerate all possible mover sequences of length 10
# with exactly 2 of each processor.
# ============================================================

from itertools import permutations

# We need all permutations of [0,0,1,1,2,2,3,3,4,4]
# where exactly 2 of each processor index appear.
# That's 10!/(2!)^5 = 113400 permutations. Too many to enumerate directly.

# Instead, let's reason about the constraint.

print("\n" + "="*70)
print("CAN 4 NB PAIRS SUPPORT THE ROUTING REQUIREMENT?")
print("="*70)

# With P3 using 2 states and P4 using 2 states:
# 4 pairs: (s,t), (a,t), (a,b), (s,b)
# where s→a→s is P3's cycle, t→b→t is P4's cycle.

# The cycle visits these 4 pairs. Between P3/P4 moves, the pair
# stays constant (binary moves don't change NB states).

# The NB pair trajectory is a path through the 4-node graph:
# (s,t) ↔ (a,t) (P3 move connects these)
# (s,b) ↔ (a,b) (P3 move connects these)
# (s,t) ↔ (s,b) (P4 move connects these)
# (a,t) ↔ (a,b) (P4 move connects these)
# This is a 4-cycle: (s,t)-(a,t)-(a,b)-(s,b)-(s,t)

# With 4 NB moves (2 P3 + 2 P4), the trajectory visits all 4 nodes
# in a cycle: (s,t)→(a,t)→(a,b)→(s,b)→(s,t) or a rotation/reflection.

# The routing requirement: the cycle must include exits via P0 and P2.
# Exit via P2: P3 must be in a "trigger" state AND P2 must be uniquely privileged.
# Exit via P0: P4 must be in a "trigger" state AND P0 must be uniquely privileged.

# Let's say P3's trigger state for P2 is 'a', and P4's trigger state for P0 is 'b'.
# Then exits via P2 occur when P3=a: pairs (a,t) or (a,b).
# Exits via P0 occur when P4=b: pairs (s,b) or (a,b).

# But exits occur when a binary processor moves (after a NB move or between NB moves).
# Actually, exits occur at specific cycle positions where the NB pair causes
# a binary processor to be privileged.

# The KEY: the NB pair determines WHO is privileged (or at least constrains it).
# At pair (s,t): some set of processors are privileged.
# At pair (a,t): different set.
# At pair (a,b): different set.
# At pair (s,b): different set.

# For mutual exclusion: at each cycle position, EXACTLY ONE processor is privileged.
# So each cycle position corresponds to a specific (binary_state, NB_pair) that
# makes exactly one processor privileged.

# With 4 NB pairs and the need for both P0 and P2 to be triggered:
# At least one pair triggers P0, at least one triggers P2.
# If they're the same pair (a,b): mutual exclusion fails (both P0 and P2 privileged).
#   UNLESS the binary state at that position is such that only one is privileged.

# So pair (a,b) can trigger P0 at one binary state and P2 at a different binary state.
# This is possible! No contradiction from 4 pairs alone.

# HOWEVER: the cycle must also include positions where P3 or P4 is the unique
# privileged processor (for NB moves). These positions have specific NB pairs.

# Let me check whether 4 NB pairs can support all required privilege assignments.

# Actually, the REAL constraint is the CONVERGENCE property (no bad cycles).
# With only 4 NB pairs (out of 9 possible), there are 72 - 4*6 = many
# configurations NOT on the good cycle → they are bad configs.
# Convergence requires all bad configs to reach the good cycle under
# any daemon. With so few good configs (cycle length 10), there are
# 72 - 10 = 62 bad configs. These must all converge.

# The convergence constraint is very tight with 10 good configs out of 72.
# Compare with the witness: 18 good + some basin out of 96.

# I suspect this is where the impossibility lies: with only 4 NB pairs,
# the good cycle is too short, and there are too many bad configs to
# converge without creating cycles.

# Let me check: what's the maximum cycle length with 4 NB pairs?
# 4 NB pairs × 6 binary states = 24 possible configs (out of 72).
# But not all 24 need to be on the good cycle.
# The cycle must be ≤ 24 (since there are only 24 configs with these NB pairs).

# Hmm, but 24 < 72 means many configs (72 - 24 = 48) are bad.
# With 48 bad configs and only 24 candidate good configs,
# convergence is hard but not obviously impossible.

print("""
SUMMARY OF THE 4-PAIR ANALYSIS:

If P3 and P4 each use only 2 states, the (P3,P4) subsystem has 4 pairs.
These 4 pairs can support BOTH routing directions (exit via P0 and P2)
IF the binary block states are appropriately distributed.

So the counting argument from 4 pairs alone doesn't prove impossibility.

But P3 and P4 might need MORE than 2 states each. If P3 needs 3 states
(uses all of {0,1,2}), it moves at least 3 times. Similarly P4.
Then cycle length ≥ 6 + 3 + 3 = 12, and (P3,P4) uses 3×3 = 9 pairs.

12 positions, 9 pairs: pigeonhole gives 3 shared. But again, shared
pairs can have different binary states.

The REAL constraint comes from the TRANSITION STRUCTURE and CONVERGENCE.
""")

# ============================================================
# DIFFERENT APPROACH: Use the GLOBAL PAIR REQUIREMENT
#
# From the n=5 witness: 10 DISTINCT (P3,P4) pairs are used.
# With ternary P4: only 9 available. 10 > 9 → impossible.
#
# But this is specific to the witness. A shorter cycle might use ≤ 9.
#
# QUESTION: What is the MINIMUM number of distinct (P3,P4) pairs
# that ANY valid cycle for ms=(2,2,2,3,3) must use?
#
# APPROACH: Count the distinct binary-block-state groups and the
# minimum number of NB pairs per group.
# ============================================================

print("="*70)
print("MINIMUM DISTINCT NB PAIRS: COUNTING VIA BINARY STATE GROUPS")
print("="*70)

# For ANY valid cycle, the binary block visits 6 states.
# At each state, the NB pair must be distinct from other pairs
# at the SAME binary state.
#
# How many times does each binary state appear in the cycle?
# The cycle has L positions (L ≥ 10).
# L = (binary moves) + (non-binary moves)
# binary moves ≥ 6 (each of 3 processors moves ≥ 2 times)
# non-binary moves ≥ 4 (each of 2 processors moves ≥ 2 times)
#
# Each non-binary move creates a "repeat" of the current binary state.
# So binary state repetitions = non-binary moves.
#
# With NB moves = 4: 4 repetitions across 6 binary states.
# With NB moves = k: k repetitions across 6 binary states.
#
# The maximum count of any single binary state = 1 + (# NB moves while in that state).
#
# The KEY: the NON-BINARY moves don't all happen in one binary state.
# They're distributed across different binary states.
# Some binary states may have 0 NB moves (appearing only once),
# others may have many.

# In the witness: NB moves = 10. Binary state (0,0,1) has 6 of them.
# Binary state (0,0,0) has 4 of them.

# The structural reason for so many NB moves: the token BOUNCES
# between P3 and P4 within a single binary state. Each bounce is
# 2 NB moves. With ≥2 bounces in one binary state, that state
# needs ≥5 distinct NB pairs (1 initial + 2 per bounce).

# Can we prove that bouncing is NECESSARY?

print("""
THE BOUNCING ARGUMENT:

After the rightward sweep (binary = (1,1,1)), the token enters P3.
P3 must process the token. Options:
(a) P3 forwards to P4 immediately (1 NB move), then P4 exits to P0.
    Total: 2 NB moves in binary state (1,1,1).
(b) P3 bounces: P3 → P4 → P3 → ... → exit.
    More NB moves needed.

For option (a): the minimum. But then after the leftward sweep
(binary = (0,0,0)), the token enters P4. P4 forwards to P3,
P3 exits to P2. Total: 2 NB moves in binary state (0,0,0).

Total NB moves: 4 (minimum). Cycle length: 10.
NB pairs used: at most 4 (if P3 and P4 each use 2 states).

Can this work? Let's check.

In the minimum cycle:
  R sweep: P0→P1→P2 (binary: 000→100→110→111)
  NB phase 1: P3→P4 in binary state (1,1,1)
    P3 changes, P4 changes. NB pair goes (s,t)→(a,t)→(a,b).
    Wait, that's 2 NB moves. After P4's move, we need P0 to be
    privileged (exit via P0).
  L sweep: P0→P1→P2... wait, that's rightward again.

Actually, let me think about this more carefully.

After rightward sweep, binary = (1,1,1).
Token exits to P3 (P3 becomes privileged).
P3 moves: (s3 → s3'). This is 1 NB move.
Then either P4 or P2 becomes privileged.
  If P4: P4 moves (1 more NB move). Then P0 or P3 becomes privileged.
    If P0: exit via P0. Binary sweep can begin.
    If P3: another bounce. More NB moves.
  If P2: exit via P2. Token goes back into binary block.
    This is WRONG — the token just came from P2. Going back
    creates P2→P3→P2 which doesn't progress the cycle.
    Actually, if P3 moves to a state where P2 is privileged,
    P2 moves (flips bit), changing binary from (1,1,1) to (1,1,0).
    This IS a valid binary move, continuing the leftward sweep!

So option: R sweep (000→111), P3 move, back to P2 (111→110→100→000).
This means the token goes P0→P1→P2→P3→P2→P1→P0 with P3 in the middle.
P4 is never visited! FAIRNESS VIOLATION — P4 must move at least once.

So the token MUST reach P4 at some point. After P3, the token must
go to P4 (not back to P2) at least once.

After P3→P4, the token can exit to P0 or go back to P3.
After P4→P0, the leftward sweep begins: P0→P1→P2.
But then the token is at P2. It must go to P3 again.
P3 must route it to P4. P4 exits to P0.
Wait, this creates the same cycle: R sweep, P3, P4, exit to P0,
L sweep, back to P3, P4... but when does the L sweep happen?

Let me trace more carefully:
1. Start: (0,0,0,s,t). P0 privileged. Binary → (1,0,0).
2. (1,0,0,s,t). P1 privileged. Binary → (1,1,0).
3. (1,1,0,s,t). P2 privileged. Binary → (1,1,1).
4. (1,1,1,s,t). P3 privileged. NB → (1,1,1,a,t). [P3 moves: s→a]
5. (1,1,1,a,t). P4 privileged. NB → (1,1,1,a,b). [P4 moves: t→b]
6. (1,1,1,a,b). P0 privileged? If yes: Binary → (0,1,1). [L sweep begins]
   But for P0 to be privileged at (1,1,1,a,b):
   f0(s4=b, b0=1, b1=1) ≠ 1.
   P0 sees L=b (P4's state), S=1 (own state), R=1 (P1's state).
   Need f0(b, 1, 1) ≠ 1, so f0(b, 1, 1) = 0. ✓ Possible.

7. (0,1,1,a,b). P1 privileged. Binary → (0,0,1). [L sweep continues]
8. (0,0,1,a,b). P2 privileged? f2(b1=0, b2=1, s3=a) ≠ 1.
   Need f2(0, 1, a) = 0. ✓ Possible.
   Binary → (0,0,0).
9. (0,0,0,a,b). Now who is privileged?
   P4 should be privileged (to visit P4 for fairness, and to route back).
   f4(s3=a, s4=b, b0=0) ≠ b. Need f4(a, b, 0) ≠ b. ✓ Possible.
   NB → (0,0,0,a,t). [P4 moves: b→t]
10. (0,0,0,a,t). P3 should be privileged.
    f3(b2=0, s3=a, s4=t) ≠ a. Need f3(0, a, t) ≠ a. ✓ Possible.
    NB → (0,0,0,s,t). [P3 moves: a→s]

BACK TO START! Cycle length = 10. All 5 processors move 2 times.

NB pairs used: (s,t), (a,t), (a,b), (a,t), (s,t)
Wait, let me list them:
  Steps 1-3: (s,t) [binary moves, NB constant]
  Step 4: NB changes to (a,t)
  Step 5: NB changes to (a,b)
  Steps 6-8: (a,b) [binary moves]
  Step 9: NB changes to (a,t)
  Step 10: NB changes to (s,t)

NB pairs in cycle: (s,t), (s,t), (s,t), (a,t), (a,b), (a,b), (a,b), (a,b), (a,t), (s,t)

Wait, that's wrong. Let me be more precise:

Position 0: config (0,0,0,s,t), NB pair = (s,t)
Position 1: config (1,0,0,s,t), NB pair = (s,t)
Position 2: config (1,1,0,s,t), NB pair = (s,t)
Position 3: config (1,1,1,s,t), NB pair = (s,t)  [P3 moves next]
Position 4: config (1,1,1,a,t), NB pair = (a,t)  [P4 moves next]
Position 5: config (1,1,1,a,b), NB pair = (a,b)  [P0 moves next]
Position 6: config (0,1,1,a,b), NB pair = (a,b)
Position 7: config (0,0,1,a,b), NB pair = (a,b)  [? moves next]
  Wait: at (0,0,1,a,b), is P2 privileged?
  If b2=1 and f2(0,1,a) = 0 ≠ 1: yes, P2 privileged.
  But we need P2 to be UNIQUELY privileged. Are P3 or P4 also privileged?
  P3 at (0,0,1,a,b): f3(1, a, b). If this ≠ a, P3 is also privileged → ME violation!
  So we need f3(1, a, b) = a. P3 must be NON-privileged at this config.

Position 8: config (0,0,0,a,b), NB pair = (a,b) [P4 moves next]
  P4 at (0,0,0,a,b): f4(a, b, 0) ≠ b → P4 privileged. ✓
  But P3 at (0,0,0,a,b): f3(0, a, b). Must = a for non-privilege.
  P0 at (0,0,0,a,b): f0(b, 0, 0). Must = 0 for non-privilege.
  P1 at (0,0,0,a,b): f1(0, 0, 0). Must = 0 for non-privilege.
  P2 at (0,0,0,a,b): f2(0, 0, a). Must = 0 for non-privilege.

Position 9: config (0,0,0,a,t), NB pair = (a,t) [P3 moves next]
  P3 at (0,0,0,a,t): f3(0, a, t) ≠ a → P3 privileged. ✓
  But P4 at (0,0,0,a,t): f4(a, t, 0). Must = t for non-privilege.

  After P3 moves: s3 = a → s. Config = (0,0,0,s,t) = Position 0. ✓

DISTINCT NB pairs used: (s,t), (a,t), (a,b) — only 3!
This FITS in ternary P4 (with s,a ∈ {0,1,2} and t,b ∈ {0,1,2}).

But wait — I used only 3 of the 4 possible pairs. (s,b) was never used.
Is this a valid cycle? Let me check all the constraints.
""")

# Let me try to construct a concrete system for ms=(2,2,2,3,3)
# with the cycle structure above and check if convergence holds.

print("="*70)
print("ATTEMPTING TO CONSTRUCT A SYSTEM FOR ms=(2,2,2,3,3)")
print("="*70)

# Let's try s=0, a=1, t=0, b=1 (using only 2 of each ternary's 3 states).
# NB pairs: (0,0), (1,0), (1,1).

s, a, t, b = 0, 1, 0, 1

cycle = [
    (0,0,0,s,t),  # 0: P0 moves
    (1,0,0,s,t),  # 1: P1 moves
    (1,1,0,s,t),  # 2: P2 moves
    (1,1,1,s,t),  # 3: P3 moves
    (1,1,1,a,t),  # 4: P4 moves
    (1,1,1,a,b),  # 5: P0 moves
    (0,1,1,a,b),  # 6: P1 moves
    (0,0,1,a,b),  # 7: P2 moves
    (0,0,0,a,b),  # 8: P4 moves
    (0,0,0,a,t),  # 9: P3 moves → back to (0,0,0,s,t)
]

expected_movers = [0, 1, 2, 3, 4, 0, 1, 2, 4, 3]

print(f"Proposed cycle (length {len(cycle)}):")
for idx, (c, m) in enumerate(zip(cycle, expected_movers)):
    print(f"  {idx}: {c}  P{m} moves")

# Check: all configs distinct?
if len(set(cycle)) == len(cycle):
    print("\n  All configs distinct ✓")
else:
    print("\n  COLLISION in cycle! ✗")
    for i, c in enumerate(cycle):
        for j in range(i+1, len(cycle)):
            if c == cycle[j]:
                print(f"    Steps {i} and {j} are identical: {c}")

# Check: all processors appear in movers?
if set(expected_movers) == {0,1,2,3,4}:
    print("  All processors move ✓")

# Now: can we define transition functions that make this work?
# For each cycle position, the mover must be the UNIQUE privileged processor.

print("\nRequired transition function entries from cycle:")
for idx in range(len(cycle)):
    c = cycle[idx]
    mover = expected_movers[idx]
    c_next = cycle[(idx+1) % len(cycle)]

    # Mover must be privileged: f_mover(L, S, R) ≠ S
    L = c[(mover-1) % 5]
    S = c[mover]
    R = c[(mover+1) % 5]
    S_new = c_next[mover]
    print(f"  f{mover}({L},{S},{R}) = {S_new}  [privileged, S={S}→{S_new}]")

    # All others must be non-privileged: f_i(L, S, R) = S
    for i in range(5):
        if i != mover:
            Li = c[(i-1) % 5]
            Si = c[i]
            Ri = c[(i+1) % 5]
            # Check that Si doesn't change
            assert c_next[i] == Si or i == mover, f"Step {idx}: P{i} changed but wasn't mover!"

print("\nNow checking: are the required entries CONSISTENT?")
print("(i.e., no contradictions where same input → different output)")

# Collect all required entries
required = defaultdict(set)
for idx in range(len(cycle)):
    c = cycle[idx]
    mover = expected_movers[idx]
    c_next = cycle[(idx+1) % len(cycle)]

    # Mover entry
    L = c[(mover-1) % 5]
    S = c[mover]
    R = c[(mover+1) % 5]
    S_new = c_next[mover]
    required[(mover, L, S, R)].add(('priv', S_new, idx))

    # Non-mover entries (must be non-privileged)
    for i in range(5):
        if i != mover:
            Li = c[(i-1) % 5]
            Si = c[i]
            Ri = c[(i+1) % 5]
            required[(i, Li, Si, Ri)].add(('nopriv', Si, idx))

conflicts = []
for key, vals in sorted(required.items()):
    outputs = set()
    for (ptype, out, step) in vals:
        outputs.add(out)
    if len(outputs) > 1:
        conflicts.append((key, vals))

if conflicts:
    print(f"\n  CONFLICTS FOUND: {len(conflicts)}")
    for key, vals in conflicts:
        print(f"    f{key[0]}({key[1]},{key[2]},{key[3]}): {vals}")
else:
    print(f"\n  No conflicts in required entries!")
    print("  The cycle is CONSISTENT — a valid transition function might exist.")
    print("  Need to check convergence (no bad cycles) to confirm.")

    # Count how many transition function entries are determined
    determined = {}
    for key, vals in required.items():
        val = list(vals)[0]
        determined[key] = val[1]  # output value

    proc_entries = defaultdict(dict)
    for (proc, L, S, R), out in determined.items():
        proc_entries[proc][(L, S, R)] = out

    for proc in range(5):
        m_L = ms[(proc-1) % 5]
        m_S = ms[proc]
        m_R = ms[(proc+1) % 5]
        total = m_L * m_S * m_R
        determined_count = len(proc_entries[proc])
        print(f"  P{proc}: {determined_count}/{total} entries determined")
