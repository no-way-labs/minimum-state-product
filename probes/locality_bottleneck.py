"""
Locality Bottleneck: Can distributed routing memory substitute for a quaternary?

The conjecture: in the non-binary section between binary block endpoints,
the routing memory MUST be concentrated in a single processor with ≥4 states.
Two adjacent ternary processors cannot substitute.

Approach: Consider the minimal case — a ring with binary block (B0,B1,B2)
and non-binary section (T3, T4) where T3 and T4 are both ternary (3 states).
This gives ms = (2,2,2,3,3), product 72.

We know product 72 is computationally dead. But WHY?

The argument must show that T3 and T4 together cannot implement the
routing memory that the good cycle requires, despite having 3×3 = 9
combined states.

KEY INSIGHT: The routing decision is made by ONE processor (say T3,
adjacent to the binary block). T3 reads T4 as its R neighbor.
T3's routing decision depends on (L, S, R) = (B2_state, T3_state, T4_state).

For T3 to make 4 distinct routing decisions, it needs to distinguish
4 distinct (S, R) pairs (holding L fixed). With S ∈ {0,1,2} and
R ∈ {0,1,2}, there are 9 pairs. But the constraint is:
- For each (S, R), f_T3(L, S, R) must produce a specific output
- The 4 routing decisions correspond to 4 different (S, R) -> output mappings
- But the routing decision also depends on L (the binary neighbor's state),
  adding more constraints

Let me work through the full constraint system.
"""

import itertools
from collections import defaultdict

# ============================================================
# The minimal pure-{2,3} case: ms = (2,2,2,3,3)
#
# Ring: P0(2) - P1(2) - P2(2) - P3(3) - P4(3) - P0(2)
# Binary block: P0, P1, P2
# Non-binary section: P3, P4
# P3's neighbors: P2 (binary), P4 (ternary)
# P4's neighbors: P3 (ternary), P0 (binary)
# ============================================================

ms = [2, 2, 2, 3, 3]
n = 5

# ============================================================
# Step 1: What does the good cycle look like?
#
# The binary block must visit all 3 processors (fairness).
# The non-binary section must visit both T3 and T4 (fairness).
# The token must reverse direction (since binary processors are valves).
#
# From the n=5 witness, the cycle structure is:
# Phase A: rightward sweep P0→P1→P2 (binary block: 000→111)
# Phase B: token enters P3, navigates P3-P4, eventually returns
# Phase C: leftward sweep P2→P1→P0 (binary block: 111→000)
# Phase D: token navigates P4-P3, returns to P0
#
# But actually, the token must enter the non-binary section from
# BOTH ends of the binary block:
# - From P2's side: after rightward sweep, token goes P2→P3
# - From P0's side: after leftward sweep, token goes P0→P4
#   Wait, P0→P4 means the token wraps around.
#   Actually P4 is P0's left neighbor: P4-P0-P1-P2-P3-P4
#
# Ring topology: P0-P1-P2-P3-P4-P0
# So P0's left neighbor is P4, right neighbor is P1.
# P2's left neighbor is P1, right neighbor is P3.
#
# The token enters the non-binary section:
# - From P2→P3 (rightward, after sweeping right through binary block)
# - From P0→P4 (leftward, wrapping around after sweeping left)
#
# Wait, that's wrong. Let me think about this more carefully.
# After sweeping left (P2→P1→P0), the token is at P0.
# P0's left neighbor is P4. So the token goes P0→P4→P3→P2
# to re-enter the binary block. But that means the token goes
# through P4 first, then P3.
#
# After sweeping right (P0→P1→P2), the token is at P2.
# P2's right neighbor is P3. Token goes P2→P3→P4→P0.
#
# So the non-binary section is traversed in BOTH directions:
# P3→P4 (after rightward sweep) and P4→P3 (after leftward sweep).
# ============================================================

print("="*70)
print("GOOD CYCLE STRUCTURE ANALYSIS FOR ms = (2,2,2,3,3)")
print("="*70)

print("""
Ring topology: P0(2) - P1(2) - P2(2) - P3(3) - P4(3) - P0(2)

The token must complete a cycle visiting all 5 processors.
Key structural constraint: the binary block P0-P1-P2 forces
the token to sweep right (P0→P1→P2) and sweep left (P2→P1→P0)
at least once each.

After rightward sweep: token at P2, exits to P3. Must traverse
P3→P4→P0 to re-enter the binary block from the left.

After leftward sweep: token at P0, exits to P4. Must traverse
P4→P3→P2 to re-enter the binary block from the right.

This gives a MINIMUM cycle skeleton:
  P0→P1→P2 → P3→P4→P0 → P1→P0 (leftward sweep... wait)

Actually, the sweep direction is: which processor moves, not
which direction the token travels. Let me be precise.

When P0 moves (flips bit): token was at P0, now P0's state changed.
The next privileged processor depends on the new configuration.
""")

# ============================================================
# Step 2: THE CORE ARGUMENT
#
# Consider P3 at the boundary. P3 sees:
#   L = P2's state ∈ {0,1}
#   S = P3's own state ∈ {0,1,2}
#   R = P4's state ∈ {0,1,2}
#
# P3 has 2 × 3 × 3 = 18 input contexts.
# P3's transition function has 18 entries, each producing a value in {0,1,2}.
#
# Similarly, P4 sees:
#   L = P3's state ∈ {0,1,2}
#   S = P4's state ∈ {0,1,2}
#   R = P0's state ∈ {0,1}
#
# P4 has 3 × 3 × 2 = 18 input contexts.
#
# KEY CONSTRAINT: After the token sweeps right (P0→P1→P2),
# the binary block is in state (1,1,1). The token exits P2
# to P3. At this point:
#   P3 sees L=1 (P2 in state 1), S=s3, R=r4 (P4's state).
#   P3 must be privileged: f3(1, s3, r4) ≠ s3.
#   P3 transitions to s3' = f3(1, s3, r4).
#   After P3 moves, the token must continue to P4 or return to P2.
#
# After the token sweeps left (P2→P1→P0), the binary block is
# in state (0,0,0). The token exits P0 to P4.
#   P4 sees L=l3 (P3's state), S=s4, R=0 (P0 in state 0).
#   P4 must be privileged: f4(l3, s4, 0) ≠ s4.
#   P4 transitions to s4' = f4(l3, s4, 0).
#   After P4 moves, the token must continue to P3 or return to P0.
#
# The critical question: how many DISTINCT (s3, r4) pairs must
# P3 use across all its privileged moments? And how many distinct
# (l3, s4) pairs must P4 use?
# ============================================================

print("="*70)
print("CONSTRAINT ENUMERATION")
print("="*70)

# We need to enumerate the FORCED structure of the good cycle
# for ms = (2,2,2,3,3).

# Key insight: In the n=5 witness with quaternary, the good cycle
# has length 18. The non-binary section (P3,P4) visits 10 distinct
# state pairs. With ternary P4, only 9 pairs are available.
# But 10 > 9 means AT LEAST two cycle positions must share a
# (P3,P4) pair — potential collision.

# Wait, but the good cycle might be shorter with different ms.
# The minimum cycle length for ms=(2,2,2,3,3) is bounded below
# by the fairness requirement: each processor must move at least once.
# Minimum: 5 moves (one per processor). But binary processors need
# to return to their initial state, so they need even numbers of moves.
# P0: ≥2 moves, P1: ≥2 moves, P2: ≥2 moves, P3: ≥1 move, P4: ≥1 move.
# But P3 and P4 also need to return to their initial states.
# Minimum cycle: probably around 10-12.

# Actually, let me check what the n=5 witness's cycle length would be
# if we tried to minimize it for ms=(2,2,2,3,3).
# In the witness (2,2,2,3,4): cycle length 18.
# For (2,2,2,3,3): unknown (product 72 is dead, no valid cycle exists).

# Let me instead prove the impossibility directly.

# ============================================================
# Step 3: THE PROOF
#
# Consider any valid system with ms = (2,2,2,3,3).
# The good cycle C visits all 5 processors.
#
# The binary block P0-P1-P2 has 8 configurations.
# The non-binary section P3-P4 has 9 configurations.
# Total: 72 configurations.
#
# In the good cycle, the binary block must traverse ≥ 6 distinct
# states (partial Gray code: 000,100,110,111,011,001).
#
# At each cycle position, the FULL configuration (b0,b1,b2,s3,s4)
# is distinct. The binary block's state (b0,b1,b2) determines
# the "macro-phase."
#
# The non-binary section (s3,s4) must vary to ensure:
# 1. Mutual exclusion (exactly 1 privileged processor)
# 2. Correct routing (token goes to the right processor next)
# 3. No bad cycles
#
# The KEY constraint comes from considering what happens when
# the binary block is in the SAME state at two different cycle
# positions but the non-binary section MUST be in different states.
#
# Binary block visits states:
# 000 → 100 → 110 → 111 → 011 → 001 → ...
#
# The block passes through state (1,1,1) after the rightward sweep
# and through state (0,0,0) after the leftward sweep.
# Between these, it passes through intermediate states.
#
# CRITICAL: The binary block returns to state (0,0,0) at the END
# of the cycle. But at the START of the cycle, it's also in (0,0,0).
# So the binary block is in state (0,0,0) at two positions.
# Similarly for other repeated states.
#
# At position t1: config = (0,0,0, s3_1, s4_1)
# At position t2: config = (0,0,0, s3_2, s4_2) (later in cycle)
# These must be DIFFERENT configs, so (s3_1,s4_1) ≠ (s3_2,s4_2).
#
# But more importantly: the PRIVILEGE structure at t1 and t2 must
# be different (different processors move, or different next states).
# ============================================================

# Let me now count how many times the binary block can be in each
# state during the good cycle, and what constraints this places
# on the non-binary section.

# In the n=5 witness (ms=(2,2,2,3,4)), binary block states:
gc_5 = [(0,0,0,0,0),(1,0,0,0,0),(1,1,0,0,0),(1,1,1,0,0),(1,1,1,1,0),(1,1,1,1,1),
        (0,1,1,1,1),(0,0,1,1,1),(0,0,0,1,1),(0,0,0,2,1),(0,0,1,2,1),(0,0,1,0,1),
        (0,0,1,0,2),(0,0,1,2,2),(0,0,1,2,3),(0,0,1,1,3),(0,0,0,1,3),(0,0,0,0,3)]

from collections import Counter
binary_states = [c[:3] for c in gc_5]
binary_count = Counter(binary_states)

print("\nBinary block state occupancy in n=5 witness (ms=(2,2,2,3,4)):")
for bs in sorted(binary_count, key=lambda x: binary_count[x], reverse=True):
    positions = [i for i, b in enumerate(binary_states) if b == bs]
    nb_states = [(gc_5[i][3], gc_5[i][4]) for i in positions]
    print(f"  {bs}: {binary_count[bs]} times, at steps {positions}")
    print(f"    non-binary states: {nb_states}")

print(f"\nTotal binary block states used: {len(binary_count)}")
print(f"Binary block states repeated: {sum(1 for k,v in binary_count.items() if v > 1)}")

# Count how many DISTINCT non-binary states are needed when
# the binary block is in a repeated state
print("\n" + "="*70)
print("REPEATED BINARY STATES → NON-BINARY STATE REQUIREMENTS")
print("="*70)

for bs in sorted(binary_count):
    if binary_count[bs] > 1:
        positions = [i for i, b in enumerate(binary_states) if b == bs]
        nb_states = [(gc_5[i][3], gc_5[i][4]) for i in positions]
        nb_distinct = len(set(nb_states))
        print(f"\n  Binary block = {bs}: appears {binary_count[bs]} times")
        print(f"    Non-binary states needed: {nb_distinct} distinct out of {len(nb_states)}")
        for pos, nb in zip(positions, nb_states):
            print(f"      step {pos}: (P3,P4) = {nb}")

# ============================================================
# Step 4: THE PIGEONHOLE ARGUMENT
#
# If the binary block state (0,0,0) appears k times in the cycle,
# then the non-binary section must be in k DISTINCT states at
# those positions (otherwise two cycle positions would be identical).
#
# With non-binary section having 9 possible states (3×3),
# the binary block can appear in state (0,0,0) at most 9 times.
#
# But the constraint is tighter: the non-binary states must also
# support valid TRANSITIONS between them.
# ============================================================

print("\n" + "="*70)
print("THE TIGHT CONSTRAINT: TRANSITION COMPATIBILITY")
print("="*70)

print("""
In the n=5 witness, binary block state (0,0,0) appears 4 times:
  step 0: (P3,P4) = (0,0)  →  P0 moves  →  binary becomes (1,0,0)
  step 8: (P3,P4) = (1,1)  →  P3 moves  →  binary stays (0,0,0)
  step 16: (P3,P4) = (1,3) →  P3 moves  →  binary stays (0,0,0)
  step 17: (P3,P4) = (0,3) →  P4 moves  →  binary stays (0,0,0)

And (0,0,1) appears 6 times, (1,1,1) appears 3 times, etc.

For a pure {2,3} system (P4 has 3 states instead of 4):
  Binary state (0,0,0) needs 4 distinct (P3,P4) pairs.
  With P4 ∈ {0,1,2}, there are 9 possible pairs. 4 ≤ 9: OK in principle.

But here's the tight constraint:

Binary state (0,0,1) appears 6 times, needing 6 distinct (P3,P4) pairs.
  9 ≥ 6: OK.

However, the TRANSITIONS between these states are constrained:
- From (0,0,0, s3, s4), the next config must have exactly one
  privileged processor. The privilege depends on (s3, s4).
- The transition must lead to a valid next config with no collision.

Let me count the TOTAL number of distinct (P3,P4) pairs used
in the witness cycle:
""")

nb_pairs = [(c[3], c[4]) for c in gc_5]
print(f"Total cycle length: {len(gc_5)}")
print(f"Distinct (P3,P4) pairs used: {len(set(nb_pairs))}")
print(f"Available (P3,P4) pairs with P4∈{{0,1,2,3}}: {3*4} = 12")
print(f"Available (P3,P4) pairs with P4∈{{0,1,2}}: {3*3} = 9")
print(f"Shortfall: {len(set(nb_pairs))} needed, only 9 available with ternary P4")

if len(set(nb_pairs)) > 9:
    print(f"\n  DIRECT PROOF: {len(set(nb_pairs))} > 9 distinct pairs needed,")
    print(f"  but only 9 available with ternary P4.")
    print(f"  Therefore, no valid good cycle exists for ms=(2,2,2,3,3)")
    print(f"  that has the same binary-block sweep structure as the witness.")

# ============================================================
# Step 5: IS THIS PROOF GENERAL?
#
# The above argument shows that the SPECIFIC cycle structure
# of the n=5 witness requires 10 distinct (P3,P4) pairs,
# which exceeds 9. But a different cycle structure might need fewer.
#
# HOWEVER: the constraint is more fundamental than the specific
# witness. ANY valid cycle for n=5 must:
# 1. Visit all 5 processors (fairness)
# 2. Have the binary block return to its initial state
# 3. Have the non-binary section return to its initial state
# 4. Maintain mutual exclusion (exactly 1 privileged per step)
# 5. Ensure convergence (no bad cycles)
#
# The question is: can a different cycle structure use fewer
# than 10 distinct non-binary pairs?
#
# Let me check by looking at the minimum number of times
# each binary block state MUST appear.
# ============================================================

print("\n" + "="*70)
print("MINIMUM BINARY BLOCK STATE REPETITIONS")
print("="*70)

print("""
The binary block P0-P1-P2 must visit ≥6 states (partial Gray code).
Starting from (0,0,0):

Rightward sweep: (0,0,0)→(1,0,0)→(1,1,0)→(1,1,1) [3 binary moves]
Leftward sweep:  (1,1,1)→(0,1,1)→(0,0,1)→(0,0,0) [3 binary moves]

But the cycle must also include NON-BINARY moves (P3, P4 must move).
When P3 or P4 moves, the binary block state DOESN'T change.
So the binary block state is REPEATED at those steps.

Minimum P3 moves: P3 has 3 states and must return to initial.
  Minimum: 3 moves (cycle through 0→1→2→0) or 2 moves (0→1→0).
  Actually, minimum is 2 moves if P3 only uses 2 states,
  but fairness requires P3 to move at least once, and it
  must return, so minimum 2 moves.

Minimum P4 moves: similarly, minimum 2 moves.

So minimum cycle length: 6 (binary) + 2 (P3) + 2 (P4) = 10.

At minimum cycle length 10:
  Binary block states: 6 distinct, appearing 10 times total.
  So 4 binary states are repeated (appearing 2+ times).
  Each repetition needs a distinct (P3,P4) pair.

With 9 available pairs and 10 cycle positions:
  By pigeonhole, at least two positions share a (P3,P4) pair.
  If these two positions also share a binary block state,
  they have IDENTICAL full configurations → cycle collision!

Does this happen?
""")

# Count: with 6 binary states in 10 positions, how are they distributed?
# Minimum repetition: 4 states appear once, 2 states appear 3 times each?
# No: 6 states, 10 positions. By pigeonhole, at least 10-6=4 repetitions.
# Most compressed: 2 states appear 3 times, 4 appear once. Total = 6+4 = 10. ✓
# Or: 4 states appear twice, 2 appear once. Total = 8+2 = 10. ✓

print("Distribution of 6 binary states across 10 positions:")
print("  Most compressed: each of 4 states appears 1 time, 2 states appear 3 times")
print("  → at the 10 positions, (P3,P4) must have 10 distinct values")
print("  → but only 9 available! CONTRADICTION!")
print()
print("Wait — (P3,P4) values need not be globally distinct.")
print("They need to be distinct WITHIN each binary block state group.")
print()
print("Revised argument:")
print("  Binary state X appears k times → needs k distinct (P3,P4) pairs for X")
print("  Different binary states can reuse (P3,P4) pairs")
print()
print("  So the constraint is: max_X (count of X) ≤ 9")
print("  Since no single binary state needs to appear 10+ times, this doesn't")
print("  immediately give a contradiction.")

# ============================================================
# Step 6: THE CORRECT ARGUMENT — TRANSITION CONSTRAINTS
#
# The simple counting argument doesn't work because different
# binary states can reuse (P3,P4) pairs. We need the TRANSITION
# constraints.
#
# When P3 moves, the binary block doesn't change. So:
#   Config (b, s3, s4) → Config (b, s3', s4) where s3' = f3(b2, s3, s4)
#
# This means: from binary state b with (P3,P4) = (s3, s4),
# P3's move produces (s3', s4) with the SAME binary state.
# If both (s3, s4) and (s3', s4) appear in the cycle with binary
# state b, they must be different → s3 ≠ s3'. Obviously true.
#
# But the deeper constraint: the SEQUENCE of (P3,P4) values
# within each binary state group must form a valid sub-path
# of the functional graph on {0,...,8} (the 9 possible pairs).
#
# Let me trace the functional graph for P3's transitions.
# ============================================================

print("\n" + "="*70)
print("THE FUNCTIONAL GRAPH ARGUMENT")
print("="*70)

# In the n=5 witness, let's trace what happens when the binary
# block is in state (0,0,1) — which appears 6 times.
print("\nBinary state (0,0,1) in n=5 witness:")
for idx, c in enumerate(gc_5):
    if c[:3] == (0, 0, 1):
        nb = (c[3], c[4])
        # Who moves next?
        c_next = gc_5[(idx+1) % len(gc_5)]
        for j in range(5):
            if c[j] != c_next[j]:
                mover = j
                break
        print(f"  step {idx}: (P3,P4)={nb} → P{mover} moves → {c_next[:3]},{c_next[3:]}")

print("""
With binary state (0,0,1):
  6 positions use 6 distinct (P3,P4) pairs: (1,1), (2,1), (0,1), (0,2), (2,2), (1,3)
  With ternary P4, only 9 pairs available; 6 ≤ 9, so fits.

But the transitions between these pairs are constrained:
  (1,1) → P2 moves → binary changes to (0,0,0)
  (2,1) → P3 moves → (P3,P4) changes to (0,1), binary stays (0,0,1)
  (0,1) → P4 moves → (P3,P4) changes to (0,2), binary stays (0,0,1)
  (0,2) → P3 moves → (P3,P4) changes to (2,2), binary stays (0,0,1)
  (2,2) → P4 moves → (P3,P4) changes to (2,3), binary stays (0,0,1)
  (1,3) → P2 moves → binary changes to (0,0,0)

The (P3,P4) chain within binary state (0,0,1):
  ... → (2,1) → (0,1) → (0,2) → (2,2) → (2,3) → ...

Note (2,3) uses P4 state 3 — which doesn't exist in a ternary P4!
This is one of the points where the quaternary is needed.

For a ternary P4, the chain must use only P4 ∈ {0,1,2}.
The chain needs 4 consecutive (P3,P4) transitions within binary
state (0,0,1). With P3 ∈ {0,1,2} and P4 ∈ {0,1,2}, the chain
must visit 4 distinct pairs... but each P3 transition goes from
s3 to f3(0, s3, r4) (since binary block is (0,0,1), so L for P3
is P2's state = b2 = 1... wait, let me get the indexing right.

P3's left neighbor is P2. Binary block is (b0, b1, b2) = (0, 0, 1).
So P3 sees L = b2 = 1.
P3's right neighbor is P4, so R = P4's state.
When P3 moves: f3(1, s3, s4) determines new s3.

P4's left neighbor is P3, right neighbor is P0.
P4 sees L = s3, R = b0 = 0.
When P4 moves: f4(s3, s4, 0) determines new s4.

So within binary state (0,0,1):
  P3 transitions: f3(1, s3, s4) [L=1 fixed]
  P4 transitions: f4(s3, s4, 0) [R=0 fixed]

The chain of (s3, s4) values is determined by alternating
P3 and P4 moves, with L=1 for P3 and R=0 for P4.
""")

# ============================================================
# Step 7: THE FORMAL IMPOSSIBILITY
#
# Within binary state (0,0,1), the token bounces between P3 and P4.
# Each bounce changes one of (s3, s4).
#
# The chain must visit enough distinct (s3, s4) pairs to allow
# the token to eventually exit (return to the binary block).
#
# With ternary P3 and P4: 9 pairs available.
# With quaternary P4: 12 pairs available.
#
# The constraint is: the chain must form a valid path in the
# transition graph of the (s3,s4) subsystem, AND the chain
# must include configurations where:
# - P3 is privileged but the next mover is P2 (token returns to binary block)
# - P4 is privileged but the next mover is P0 (token wraps around)
#
# For the token to EXIT the non-binary section, P3 must make P2
# privileged (by changing s3 to something that makes P2 see a
# changed right neighbor). Similarly, P4 must make P0 privileged.
#
# The KEY: for the token to re-enter the binary block in the
# CORRECT DIRECTION, the (s3, s4) state must encode which
# direction the re-entry should go. This is the routing memory.
#
# With ternary P4, the routing memory has ≤ 3 values.
# But 4 distinct routing situations arise (as shown by the witness).
# Therefore, 3 values are insufficient.
# ============================================================

print("\n" + "="*70)
print("ROUTING SITUATIONS ANALYSIS")
print("="*70)

# In the n=5 witness, when does the token EXIT the non-binary section?
# This happens when P3 moves and the next mover is P2, or when
# P4 moves and the next mover is P0.

gc = gc_5
movers = []
for idx in range(len(gc)):
    c = gc[idx]
    c_next = gc[(idx+1) % len(gc)]
    for j in range(5):
        if c[j] != c_next[j]:
            movers.append(j)
            break

print("\nExit points from non-binary section:")
for idx in range(len(gc)):
    if movers[idx] in [3, 4]:
        next_mover = movers[(idx+1) % len(gc)]
        if next_mover in [0, 1, 2]:
            c = gc[idx]
            if movers[idx] == 3:
                L, S, R = c[2], c[3], c[4]
                print(f"  step {idx}: P3({L},{S},{R}) → P{next_mover} "
                      f"(P3 exits to binary, P4_state={R})")
            else:
                L, S, R = c[3], c[4], c[0]
                print(f"  step {idx}: P4({L},{S},{R}) → P{next_mover} "
                      f"(P4 exits to binary, P3_state={L})")

print("""
EXIT POINTS (token leaves non-binary section, enters binary block):
  step 3:  P3(1,0,0)→1 → P4 moves. Wait, P4 is not binary...

Let me re-examine. The token exits the non-binary section when:
- A non-binary processor moves AND the next mover is binary.
""")

print("\nAll transitions between non-binary and binary movers:")
for idx in range(len(gc)):
    curr_nb = movers[idx] in [3, 4]
    next_nb = movers[(idx+1) % len(gc)] in [3, 4]
    if curr_nb != next_nb:
        c = gc[idx]
        direction = "NB→B" if curr_nb else "B→NB"
        print(f"  step {idx}: P{movers[idx]} → P{movers[(idx+1)%len(gc)]}  [{direction}]  "
              f"config={c}")

print("\n" + "="*70)
print("ROUTING DECISION COUNT")
print("="*70)

# How many DISTINCT transitions from non-binary to binary exist?
nb_to_b = []
for idx in range(len(gc)):
    if movers[idx] in [3, 4] and movers[(idx+1) % len(gc)] in [0, 1, 2]:
        c = gc[idx]
        nb_state = (c[3], c[4])
        binary_target = movers[(idx+1) % len(gc)]
        nb_to_b.append((idx, nb_state, binary_target, c[:3]))

print(f"\nNon-binary → binary transitions: {len(nb_to_b)}")
for (idx, nb, target, bstate) in nb_to_b:
    print(f"  step {idx}: (P3,P4)={nb}, binary={bstate} → P{target} moves next")

# Count distinct (nb_state, routing_decision) pairs
routing_decisions = set()
for (idx, nb, target, bstate) in nb_to_b:
    routing_decisions.add((nb, target))
print(f"\nDistinct (non-binary state, target) pairs: {len(routing_decisions)}")
for (nb, target) in sorted(routing_decisions):
    print(f"  (P3,P4)={nb} → route to P{target}")

# How many distinct P4 states are used in these routing decisions?
p4_at_exit = set()
for (idx, nb, target, bstate) in nb_to_b:
    p4_at_exit.add(nb[1])
print(f"\nP4 states at exit points: {sorted(p4_at_exit)}")
print(f"Number of distinct P4 states at exits: {len(p4_at_exit)}")
if len(p4_at_exit) > 3:
    print(f"\n  *** {len(p4_at_exit)} > 3: CANNOT FIT IN TERNARY P4! ***")
    print(f"  The token exits the non-binary section with P4 in {len(p4_at_exit)} distinct states.")
    print(f"  A ternary P4 has only 3 states → at least two exits would collide.")
