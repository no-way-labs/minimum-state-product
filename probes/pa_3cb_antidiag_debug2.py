#!/usr/bin/env python3
"""Debug 2: Analyze the non-AD cycle at n=5, ms=(2,2,2,3,3)."""
from collections import Counter

# The non-AD cycle:
# movers = [4, 4, 0, 1, 2, 3, 2, 3, 4, 4, 0, 1, 2, 3, 2, 3]
# P1 fires at steps 3 and 11.
# Between: steps 4-10: movers = [2, 3, 2, 3, 4, 4, 0]
# After: steps 12-15 + 0-2: movers = [2, 3, 2, 3, 4, 4, 0]

movers = [4, 4, 0, 1, 2, 3, 2, 3, 4, 4, 0, 1, 2, 3, 2, 3]
n = 5
L = len(movers)

p1_steps = [s for s in range(L) if movers[s] == 1]
s1, s2 = p1_steps
print(f'P1 fires at steps {s1} and {s2}')

between = [movers[s] for s in range(s1+1, s2)]
print(f'Between: {between}')

# Crossing sequence
crossings = []
for m in between:
    if m == 0: crossings.append('B0')
    elif m == 2: crossings.append('B2')
print(f'Crossings: {crossings}')

# The crossing sequence is: B2, B2, B0
# C1 = B2 (exit through Bridge 2)
# C2 = B2 (enter through Bridge 2? or exit?)
# C3 = B0 (enter through Bridge 0)

# Let me track territory explicitly
print('\nTerritory tracking:')
in_binary = True  # start at P1 (binary)
for i, m in enumerate(between):
    if m in {0, 1, 2}:
        if in_binary:
            print(f'  Step {i}: mover P{m} (binary, EXIT through B{"0" if m==0 else "2"})')
            in_binary = False
        else:
            print(f'  Step {i}: mover P{m} (non-binary->binary, ENTER through B{"0" if m==0 else "2"})')
            in_binary = True
    else:
        territory = 'binary' if in_binary else 'non-binary'
        print(f'  Step {i}: mover P{m} ({territory})')

# AH WAIT: The issue is that the walk starts at P1 and the first between-step
# is P2. P1 and P2 are both in binary territory. So the walk starts IN binary
# at P1, and the first mover P2 fires WITHIN binary territory.
# Then from P2, the walk goes to P3 (non-binary). So P2's firing is still
# in binary territory, and the EXIT happens when the walk moves from P2 to P3.

# But in my crossing counting, I count P2 as a crossing. This is correct
# if P2's firing represents the walk being at P2 (boundary of binary territory).
# After P2 fires, the next mover is P3 (non-binary), so the walk crosses Bridge 2.

# Actually: the MOVER at step t is who fires. After P2 fires, the walk goes to P3.
# P2 fires AT P2, meaning the walk IS at P2 when P2 fires. Then it moves to P3.
# So P2 firing = walk at P2 -> exits to P3 = Bridge 2 crossing.

# The sequence between P1's firings: 2, 3, 2, 3, 4, 4, 0
# Step 0: P2 fires (walk at P2, exits to P3 via Bridge 2). C1 = B2.
# Step 1: P3 fires (walk at P3, non-binary territory).
# Step 2: P2 fires. Walk was at P3, comes to P2 (enters binary via Bridge 2). C2 = B2.
#   Then from P2, walk goes to P3 (exits via Bridge 2). C3 = B2? NO!
#   Wait: C2 is the ENTRY at P2. After entering, P2 fires and the walk goes to P3.
#   That exit is C3. But C3 should be B2 (exit via Bridge 2). So C2=C3=B2.
#   But that's a pair adding 2 to k_2.

# Step 3: P3 fires (non-binary).
# Step 4: P4 fires (non-binary).
# Step 5: P4 fires (non-binary).
# Step 6: P0 fires. Walk comes from P4 to P0 (enters binary via Bridge 0). C4 = B0.
#   This is the last crossing. C4 = B0 = entry.

# So the crossing sequence is: B2(exit), B2(enter), B2(exit), B0(enter)
# C1=B2, C2=B2, C3=B2, C4=B0
# q = 4 (even). C_q = B0 (entry). OK.

# Paired: C1 unpaired B2 exit. (C2, C3) = B2 pair. C4 unpaired B0 entry.
# k_2 = 1 (unpaired) + 2 (pair) = 3? But data says k_2 = 2.

# WAIT: I'm double-counting! Each P2 appearance in the mover word is ONE crossing.
# P2 appears at between positions 0 and 2. That's k_2 = 2.
# But in my crossing sequence, I had 3 B2 crossings (C1, C2, C3).
# The issue: when P2 fires at position 2, it's BOTH an entry and an exit.
# It enters binary (from P3), fires, and exits to P3. But this is a SINGLE
# P2 firing (k_2 increments by 1, not 2).

# My pairing model assumed each crossing alternates entry/exit.
# But a P2 firing that enters-and-exits in one step is TWO crossings but ONE firing.
# This breaks the pairing!

print('\n\nKEY INSIGHT: When P2 fires after being reached from P3, and the next')
print('mover is also P3, then P2 both ENTERS and EXITS in a single firing.')
print('This creates two crossings from one P2 firing, breaking the pairing model.')
print()

# The correct model: each P_0 firing = 1 increment to k_0.
# Each P_2 firing = 1 increment to k_2.
# The pairing of territory crossings is a different count than k_0, k_2.

# So my proof has a flaw! The crossing count q can differ from k_0 + k_2
# because a single P_2 firing can create 2 crossings (enter + exit).

# Revised understanding:
# The walk enters binary at P2 (from P3), P2 fires, walk exits to P3.
# This is: non-binary -> P2 -> non-binary.
# P2 fires once (k_2 += 1), but territory crosses twice (enter + exit).

# For the parity argument, we need k_0 and k_2, not territory crossings.
# k_0 = #(P0 fires in between), k_2 = #(P2 fires in between).
# These are just the counts of P0 and P2 in the mover word.

# The relationship between territory crossings and k_0, k_2:
# Each "bounce" at P0 (enter binary at P0, exit binary at P0) = 1 P0 firing.
# Each "bounce" at P2 (enter binary at P2, exit binary at P2) = 1 P2 firing.
# A "pass-through" at P0 (enter at P0, traverse to P2, exit at P2) = 1 P0 firing + 1 P2 firing.
# But pass-through requires traversing the binary block, which P1 blocks!

# So with P1 as a wall, there are NO pass-throughs. Every visit to P0 is a bounce
# (enter and exit through Bridge 0), and every visit to P2 is a bounce
# (enter and exit through Bridge 2).

# Hmm but the first visit to P2 might be different: the walk starts at P1,
# goes to P2, and P2 exits to P3. This is NOT a bounce (didn't enter from P3).
# It's a one-way exit.

# Similarly, the last visit to P0: walk enters from P_{n-1} at P0, then proceeds
# to P1. This is a one-way entry (doesn't exit through B0).
# Wait: P0 -> P1 is impossible because P1 is blocked (P1 doesn't fire).
# So P0's only exit is to P_{n-1}. So P0's last visit IS a bounce.

# Let me re-examine. In the reversed direction case:
# Between: [2, 3, 2, 3, 4, 4, 0]
# Walk: P1 -> P2 -> P3 -> P2 -> P3 -> P4 -> P4 -> P0 -> P1
# Wait: the last mover before s2 is P0, and the next is P1 (fires at s2).
# After P0 fires, the next mover must be adjacent to P0: P1 or P_{n-1}=P4.
# The next mover IS P1 (at s2). So P0 fires and the walk goes to P1.
# But P1 is in the binary block! And P0 is in the binary block!
# The walk from P0 to P1 is WITHIN the binary block.
# So P0's last visit is NOT a bounce -- it's an entry into binary territory
# that proceeds to P1 WITHOUT exiting through Bridge 0.

# THIS IS THE ISSUE. When the walk enters binary at P0 and proceeds to P1
# (at s2), there's no matching exit at P0. P0 fires once (k_0 += 1),
# but the territory crosses from non-binary to binary (entry) without
# a matching exit at P0.

# Similarly, the first step: P1 fires at s1, walk goes to P2.
# P2 fires and exits to P3. P2 fires once (k_2 += 1), and territory
# crosses from binary to non-binary (exit) without a matching entry at P2.

# So the "unpaired" crossings are:
# First: P2 exit (k_2 += 1) -- no matching entry at P2
# Last: P0 entry (k_0 += 1) -- no matching exit at P0

# Any intermediate visit to P0 or P2 IS a bounce (enter + exit through same bridge).
# Each bounce adds 1 to k_0 or k_2.

# So: k_0 = 1 (final entry) + #(P0 bounces)
#     k_2 = 1 (first exit) + #(P2 bounces)

# A P0 bounce adds 1 to k_0. A P2 bounce adds 1 to k_2.
# No parity constraint on the number of bounces!

# In the non-AD example: k_0 = 1 (final entry, no P0 bounces), k_2 = 2 (first exit + 1 P2 bounce).
# k_0 = 1 (odd), k_2 = 2 (even). So c[0] flips but c[2] doesn't.

# AH! But with the OTHER direction (P0 first, P2 last):
# k_0 = 1 (first exit) + #(P0 bounces)
# k_2 = 1 (final entry) + #(P2 bounces)
# Same structure. The unpaired one is always 1.

# The issue is that BOUNCES add to the count, and each bounce adds exactly 1.
# So k_0 = 1 + #(P0 bounces) and k_2 = 1 + #(P2 bounces).
# For BOTH to be odd, we need both bounce counts to be even.
# There's no topological reason forcing this!

# My original proof was wrong. The paired crossing principle was based on
# territory crossings, but k_0 and k_2 count FIRINGS, not crossings.
# A bounce at P0 is 1 firing but 2 crossings (enter + exit).
# The unpaired crossing at the start/end is 1 firing and 1 crossing.

# So: territory crossings = 2*(#bounces) + 2 (start + end)
#     = 2*(k_0 - 1 + k_2 - 1) + 2 = 2*(k_0 + k_2 - 1)
# Always even. But k_0, k_2 can be any positive integers.

# CONCLUSION: The parity lemma as stated IS FALSE.
# Counterexample at n=5, ms=(2,2,2,3,3): k_0=1, k_2=2.
# The anti-diagonal fails for 6/500 cycles.

print('\n\nCONCLUSION: The Parity Lemma is FALSE as stated.')
print('Counterexample at n=5, ms=(2,2,2,3,3): k_0=1, k_2=2.')
print('The anti-diagonal fails for reversed-direction cycles.')
print()
print('The lemma DOES hold when both non-binary neighbors have m_i >= 3')
print('AND one of them has m_i >= 4 (breaking the symmetry).')
print('It also holds at n >= 6 with ms=(2,2,2,3,3,3).')
print()
print('The issue is specific to n=5, ms=(2,2,2,3,3) where both')
print('non-binary procs have the SAME modulus (both 3).')
