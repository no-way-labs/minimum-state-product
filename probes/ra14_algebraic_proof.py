#!/usr/bin/env python3
"""
ra14_algebraic_proof.py — Algebraic proof of EC for odd-winding non-uniform
words with non-consecutive binary.

=== PROOF STRUCTURE ===

The proof decomposes into cases by fire count parity:

CASE 1 (Parity obstruction): When B (sum of ternary multipliers) has
opposite parity to n, CL + n is odd, making winding +-n impossible.
This case is vacuously true.

For CASE 1 to be the ONLY case (making the theorem vacuously true for all fc):
Need: ALL valid fc have B with opposite parity to n.
B = sum of k_p over ternary procs, each k_p >= 1.
Number of ternary procs = T = n - 3.

B_min = T = n - 3. Parity of B_min: (n-3) mod 2.
n and n-3 have the same parity iff 3 is even: never.
So B_min always has OPPOSITE parity to n. CASE 1 applies to minimum fc.

For non-minimum fc: can B have same parity as n?
B = sum of k_p where each k_p >= 1. B ranges from T to infinity.
B can be T, T+1, T+2, ... (by incrementing individual k_p).
So B can take ANY value >= T.

If T is even (n odd): B_min = T even. n odd. OPPOSITE.
B_min+1 = T+1 odd. Same as n. So YES, B can match n's parity.
But requires at least one k_p >= 2.

If T is odd (n even): B_min = T odd. n even. OPPOSITE.
B_min+1 = T+1 even. Same as n. YES.

So in both cases, non-minimum fc CAN have B with matching parity.

BUT: the Lean sorry is specifically for the case where binary p has
ISOLATED firings. What constraint does "isolated" place on fc?

ISOLATED FIRINGS for binary p: no two consecutive steps fire p.
In the mover word, p never appears twice in a row.
This means: between any two fires of p, at least one other processor fires.

For binary p with fc[p] = 2: p fires at steps s1 and s2.
Isolated: s2 > s1 + 1 and (s1 > 0 or s2 < CL - 1 for the wrap).
Wait, more precisely: word[s1]=p, word[(s1+1)%CL] != p (for all s1 where word[s1]=p).

This is about the ORDERING of fires in the word, not just about fc.
For fc[p] = 2: the two fires of p are separated by at least 1 step.
This is almost always true except for "burst" patterns.

Given fc[p] = 2 and isolated: the walk visits p twice, with non-p steps between.
The walk enters p from one neighbor and exits to the other (or same).

=== KEY REALIZATION ===

The Lean proof structure is:
1. For binary p with fc >= 2: either EC, permanent, or isolated.
2. Permanent contradicts odd winding.
3. Isolated: THIS is the sorry.

But does "isolated" even COMBINE with valid odd winding?

For fc = ms (minimum): winding is impossible by parity.
For non-minimum fc: winding is possible.
With non-minimum fc: the binary STILL has fc[p] = 2 (unchanged).
A ternary was incremented.

So the question is: with fc[p] = 2, isolated, and the walk having winding +-1
per edge, does EC hold?

=== PARITY + EDGE COUNT APPROACH ===

Actually, I realize the key insight might be even simpler.

In the Lean proof, the hypothesis `isOddWinding` means |totalDisplacement| = n.
And `converges sys gc` means the system converges.

But: a converging system has `gc.configs.length` equal to the number of configs
in the good cycle. The fire count `gc.fireCount p` is the number of steps where
p is the mover.

The fire count must be a multiple of ms[p] because the state at p must return
to its starting value after a full cycle.

NOW: the walk is the sequence of movers. Each mover is the position of the token.
The token moves +-1 at each step. So consecutive movers differ by +-1 mod n.

totalDisplacement = sum of signed steps (each +-1).
isOddWinding: |totalDisplacement| = n.

For totalDisplacement = +n: CW = (CL + n)/2, CCW = (CL - n)/2.
Both must be non-negative integers.
CL >= n. CL + n must be even.

CL = sum(fc[p]) = sum(k_p * ms[p]) = 2A + 3B.
CL + n = 2A + 3B + n.

For n >= 9 (the Lean condition): need 2A + 3B + n even.

=== THE ACTUAL PROOF ===

Wait. Let me re-examine the Lean code. The sorry at line 601 is:
```
· -- Non-consecutive isolated odd-winding: structural prefix-residue EC (RA13 verified 11555/11555)
  sorry -- non-consecutive isolated odd-winding: structural prefix-residue EC (RA13)
```

And the context is: gc is a good cycle with odd winding, non-adjacent binary pair
(p, q) both binary and not adjacent, both have isolated firings with fc >= 2.

The proof path should show: under these conditions, the mover word has
structural entry conflict.

Given what I've discovered: the parity argument shows that for MOST fc,
the walk can't have odd winding. For the remaining fc, CL > 18, and we
need a cross-type pigeonhole argument.

Let me try to prove the CROSS-TYPE collision.
"""

print("=== CROSS-TYPE COLLISION ANALYSIS ===")
print()
print("At binary p (non-consecutive), ms[p]=2, neighbors ternary (ms=3).")
print("Residue space = 3*2*3 = 18.")
print()

# The key constraint: pfc_p mod 2 partitions steps into parity-0 and parity-1.
# Mover steps for p: fc[p] = 2 steps. pfc_p = 0 at first fire, 1 at second.
# So one mover at parity-0, one at parity-1.
#
# Non-mover steps: CL - 2 steps. Distributed between parity 0 and 1.
# Between fires: parity-1 segment. Before first fire + after second fire: parity-0 segment.
# (Since fc[p] = 2, pfc goes 0..0,1..1,0(=2 mod 2)..0)
#
# At parity-0 mover: (pfc_L mod 3, 0, pfc_R mod 3).
# At parity-0 non-movers: same format, space = 3*1*3 = 9.
# At parity-1 mover: (pfc_L mod 3, 1, pfc_R mod 3).
# At parity-1 non-movers: same, space = 9.
#
# For EC at parity-0: mover pair (a, c) must appear among non-mover pairs at parity-0.
# For EC at parity-1: mover pair (b, d) must appear among non-mover pairs at parity-1.
#
# Non-mover at parity-0: all steps before first fire + after second fire.
# Non-mover at parity-1: all steps between first and second fire.
#
# ISOLATED binary: no consecutive p-fires. So between the two fires:
# at least 1 non-p step. This means the parity-1 segment has >= 1 non-mover step.
#
# How many non-mover steps at each parity?
# Let s1 be first fire position, s2 be second fire position.
# Parity-1 non-movers: positions s1+1, s1+2, ..., s2-1 (all between fires, none are p).
# Count = s2 - s1 - 1 >= 1 (isolated).
# Parity-0 non-movers: positions 0,..,s1-1 and s2+1,..,CL-1 (wrapping).
# Count = CL - 2 - (s2 - s1 - 1) = CL - s2 + s1 - 1.
#
# For the parity-0 space (size 9):
# Need CL - s2 + s1 - 1 non-mover steps, 1 mover step.
# If the non-mover steps cover all 9 pairs: the mover pair MUST be covered. EC.
# But non-movers might not cover all 9.

# For the parity-1 space (size 9):
# Need s2 - s1 - 1 non-mover steps, 1 mover step.
# If non-movers cover all 9: EC.

# The TOTAL non-movers = CL - 2. Distributed between parity-0 and parity-1.
# The distribution depends on s1, s2.
# Sum = (CL - s2 + s1 - 1) + (s2 - s1 - 1) = CL - 2. CHECK.

# For CL >= 21 (n >= 7 with non-min fc):
# CL - 2 >= 19 total non-movers, split between two spaces of size 9 each.
# By pigeonhole: one space gets at least ceil(19/2) = 10 non-movers.
# 10 non-movers in a 9-space: at least 2 share a pair (but could be non-mover-non-mover).
# Distinct non-mover pairs in that space: at most 9. But we want >= 9 to force EC.
# 10 non-movers in 9 slots: all 9 slots covered. So mover's pair MUST be among them!

# WAIT! 10 non-mover steps in a 9-element space means each step maps to a pair.
# 10 steps, 9 distinct pairs possible. By pigeonhole, some pair is hit twice.
# But ALL 9 pairs might not be covered (one pair gets 2 hits, 8 get 1 each, 1 gets 0).
# So 10 steps doesn't guarantee full coverage!

# For full coverage: need >= 9 DISTINCT pairs among the non-movers.
# 10 steps can give 9 distinct if one is repeated.
# But 10 steps COULD give as few as 1 distinct (all same pair).

# So this approach doesn't work directly. We need more structure.

# NEW APPROACH: Look at the walks available in the parity-0/1 segments.
# The pfc_L changes by 1 each time the walk visits L. Similarly for R.
# Between specific steps, pfc_L and pfc_R change by specific amounts.

# Actually: in the parity-0 segment (before first p-fire and after second p-fire):
# pfc_p is constant (0 mod 2). pfc_L and pfc_R evolve as the walk proceeds.
# The walk is on the ring, visiting positions. In the parity-0 segment,
# the walk visits various positions, and pfc_L, pfc_R increment when
# L or R are visited.

# The pair (pfc_L mod 3, pfc_R mod 3) traces a path in Z_3 x Z_3.
# The path changes when L or R is visited.
# In a CW step past L: pfc_L increments.
# In a CCW step past R: pfc_R increments.

# The walk structure constrains which (pfc_L, pfc_R) pairs are reachable.

# For parity-0 segment: this includes the "wrap-around" (after last fire + before first fire).
# The mover at parity-0 is the FIRST fire of p. Its pair is (pfc_L(s1) mod 3, pfc_R(s1) mod 3).
# The non-movers before s1 have pairs that trace from (0,0) to (pfc_L(s1), pfc_R(s1)).
# The non-movers after s2 trace from (pfc_L(s2+1), pfc_R(s2+1)) to (fc[L], fc[R]) = (0,0) mod 3.

# CRITICAL: The pair at the mover (pfc_L(s1) mod 3, pfc_R(s1) mod 3) is reached
# from (0,0) by the path of the walk before s1.
# If that path visits L at least 3 times (one full cycle mod 3) AND R at least 3 times:
# then all 9 pairs are hit before s1, guaranteeing EC.
# But this might not happen.

# Actually, we don't need ALL 9 pairs hit. We just need the MOVER's pair to be hit
# by SOME non-mover in the same parity class.

# The mover at s1 has pair (pfc_L(s1), pfc_R(s1)) mod 3.
# The non-mover at s1-1 (just before the fire) has pair (pfc_L(s1-1), pfc_R(s1-1)) mod 3.
# These differ by at most (1, 0) or (0, 1) or (0, 0):
# pfc_L(s1) = pfc_L(s1-1) + (1 if word[s1-1] == L else 0).
# pfc_R(s1) = pfc_R(s1-1) + (1 if word[s1-1] == R else 0).

# For the FIRST fire of p at step s1:
# The walk arrives at p from either L or R.
# If from L: word[s1-1] = L. Then pfc_L(s1) = pfc_L(s1-1) + 1, pfc_R(s1) = pfc_R(s1-1).
# If from R: word[s1-1] = R. Then pfc_R(s1) = pfc_R(s1-1) + 1, pfc_L(s1) = pfc_L(s1-1).

# So the mover pair and the previous non-mover pair differ by exactly 1 in one component.
# EC at parity 0 iff (pfc_L(s1), pfc_R(s1)) mod 3 = (pfc_L(t), pfc_R(t)) mod 3 for some non-mover t at parity 0.
# The "previous" non-mover (s1-1) has pair that differs by 1 in one component mod 3.
# This is an EC iff the +1 doesn't change the residue, i.e., iff the incremented component was ≡ 2 mod 3.
# (a mod 3) = ((a-1)+1) mod 3 = (a-1) mod 3 iff a mod 3 = (a-1) mod 3 + 1 mod 3... no.
# (a mod 3) = ((a-1) mod 3) iff a ≡ 0 and a-1 ≡ 2... that's a mod 3 = 0, (a-1) mod 3 = 2. 0 ≠ 2. NOT EQUAL.
# Actually we need (a mod 3) == ((a-1) mod 3)? That's never true for integers a.

# Wait, the non-mover at s1-1 has pair (pfc_L(s1-1) mod 3, pfc_R(s1-1) mod 3).
# The mover at s1 has pair (pfc_L(s1) mod 3, pfc_R(s1) mod 3).
# If arrived from L: pfc_L(s1) = pfc_L(s1-1) + 1. So the L-component differs.
# If pfc_L(s1) mod 3 == pfc_L(s1-1) mod 3: then 1 ≡ 0 mod 3. IMPOSSIBLE.
# So the pair ALWAYS differs by 1 in the L-component (or R-component) mod 3.
# The adjacent non-mover NEVER has the same pair as the mover.

# But what about NON-ADJACENT non-movers? E.g., step s1-2 or earlier?
# Those could have any pair.

# ACTUALLY: the "after second fire" segment wraps around to before the first fire.
# So the parity-0 non-movers include both segments.
# The pair (pfc_L, pfc_R) mod 3 traces a specific path in Z_3 x Z_3.
# After the full cycle: (fc_L, fc_R) mod 3 = (0, 0) since fc = k*ms.
# The path is a CLOSED loop in Z_3 x Z_3.
# A closed loop of length >= CL - 2 in a 9-point space.
# For CL - 2 >= 19: the loop visits >= 19 points. Must revisit many points.
# The mover's pair is one point on this loop. The non-movers trace the rest.
# Since the loop closes and has length >= 19 in a 9-point space: the mover's point
# is likely revisited. But not GUARANTEED.

# Hmm. Let me think about this differently.

# COMPLETELY NEW APPROACH: Maybe I should check whether the sorry case
# (odd winding + non-consecutive binary + isolated + non-uniform)
# is actually VACUOUSLY EMPTY for n >= 9.

# The edge count analysis shows: walks exist for n >= 7 with non-min fc.
# But those walks may ALL have non-isolated binary firings!

# Let me check: among the walks with valid edge counts,
# can the binary have non-isolated firings?

print("CHECKING: Do valid walks with isolated binary firings exist?")
print("=" * 70)
print()
print("Edge count analysis gives: for each edge (p, p+1), the CW and CCW")
print("traversal counts. From these, we know how many times each processor")
print("is visited and the direction structure. But it doesn't tell us about")
print("CONSECUTIVE firings at the same processor.")
print()
print("For binary p with fc[p] = 2: p is visited twice.")
print("If the two visits are consecutive: word = ...p, p,... (non-isolated).")
print("For binary p, consecutive fires mean the walk goes p -> (p+-1) -> p.")
print("Wait no: consecutive FIRINGS mean word[t] = p and word[t+1] = p.")
print("But in a +-1 walk: word[t+1] = word[t] +- 1, so word[t+1] != word[t].")
print("In a +-1 walk, CONSECUTIVE FIRINGS AT THE SAME PROC ARE IMPOSSIBLE!")
print()
print("!!!! THIS IS THE KEY INSIGHT !!!!")
print()
print("In a valid +-1 cyclic walk, consecutive positions differ by 1.")
print("So word[t] != word[t+1] for all t.")
print("Therefore, consecutive firings at the same processor NEVER happen.")
print("Binary firings are ALWAYS isolated in a +-1 walk!")
print()
print("This means: the 'isolated firings' condition in the Lean proof is")
print("AUTOMATICALLY satisfied for any +-1 cyclic walk.")
print("The sorry case is: odd winding + non-consecutive binary + +-1 walk.")
print("And we've shown: this case is equivalent to odd winding + non-consecutive binary.")
print()

# But wait: the Lean GoodCycle mover word IS a +-1 walk (token moves +-1).
# So 'isolated' is always true. The trichotomy EC/permanent/isolated
# means: either EC (done), or permanent (all steps fire p, impossible for +-1 walk
# since other procs need to fire too), or isolated (always true for +-1 walk).

# So the sorry case is essentially: odd winding + non-consecutive binary +
# binary p fires >= 2 (guaranteed by odd winding) + NOT EC at p directly.

# The proof needs: under these conditions, SOME proc has EC.

# Combined with the parity argument: if ALL fc vectors that could produce
# odd winding also have EC, we're done.

# For minimum fc: parity obstruction -> vacuously true.
# For non-minimum fc (one ternary doubled): walks exist for n >= 7.
#   For these walks: we need EC.

# But: even for non-minimum fc, the BINARY fires are still at minimum (fc = 2).
# Only the ternary was incremented. So the binary has fc = 2.

# Actually: the Lean proof picks a SPECIFIC binary p and asks about its firings.
# It could be that p has fc[p] > 2 if the user chose to increment p's multiplier.
# But the proof only needs fc[p] >= 2.

# THE ACTUAL THEOREM TO PROVE:
# For any +-1 cyclic walk with odd winding and fire counts fc[p] = k_p * ms[p]
# where ms has 3 non-consecutive binary and product < threshold:
# EC exists.

# From parity: odd winding requires B ≡ n (mod 2), which forces CL >= 3n.
# From CL >= 3n >= 21 (for n >= 7):
# We can potentially use pigeonhole at binary p (space 18, CL > 18).

# For n = 5: CL = 15 when possible, but we showed 0 valid walks exist.
# For n = 6: not relevant (n >= 9 in Lean, but let's check anyway).
# For n = 7: CL = 21, space = 18. CL > 18.
# For n = 9: CL = 27, space = 18. CL > 18.

# REFINED PIGEONHOLE: At binary p with fc[p] = 2, non-consecutive (neighbors ternary).
# Space = 3 * 2 * 3 = 18.
# But: the pfc_p component has only 2 values (0 and 1).
# So we can split into two subspaces: pfc_p=0 (space 9) and pfc_p=1 (space 9).
#
# Parity-0: 1 mover step, (CL - 2 - m1) non-mover steps where m1 = number of
#   non-mover steps in parity-1.
# Parity-1: 1 mover step, m1 non-mover steps.
# m1 = s2 - s1 - 1 (steps between the two fires).
# Parity-0 non-movers: CL - 2 - m1.
#
# For parity-0: 1 + (CL - 2 - m1) steps. If CL - 2 - m1 > 9: non-movers > 9 in a
#   9-space, but they might not cover all 9.
# Wait: CL - 2 - m1 > 9 doesn't help directly either.
#
# For parity-0: the mover pair and non-mover pairs live in Z_3 x Z_3.
# CL - 2 - m1 non-mover steps. If >= 9 non-movers AND they cover all 9 pairs: EC.
# But "covering all 9" is not guaranteed.
#
# For parity-1: m1 non-movers. If m1 >= 9 and they cover all 9: EC.
#
# NEITHER parity is guaranteed to have "full coverage" by simple counting.

# OK, let me try yet another approach: the WALK STRUCTURE.

print("=" * 70)
print("WALK STRUCTURE ANALYSIS")
print()
print("In the parity-0 segment (before fire 1, after fire 2, wrapping):")
print("The (pfc_L, pfc_R) mod (3,3) pair traces a path in Z_3 x Z_3.")
print("Each step of the walk that visits L increments pfc_L.")
print("Each step that visits R increments pfc_R.")
print("After a full cycle: pfc_L = fc_L ≡ 0 mod 3, pfc_R = fc_R ≡ 0 mod 3.")
print("So the path is CLOSED in Z_3 x Z_3.")
print()
print("The mover at fire 1 (position s1) has pair (a, b) = (pfc_L(s1), pfc_R(s1)) mod 3.")
print("The non-movers trace the rest of the path.")
print()
print("For EC: need (a, b) to appear among the non-mover pairs.")
print()
print("The path visits (a, b) at step s1 (the mover). Does it visit (a, b) again?")
print("The path has total length CL (all steps). In the parity-0 class: CL - 2 - m1 + 1 steps")
print("(non-movers + 1 mover). If CL - 2 - m1 + 1 > 9: by pigeonhole, some pair is")
print("visited twice. But the mover's pair might be visited only once.")
print()
print("STRONGER ARGUMENT: The (pfc_L, pfc_R) mod 3 path is determined by")
print("the edges traversed. When the walk crosses edge (L-1, L): pfc_L increments.")
print("When it crosses edge (R, R+1): pfc_R increments.")
print("After CL steps: pfc_L = fc_L = 3k_L, pfc_R = fc_R = 3k_R.")
print("So in Z_3: the pair returns to (0,0) after the full cycle.")
print("For fc_L = 3 (minimum ternary): pfc_L goes 0->1->2->0 (three increments).")
print("For fc_L = 6 (doubled): pfc_L goes 0->1->2->0->1->2->0 (six increments).")
print()
print("In Z_3 x Z_3: the path is a sequence of +e_1 and +e_2 moves")
print("(increments in L or R component), interspersed with 'identity' steps")
print("(when neither L nor R fires).")
print("The ONLY changes to the pair happen when L or R fires.")
print("Between L/R firings: the pair stays constant (many non-movers at same pair).")
print()
print("Total L-fires = fc_L = 3k_L. Total R-fires = fc_R = 3k_R.")
print("Total pair-changes = fc_L + fc_R = 3(k_L + k_R).")
print("The pair visits 3(k_L + k_R) + 1 distinct positions on its path")
print("(counting start, not counting repeated positions).")
print()
print("For min fc (k_L = k_R = 1): 7 path positions in 9-space.")
print("For one doubled (k_L = 2, k_R = 1): 10 path positions in 9-space.")
print("10 > 9: by pigeonhole, some pair is visited twice!")
print("But one of those visits is the mover. Is the other a non-mover?")
print()
print("The pair visits 10 positions. One is the mover. 9 are between L/R fires.")
print("Wait, that's not right either. Let me think more carefully.")
