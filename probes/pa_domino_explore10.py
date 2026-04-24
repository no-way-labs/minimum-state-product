#!/usr/bin/env python3
"""
PA Domino Exploration 10: Simple pigeonhole at the boundary binary.

Key insight for a clean proof:

Consider proc i (boundary binary). Its neighbors are left(i) [ternary, m≥3]
and right(i) = t [binary, m=2].

Context space at i: m_{left(i)} * 2 * 2 ≤ max_neighbor * 4.
With sub-threshold: m_{left(i)} ∈ {3, 4} (at most).
So context space at i ≤ 16 (usually 12).

In a sweep cycle with n ≥ 9:
- fc(i) = fire count of i (binary, even, ≥ 2)
- Non-mover steps at i: L - fc(i) where L = cycle length.
- L ≥ 3*2 + (n-3)*3 = 3n - 3 for minimum fire counts.
  For n = 9: L ≥ 24.
  For n = 10: L ≥ 27.

For EC at i: need mover and non-mover context overlap.
There are fc(i) mover observations and L - fc(i) non-mover observations.
Total = L observations in a context space of C_i.
If L > C_i, pigeonhole gives: either >C_i mover observations (repeated mover
contexts) or >C_i non-mover observations (repeated non-mover contexts),
or there's mover/non-mover overlap.

More precisely: if fc(i) > C_i or L - fc(i) > C_i, we get repeated same-type
observations. But repeated same-type doesn't immediately help.

For mover/non-mover overlap via pigeonhole:
STRONGER: if fc(i) + (L - fc(i)) = L > 2 * C_i, then BY PIGEONHOLE THERE IS OVERLAP?
No! fc(i) mover contexts ⊆ C_i contexts, (L - fc(i)) non-mover contexts ⊆ C_i contexts.
If they're disjoint: fc(i) ≤ |mover set| ≤ C_i and (L - fc(i)) ≤ |non-mover set| ≤ C_i.
But |mover set| + |non-mover set| ≤ C_i if they're disjoint!
Wait no, if they're disjoint: |mover set ∪ non-mover set| = |mover set| + |non-mover set| ≤ C_i.
So fc(i) ≤ |mover set| and L - fc(i) ≤ |non-mover set|.
But L = fc(i) + (L - fc(i)) ≤ |mover set| + |non-mover set| ≤ C_i.
So L ≤ C_i!

WAIT. That's wrong. Multiple observations can have the SAME context.
fc(i) mover observations can use at most C_i distinct contexts.
(L - fc(i)) non-mover observations can use at most C_i distinct contexts.
Total distinct contexts used: at most 2 * C_i.
But that doesn't help either.

The correct statement: if the mover set and non-mover set are disjoint,
|mover set| + |non-mover set| ≤ C_i. And each set has ≤ C_i elements.
There's no constraint from the COUNTS fc(i) and L - fc(i) alone.

So pure pigeonhole on observation COUNTS doesn't work.

But wait: for binary proc i, the mover observations are more constrained.
At mover step k (the k-th firing of i): c_i = (init + k) % 2.
So mover observations at even-indexed firings all have c_i = init,
and at odd-indexed firings all have c_i = (init + 1) % 2.

Similarly, non-mover observations between firing k and k+1 all have
c_i = (init + k + 1) % 2 (i just fired, value flipped).

So: even-firing mover contexts have (*, init, *).
    Non-mover contexts after even firings have (*, (init+1)%2, *).
    Odd-firing mover contexts have (*, (init+1)%2, *).
    Non-mover contexts after odd firings have (*, init, *).

EC at i requires: a mover context (*, v, *) matching a non-mover context (*, v, *).
From the parity:
- Even-firing mover has c_i = init. Non-mover with c_i = init comes from
  after odd firings.
- Odd-firing mover has c_i = (init+1)%2. Non-mover with c_i = (init+1)%2
  comes from after even firings.

So EC at i requires matching between:
- Even-firing mover context and after-odd-firing non-mover context, OR
- Odd-firing mover context and after-even-firing non-mover context.

This is CROSS-PARITY matching, similar to the parity obstruction at t.
But the difference: at t, the left AND right neighbors are ALSO binary,
creating a double parity constraint. At i, the left neighbor is TERNARY,
breaking the parity constraint.

Let me formalize: at proc i:
- Context = (c_{left(i)}, c_i, c_t) where c_{left(i)} ∈ {0,1,2} (ternary)
  and c_i, c_t ∈ {0,1}.

Mover observations at i's k-th firing:
  c_i = (init_i + k) % 2
  c_t = state of t at this step
  c_{left(i)} = state of left(i) at this step

Non-mover observations between i's k-th and (k+1)-th firing:
  c_i = (init_i + k + 1) % 2  (i just fired)
  c_t = changes when t fires in this interval
  c_{left(i)} = changes when left(i) fires in this interval

For the matching: we need the LEFT NEIGHBOR (ternary) component to also match.
Since ternary: c_{left(i)} ∈ {0,1,2}, and its value changes by +1 mod 3 each fire.
The parity constraint applies to c_i and c_t (both binary), but NOT to c_{left(i)}.

So the extra degree of freedom from the ternary neighbor is what allows EC at i.
But it's not automatic — it depends on the specific fire pattern.

Let me think about when EC is forced.

Actually, maybe the simplest route is: USE THE EXISTING PROVEN MACHINERY.
The sorry branch has many things already proved. Maybe the missing piece is
just connecting existing lemmas.

Let me look at what the sorry actually needs to produce and what's already available.
"""

# Rather than pigeonhole, let me think about what the Lean sorry actually
# needs to close. It needs `False`. The hypotheses include everything
# listed in the function signature of consec_isolated_false.

# The sorry sits inside a by_cases on hmech. The "false" branch has ¬hmech.
# ¬hmech means the extracted phase doesn't satisfy any dispatch condition.

# What does ¬hmech actually give us about J and K in the extracted phase?
# hmech = (Even J ∧ Even K) ∨ (J ≥ 2 ∧ K = 0) ∨ (J = 0 ∧ K ≥ 2)
# ¬hmech = ¬(Even J ∧ Even K) ∧ ¬(J ≥ 2 ∧ K = 0) ∧ ¬(J = 0 ∧ K ≥ 2)
# = (Odd J ∨ Odd K) ∧ (J < 2 ∨ K > 0) ∧ (J > 0 ∨ K < 2)
# Simplifying: at least one of J, K is odd. If J ≥ 2 then K > 0. If K ≥ 2 then J > 0.

# The odd parity condition (hparity) gives: in the min gap,
# i-fires have odd parity OR rr-fires have odd parity.
# This means: in the min gap, J is odd or K is odd.

# Actually, ¬hparity means NOT (J%2 == prev_J%2 AND K%2 == prev_K%2).
# I.e., J changes parity across the gap OR K changes parity across the gap.
# For the min gap of an isolated binary proc:
# The gap has exactly J fires of i and K fires of rr.
# The parity of prefix fire count changes by J (resp K).
# If J is odd: parity changes for i. If K is odd: parity changes for rr.
# ¬hparity: J is odd OR K is odd (not both even).

# So: the min gap has Odd(J) ∨ Odd(K). Combined with ¬hmech:
# we get that the phase is "normalForm" (not dispatchable).

# The question: what can we conclude from having a normalForm phase
# at binary proc t with binary neighbors?

# ACTUALLY: let me reconsider the whole approach. Instead of trying to prove EC,
# what if we prove that the hypotheses are INCONSISTENT?

# The key constraint: t = right(i) is binary with fc(t) ≥ 2.
# t fires in isolated fashion. Both neighbors are binary.
# Parity check failed. Dispatch failed.

# With both neighbors binary and isolated firings:
# Between consecutive t-fires, at most 1 neighbor fires (from normalForm).
# Actually, dispatch failure doesn't directly give normalForm (J+K ≤ 1).
# Dispatch failure says: not (both even), not (J≥2 K=0), not (J=0 K≥2).

# The min gap has (J, K) where J + K ≥ 1 (gap size ≥ 2, so something fires)
# and (Odd J ∨ Odd K) and not dispatchable.

# Remaining cases for (J, K):
# - (1, 0): J=1, K=0. Odd J. ¬(J≥2∧K=0) since J=1<2. ¬(J=0∧K≥2) since J≠0.
#   ¬(Even J ∧ Even K) since J odd. So this passes ¬hmech. ✓
# - (0, 1): symmetric. ✓
# - (1, 1): both odd. ¬(Even J ∧ Even K). ¬(J≥2∧K=0) since K≠0.
#   ¬(J=0∧K≥2) since J≠0. ✓
# - (1, 2): J=1 odd. ¬(Even J∧Even K). ¬(J≥2∧K=0) since K≠0.
#   ¬(J=0∧K≥2) since J≠0. ✓
# - (2, 1): symmetric. ✓
# - (1, K) for K≥3: similar. ✓
# - (J, 1) for J≥3: similar. ✓
# - (3, 0): J=3 odd. ¬(Even∧Even). ¬(J=0∧K≥2) since J≠0. But J≥2∧K=0: J=3≥2, K=0. ✓ for dispatch!
#   Wait: (3,0): J≥2 and K=0 → dispatched! So ¬hmech excludes this.
# - (0, 3): symmetric, dispatched.

# So ¬hmech with ¬hparity gives: min gap (J,K) with:
# J+K ≥ 1, Odd(J)∨Odd(K), J<2∨K>0, J>0∨K<2.
# This is: (1,0), (0,1), (1,1), (1,2), (2,1), (1,K≥3), (J≥3,1), (2,K odd≥1), etc.
# But NOT (J≥2,0) or (0,K≥2) — those are dispatched.
# And NOT (Even J, Even K) — that's dispatched.

# The common thread: J and K are both ≥ 1 (neither is 0), OR one is exactly 1.
# Actually: (1,0) has K=0 and J=1<2. (0,1) has J=0 and K=1<2.
# All other cases have J≥1 and K≥1.

# For the MIN gap: this is the smallest gap between consecutive t-fires.
# If the min gap has J=1, K=0: left(t) fires once, right(t) doesn't fire.
# This is a "tight one-sided" phase.

# The key realization: the parity failure + dispatch failure together
# constrain the phase structure, but they DON'T by themselves give EC.
# EC comes from the INTERACTION between the phase structure and the
# binary fire counts.

# NEW IDEA: The proof might be simpler than I thought.
# If we have n ≥ 9 and the sorry branch hypotheses, perhaps we can
# show that the fire count constraints are contradictory.

# Specifically: with 3 consecutive binary, sub-threshold product,
# and the specific phase structure from the sorry branch,
# maybe the fire counts can't all be satisfied simultaneously.

# Let me check: what are the fire count constraints?
# Binary proc: fc is a positive even number.
# Ternary proc: fc is a positive multiple of 3.
# Cycle length L = sum of fc(p).

# With sweep: |displacement| ≥ 2n. For displacement = CW - CCW,
# and CW = ccwMoveCount, CCW = cwMoveCount:
# fc(p) = CW_moves_at_edge_p + CCW_moves_at_edge_p.
# Sweep → |CW - CCW| ≥ 2n → CW + CCW ≥ 2n → L ≥ 2n.

# For n = 9: L ≥ 18. But with 3 binary fc=2 and 6 ternary fc=3: L ≥ 24.
# 24 ≥ 18 ✓.

# The phase structure adds: between consecutive t-fires (fc(t) gaps),
# each gap has specific (J, K). The sum over all gaps: J_total = fc(i),
# K_total = fc(rr). And the gap structure from the sorry branch constrains
# each individual gap.

# But this doesn't give a fire count contradiction.

# I think the right approach is: EMBRACE that EC is the mechanism,
# and find a proof at SOME processor that works for n ≥ 9.

# The key structural fact: with n ≥ 9, there are many ternary processors.
# Among them, some have binary neighbors. The context space at these
# ternary procs is relatively small. And the cycle is long.

# For a ternary proc q with binary right neighbor:
# Context space = m_{left(q)} * 3 * 2. If left(q) is also ternary: 18.
# If left(q) is binary: 12.

# fc(q) ≥ 3 (ternary). Non-mover observations: L - fc(q).
# For EC: need overlap.

# For q = left(i) (ternary with right(q) = i binary, left(q) ternary):
# Context space = 18.
# fc(q) ≥ 3. q fires at least 3 times: 3 mover observations.
# Non-mover: L - 3 ≥ 21 observations.
# With 18 possible contexts: we need 18 non-mover contexts to be disjoint
# from 3 mover contexts. The 3 mover contexts use ≤ 3 of the 18 slots,
# leaving ≥ 15 for non-mover. 21 observations in 15 slots → repeated,
# but we need cross-type overlap.

# Hmm, cross-type overlap isn't forced by counting alone when one type
# has few observations.

# BETTER: for a ternary proc q with BOTH neighbors binary (sandwiched):
# Context space = 2 * 3 * 2 = 12.
# Such a proc exists! With 3 consecutive binary at {i, t, rr},
# the procs left(i) has right neighbor i (binary), and left(i) itself is ternary.
# But left(left(i)) might not be binary.
# Similarly right(rr) has left neighbor rr (binary), right(rr) is ternary.
# right(right(rr)) might not be binary.

# With EXACTLY 3 consecutive binary (no 4th): left(i) and right(rr) are ternary.
# left(left(i)) is ternary (not binary). right(right(rr)) is ternary (not binary).
# So left(i) has context space = 3 * 3 * 2 = 18. Not sandwiched.

# What about internal ternary procs far from the binary triple?
# Those have both neighbors ternary: context space = 3 * 3 * 3 = 27. Even worse.

# So the best proc for pigeonhole is i or rr (binary with one ternary neighbor):
# context space = 3 * 2 * 2 = 12.

# For n ≥ 9: L ≥ 3n - 3 ≥ 24.
# If the mover set and non-mover set at i are disjoint:
# |mover set| + |non-mover set| ≤ 12.
# The mover set has fc(i)/2 distinct c_i-even contexts and fc(i)/2 distinct
# c_i-odd contexts (at most 6 each, total ≤ 12).
# Actually no: fc(i)/2 of each parity doesn't mean 6 distinct.
# fc(i) = 2k mover steps. k with c_i = 0, k with c_i = 1.
# Each with at most 3 * 2 = 6 contexts for that c_i value.
# So ≤ 12 distinct mover contexts total. (Could be fewer if L, R repeat.)

# For non-mover: between i-firings, c_i is constant.
# Between firing k and firing k+1: c_i = (init + k + 1) % 2.
# In this gap, c_t can change (t fires), c_{left(i)} can change (left(i) fires).
# Each unique (c_{left(i)}, c_i, c_t) observed at a non-mover step is
# a non-mover context.

# If mover and non-mover sets are disjoint and together ≤ 12:
# then fc(i) ≤ |mover set| ≤ 12 - |non-mover set|.
# And L - fc(i) observations go into |non-mover set| ≤ 12 - |mover set| bins.
# No contradiction from this alone.

# DIFFERENT APPROACH: Use the ternary fire count.
# left(i) is ternary, fc(left(i)) ≥ 3.
# Between consecutive left(i) fires, at least 2 steps (since left(i) is ternary
# and we're in a sweep with large displacement).
# Actually... wait. left(i) fires 3 times (or 6, 9, ...).
# Between consecutive left(i) fires, there are L/3 - 1 steps on average.

# I think the right approach is to GIVE UP on a pure counting argument
# and instead look for a structural argument that uses the SPECIFIC
# properties of the sorry branch (odd parity, dispatch failure, isolated).

print("Shifting to structural analysis of sorry branch.")
print()
print("The sorry branch has:")
print("  1. n >= 9")
print("  2. 3 consecutive binary at {i, t, rr}")
print("  3. t has fc >= 2, isolated firings")
print("  4. Odd parity at neighbor in min gap")
print("  5. Phase dispatch fails for extracted phase")
print()
print("The existing machinery has extensive phase analysis.")
print("The missing piece: connecting the phase structure to EC.")
print()
print("PROPOSED NEW ROUTE:")
print("  Instead of domino at t, show the sorry branch hypotheses")
print("  imply that SOME processor is 'sandwiched' in a way that")
print("  forces EC. The ternary neighbor of i, combined with the")
print("  binary phase structure, may create an unavoidable context")
print("  overlap at i or at left(i).")
print()
print("But the key challenge: at n=7, EC at i is NOT universal")
print("(325 failures out of 1467). So the argument must use n >= 9.")
print()
print("ALTERNATIVE PROPOSED ROUTE:")
print("  Use hconv (convergence). The cycle + transition function")
print("  must converge. The sorry branch structure may make convergence")
print("  impossible without EC.")
print()
print("SIMPLEST PROPOSED ROUTE:")
print("  The sorry proves False. It has hconv. Show:")
print("  IF ¬hasEntryConflict THEN the transition functions can be extended")
print("  to a non-converging system, contradicting hconv.")
print("  This avoids finding EC explicitly.")
