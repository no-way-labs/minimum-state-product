#!/usr/bin/env python3
"""
PA Proof Route: The CORRECT argument for the sorry branch.

After extensive exploration, the key findings are:

1. The parity obstruction: EC at t (middle binary) cannot come from the
   phase structure alone (S-component always distinguishes mover/non-mover).

2. EC is universal (computationally verified) but occurs at DIFFERENT
   processors for different cycles.

3. The sorry branch (odd parity + dispatch failure) is NOT vacuous —
   it's the generic case for sweep cycles with 3 consecutive binary.

4. Under ¬EC (by contradiction), ALL phases at t have normalForm
   (no phase satisfies any dispatch condition — they all give EC if dispatched).

5. sparse_phase_sum_ge gives fc(L) + fc(R) ≥ fc(t) under ¬EC.

CORRECT PROOF ROUTE:

The sorry needs False. We can use proof by contradiction:
- Assume ¬hasEntryConflict gc.
- Under this assumption, ALL phases satisfy normalForm (if any phase
  satisfied dispatch, it would give EC, contradicting ¬EC).
- Apply sparse_phase_sum_ge to get fc(i) + fc(rr) ≥ fc(t).
- Binary constraints: fc(i) even ≥ 2, fc(rr) even ≥ 2, fc(t) even ≥ 2.
- So fc(t) ≤ fc(i) + fc(rr).
- But fc(t) is also ≥ 2. And fc(i) + fc(rr) ≥ fc(t) ≥ 4.

Now the KEY: we also need an UPPER bound on fc(i) + fc(rr) relative to fc(t).
This is where the proof gets interesting.

Actually, let me reconsider. The right route might be:

Under ¬EC:
- All phases have J + K ≥ 1 (from normalForm argument).
- sparse_phase_sum_ge gives fc(i) + fc(rr) ≥ fc(t).
- Now consider the phases at PROC i (not at t).
  Between consecutive i-fires, t fires some number of times.
  i is binary, so fc(i) even ≥ 2.
  left(i) is ternary, right(i) = t is binary.
- At proc i, the context = (c_{left(i)}, c_i, c_t).
  Context space = 3 * 2 * 2 = 12 (if left(i) ternary).
- Under ¬EC: mover and non-mover contexts at i are disjoint.
  |mover set| + |non-mover set| ≤ 12.
- fc(i) ≤ |mover set|? No, fc(i) mover observations can reuse contexts.
  But at DISTINCT contexts: each mover observation (c_L, c_i, c_t) has
  c_i determined by parity. So at most 6 distinct contexts per c_i-parity.
  Mover set ≤ 12.
  Non-mover set ≤ 12 - |mover set| (disjoint).

This doesn't give a numerical contradiction.

ALTERNATIVE APPROACH — Binary triple coupling:

Consider all 3 binary procs {i, t, rr} simultaneously.
Each has m = 2. The "joint state" of the triple is (c_i, c_t, c_rr) ∈ {0,1}^3.
There are 8 possible joint states.

The cycle visits these 8 states in some order.
Between any two visits to the same joint state, all 3 procs must have
fired an even number of times (since they return to the same values).

KEY: c_i, c_t, c_rr are binary, and each changes only when its proc fires.
So the joint state (c_i, c_t, c_rr) changes by flipping exactly one bit
at each step where one of {i, t, rr} fires, and stays the same at steps
where none of {i, t, rr} fires (other procs fire).

The joint state traces a walk on the 3-cube {0,1}^3 where:
- Each step either flips one of the 3 bits or stays the same.
- Over the full cycle, the walk returns to start.

Under ¬EC + the phase structure, this walk has specific constraints.
Maybe the walk structure forces EC at one of the procs.

Actually, this is essentially the UBO (Universal Binary Overlap) approach,
which was DISPROVED! The full-context overlap isn't forced by the walk
on the triple.

But UBO was about the 2D projection. The full context involves the
TERNARY neighbors too.

Hmm, let me step back and think about what makes the sorry provable.
"""

# FINAL APPROACH: The sorry branch is provable because
# the odd-parity condition at the min gap, combined with ¬EC,
# creates a specific structural impossibility.
#
# Here's the argument:
#
# 1. Assume ¬EC.
# 2. Under ¬EC, ALL phases at t satisfy normalForm.
# 3. Apply the existing infrastructure:
#    a. sparse_phase_sum_ge: fc(i) + fc(rr) ≥ fc(t)
#    b. Binary: all fire counts even ≥ 2.
# 4. The odd-parity condition in the min gap means:
#    In the min gap (between t-fires a and b):
#    J_min (i-fires) is odd OR K_min (rr-fires) is odd.
# 5. Under ¬EC and normalForm, each phase has J+K ≥ 1.
#    The min gap has J+K ≥ 1.
#    With odd parity: at least one is odd.
# 6. KEY NEW ARGUMENT: Under ¬EC, the min gap parity condition
#    propagates to ALL gaps via the cyclic structure.
#    Since the sum of all J_k = fc(i) (even) and sum of all K_k = fc(rr) (even),
#    if the min gap has J odd, some OTHER gap must also have J odd (to make total even).
#    Combining with J_k ≥ 0 for all k, and J_k + K_k ≥ 1.
# 7. The min gap has MINIMUM size. So all other gaps are ≥ this size.
#    With J_k + K_k ≥ 1 for each gap and the totals being even:
#    This creates specific parity constraints.
#
# WAIT: this isn't leading anywhere specific. Let me try yet another angle.
#
# CLEAN APPROACH:
# The sorry has hconv (convergence). Maybe use:
#   Convergence + ¬EC → valid system → subThreshold contradiction?
#
# No, ¬EC means we CAN build a valid system. SubThreshold says product < bound.
# The combination doesn't obviously give a contradiction.
#
# Let me look at the sorry branch from the LEAN SIDE once more.
# The sorry needs False. Available:
# - entryConflict_impossible (needs hasEntryConflict)
# - hconv (convergence)
# - hn (n ≥ 9)
# - hsub (subThreshold)
# - All the binary structure hypotheses
#
# What if we DON'T try to find EC but instead use hsub directly?
# subThreshold sys.rs means prod(m_p) < 4 * 3^(n-2).
# With 3 binary: 8 * prod(ternary) < 4 * 3^(n-2).
#
# The sorry branch's constraints might force a MINIMUM cycle length
# that's incompatible with the state counts.
# Specifically: if fc(t) ≥ some value, and the cycle length is too large
# relative to the product, then the good cycle can't exist.
#
# Actually, cycle length L ≤ prod(m_p) in a good cycle?
# No! Cycle length can be much larger than product.
# L = sum(fc(p)) which depends on fire counts, not product.
#
# Hmm. The product bounds the NUMBER OF DISTINCT CONFIGS, not the cycle length.
# In a good cycle, configs are distinct (no repeated config until return).
# So L ≤ prod(m_p). (Each config is unique.)
#
# WAIT: that's the key! L ≤ prod(m_p) because configs don't repeat in a good cycle!
# prod(m_p) < 4 * 3^(n-2) (subThreshold).
# L ≤ 4 * 3^(n-2) - 1.
#
# And L = sum(fc(p)) ≥ sum over binary fc ≥ 2 * 3 = 6 (for 3 binary)
# Plus sum over ternary fc ≥ 3 * (n-3) = 3n - 9.
# Total L ≥ 3n - 3.
# For n = 9: L ≥ 24. And L ≤ 4 * 3^7 - 1 = 8747. Plenty of room.
# So this doesn't give a contradiction.
#
# I think the correct approach is actually:
# Show that under ¬EC, the cycle structure at t + binary neighbors
# forces a specific joint state pattern that IS an entry conflict
# at some other processor.
#
# But this is what the existing lemmas partially do. The question is:
# what's the FINAL step that closes it?

print("After extensive exploration, the conclusion is:")
print()
print("The sorry branch needs a proof that EITHER:")
print("  (A) Shows hasEntryConflict gc (→ False via entryConflict_impossible)")
print("  (B) Shows a direct contradiction from the hypotheses")
print()
print("The simplest approach that's mathematically correct:")
print()
print("PROOF BY CONTRADICTION:")
print("  Assume ¬hasEntryConflict gc.")
print("  Under ¬EC:")
print("  1. No phase at t satisfies dispatch (each would give EC).")
print("     So ALL phases are 'normalForm' — each has Odd(J) ∨ Odd(K)")
print("     and neither (J≥2,K=0) nor (J=0,K≥2).")
print("  2. sparse_phase_sum_ge applies: fc(i) + fc(rr) ≥ fc(t).")
print("  3. Binary: fc(i), fc(rr), fc(t) all even ≥ 2.")
print("  4. The min gap has J_min and K_min with Odd(J_min) ∨ Odd(K_min).")
print()
print("  Now: each phase has J_k + K_k ≥ 1.")
print("  Sum J_k = fc(i), Sum K_k = fc(rr).")
print("  fc(i) + fc(rr) ≥ fc(t) (from step 2).")
print("  fc(i) + fc(rr) = sum(J_k + K_k) ≥ fc(t) (from step 2).")
print()
print("  The question: can we get fc(i) + fc(rr) ≤ fc(t)?")
print("  If yes: fc(i) + fc(rr) = fc(t), every phase has J+K = 1.")
print("  Then the 'domino' argument applies.")
print()
print("  But do we HAVE fc(i) + fc(rr) ≤ fc(t)?")
print("  In a sweep: maybe. The sweep structure constrains fire counts.")
print()
print("CRITICAL INSIGHT: The sorry does NOT have hsweep!")
print("consec_isolated_false does not take hsweep as an argument.")
print("It has: hn, gc, hconv, hno_safe, hsub, h3bin, i, h3consec, hfc_ri, hiso.")
print()
print("So the proof CANNOT use sweep-specific arguments!")
print("It must work for ALL good cycles meeting these conditions.")
print()
print("This changes everything. Without sweep, we can't constrain")
print("the fire counts or cycle structure as tightly.")
