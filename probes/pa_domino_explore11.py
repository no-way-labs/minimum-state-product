#!/usr/bin/env python3
"""
PA Domino Exploration 11: The fc(t) counting contradiction route.

NEW IDEA: Instead of finding EC, show the sorry hypotheses are INCONSISTENT
by a fire-count argument.

The sorry has:
- 3 consecutive binary at {i, t=right(i), rr=right²(i)}
- t fires in isolated fashion, fc(t) ≥ 2
- Min gap has odd parity at a neighbor
- EXISTS a phase that fails dispatch

Claim: The sweep + subthreshold + n≥9 constraints force fc(t) to be small
enough that ALL phases can be dispatched, contradicting the existence of
an undispatchable phase.

Let me check: in a sweep, what's the relationship between fc and the
phase structure?

Actually, let me think about this differently.

SIMPLEST POSSIBLE ROUTE:
The sorry is on ONE extracted phase. What if we could extract ALL phases
and show that EACH one is dispatched?

exists_ternaryPhase gives ONE phase. If we could iterate over ALL phases
and show each is dispatched, we'd be done (since the sorry branch says
one phase fails dispatch).

But we can't iterate in the Lean proof — we'd need to show universally
that all phases satisfy the dispatch condition.

ALTERNATIVE: Show that the phase dispatch failure + odd parity
together imply a GLOBAL property that contradicts subThreshold or n≥9.

Let me think about what the phase dispatch failure means.
¬hmech means the phase has (J, K) with:
- ¬(Even J ∧ Even K): at least one is odd
- ¬(J ≥ 2 ∧ K = 0): if J ≥ 2 then K ≥ 1
- ¬(J = 0 ∧ K ≥ 2): if K ≥ 2 then J ≥ 1

Combining with the phase being a non-empty interval between consecutive
t-fires: J + K ≥ 0.

Cases:
(0, 0): would be Even ∧ Even → dispatched. Excluded.
(1, 0): ¬(Even∧Even) since J=1 odd. ¬(J≥2∧K=0) since J=1<2. OK.
(0, 1): symmetric. OK.
(1, 1): both odd. OK.
(1, 2): J=1 odd, K=2 even but J odd → ¬(Even∧Even). J≠0 → ¬(J=0∧K≥2). OK.
(2, 1): symmetric. OK.
(1, K) K≥1: all OK (J=1 is odd).
(J, 1) J≥1: all OK.
(2, 0): Even∧Even (2 even, 0 even) → dispatched. NO! Wait: 0 is even, 2 is even.
  So (2,0) is dispatched by Even∧Even. Also by J≥2∧K=0.
(0, 2): dispatched.
(3, 0): dispatched by J≥2∧K=0.
(0, 3): dispatched by J=0∧K≥2.
(2, 2): Even∧Even → dispatched.
(3, 1): J=3 odd → ¬(Even∧Even). J≥2 but K=1≠0 → ¬(J≥2∧K=0). J≠0 → ¬(J=0∧K≥2). OK.
(1, 3): symmetric. OK.

So the undispatchable (J,K) pairs are exactly those with:
  BOTH nonzero (J≥1 AND K≥1) AND at least one odd.
  OR (1,0) or (0,1).

Wait, (1,0): J=1, K=0. ¬(J≥2∧K=0) since J=1<2. So NOT dispatched by the second clause.
¬(Even∧Even) since J=1 odd. ¬(J=0∧K≥2) since J≠0. Correct, (1,0) is undispatchable.

Similarly (0,1) is undispatchable.

So undispatchable = { (J,K) : (J=1,K=0) ∨ (J=0,K=1) ∨ (J≥1 ∧ K≥1 ∧ (Odd J ∨ Odd K)) }.

Interesting. In particular: (1,0), (0,1), and anything with both ≥1 and at least one odd.

NOW: the min gap has odd parity at SOME neighbor. The min gap is also a phase.
The min gap is the SMALLEST gap. Any other gap is ≥ this size.

If the min gap has (J,K) = (1,0): it's undispatchable AND odd parity (J=1 is odd).
If the min gap has (J,K) = (0,1): undispatchable AND odd parity.
If the min gap has (J,K) = (1,1): undispatchable AND odd parity at both.

And the EXTRACTED phase (from exists_ternaryPhase) is some OTHER phase.
The dispatch fails for that other phase too.

Hmm, but exists_ternaryPhase might extract the min gap phase itself.
Let me check what exists_ternaryPhase does.
"""

# Let me look at the actual min gap vs extracted phase relationship
# In the code:
# mg = exists_minFiringGap gc (right i) hfc_ri  -- min gap
# phase = exists_ternaryPhase gc (right i) hfc_ri hfc_lt  -- some phase

# These could be the same or different. The key: the sorry has BOTH
# the min gap (mg) and the extracted phase (phase) available.

# Wait, actually re-reading the code more carefully:
# Line 282: let mg := exists_minFiringGap ...
# Line 295: obtain ⟨phase, _⟩ := exists_ternaryPhase ...
# These are separate constructions. phase is an arbitrary phase.

# The sorry has:
# 1. mg: min gap with odd parity at a neighbor
# 2. phase: some phase that fails dispatch
# These might be the same gap or different gaps.

# If they're the SAME gap: we have a gap with both odd parity and failed dispatch.
# If different: we know TWO gaps have specific properties.

# Actually, the key question: does exists_ternaryPhase produce a phase
# that is an interval between consecutive t-fires? If so, its (J,K) is
# independent of the min gap.

# For the proof: we don't need to care about the relationship.
# We just need to derive False.

# NEW INSIGHT: Maybe the proof should IGNORE the extracted phase entirely
# and work only with the min gap + global structure.

# The min gap has:
# - Gap size ≥ 2 (isolated)
# - Odd parity at left OR right neighbor
# - It's the MINIMUM gap

# What if the min gap has size exactly 2?
# Gap size 2: between t-fires a and b = a+2.
# In steps a+1: some proc fires (not t). Exactly 1 step.
# J + K ≤ 1 (at most 1 fire of i or rr in one step).
# If J=1, K=0: i fires. Odd parity at i.
# If J=0, K=1: rr fires. Odd parity at rr.
# If J=0, K=0: neither fires. But then parity would be even at both. Contradiction with ¬hparity.
# If J=1, K=1: impossible, only 1 step in the gap.
# Actually: gap_size = b - a. Steps in gap: a+1, a+2, ..., b-1.
# If b = a + 2: gap steps = {a+1}. Only 1 step.
# So exactly one proc fires (the mover at step a+1).
# J + K ≤ 1 since only 1 step.

# For gap_size = 3: steps a+1, a+2. 2 steps. J + K ≤ 2.
# Possible: (1,0), (0,1), (1,1), (2,0), (0,2), (0,0), etc.
# But (0,0) → even parity → contradiction with ¬hparity.

# Now: the min gap constrains ALL gaps (each gap ≥ min_gap_size).
# The phase structure is tight.

# WAIT. I just realized something important.
# The sorry is after the parity check on the MIN GAP ONLY.
# The min gap has odd parity at SOME neighbor.
# But other gaps might have even parity. The sorry doesn't claim
# all gaps have odd parity.

# The sorry also has the extracted phase failing dispatch.
# The extracted phase could be the min gap or a different gap.

# Let me think about what the TIGHTEST constraint is.

# ACTUALLY: I think the cleanest route is to show that in the sorry branch,
# we can extract a min-gap phase that gives EC directly, WITHOUT going
# through the dispatch.

# The key tool: the min gap has gap_size ≥ 2 (from isolated), and
# odd parity at a neighbor. The min gap phase has (J, K) with
# Odd(J) ∨ Odd(K).

# If min gap phase has (J, K) = (1, 0):
# In a 1-step gap: i fires, t doesn't, rr doesn't.
# Before i fires: context at t = (c_i, c_t_after, c_rr).
# After i fires: context at t = ((c_i+1)%2, c_t_after, c_rr).
# At next t-fire (step b): context at t = ((c_i+1)%2, c_t_after, c_rr).
# SAME as after i fires! And at the step when i fires, the non-mover
# observation at t is (c_i, c_t_after, c_rr) (pre-i-fire).
# At step b, mover at t has context ((c_i+1)%2, c_t_after, c_rr).
# These differ in L: c_i vs (c_i+1)%2. No EC at t from this alone.

# But: consider EC at the TERNARY neighbor of i.
# Actually, maybe the right approach is to look at this computationally
# one more time, but focus on the MIN GAP structure.

# Let me search for the simplest proof that works.

print("EXPLORING: What if we show the sorry hypotheses imply")
print("fc(left t) + fc(right t) >= fc(t) + 2, contradicting subThreshold?")
print()

# With 3 consecutive binary and sub-threshold:
# product = 8 * prod(ternary) < 4 * 3^(n-2)
# prod(ternary) < 3^(n-2)/2 < 3^(n-2)
# So all ternary are exactly 3.

# Fire counts: binary fc = 2k ≥ 2. Ternary fc = 3j ≥ 3.
# Cycle length L = fc(i) + fc(t) + fc(rr) + sum(fc(ternary)).

# In a sweep: L ≥ 2n (displacement ≥ 2n, each step moves 1).
# Actually not exactly; let me not worry about this.

# The phases at t: fc(t) gaps, each with (J_k, K_k).
# Sum of J_k = fc(i) (over all gaps including wrap).
# Sum of K_k = fc(rr) (over all gaps including wrap).
# Actually that's wrong: the sum counts i-fires in ALL gaps = fc(i) only if
# ALL i-fires are in some gap of t. That IS true if we count wrap-around.

# Now: with odd parity in min gap and dispatch failure,
# what can we conclude about fc(i) + fc(rr) vs fc(t)?

# If every gap has J + K ≥ 1: sum = fc(i) + fc(rr) ≥ fc(t).
# This is the content of sparse_phase_sum_ge (under ¬EC and all normalForm).
# But we don't have ¬EC as hypothesis.

# Hmm. The sorry CAN use entryConflict_impossible to get False from EC.
# So it can assume ¬EC (by contradiction).

# Let me re-read: the sorry needs False. Approach by contradiction:
# Assume ¬hasEntryConflict gc. Then derive contradiction using
# the structural constraints.

# Under ¬EC: all phases are normalForm (from the existing lemmas?).
# Actually, the existing infrastructure proves sparse_phase_sum_ge
# under the assumptions: all phases normalForm, ¬EC, isolated, binary neighbors.
# These assumptions ARE available in the sorry branch!

# Wait, are they? The sorry has:
# - hbL : sys.rs.m (left (right i)) = 2  (i.e., m_i = 2)
# - hbR : sys.rs.m (right (right i)) = 2  (i.e., m_rr = 2)
# - hiso : isolated firings at t
# - hfc_ri : fc(t) ≥ 2
# - hfc_lt : fc(t) < L

# But does it have "all phases normalForm"?
# The sorry branch has ¬hmech for ONE phase. It doesn't have ¬hmech for ALL phases.

# The even-parity phases are dispatched (give EC). Under ¬EC, there can be
# NO even-parity phases. So all phases have odd parity → normalForm.

# Wait no: "even parity" ≠ "dispatched". The dispatch conditions are:
# (Even J ∧ Even K) ∨ (J ≥ 2 ∧ K = 0) ∨ (J = 0 ∧ K ≥ 2)
# These give EC. So under ¬EC, none of these hold for ANY phase.
# That means ALL phases are undispatchable!

# So under ¬EC:
# - No phase has (Even J ∧ Even K): at least one of J, K is odd.
# - No phase has (J ≥ 2 ∧ K = 0): if J ≥ 2 then K ≥ 1.
# - No phase has (J = 0 ∧ K ≥ 2): if K ≥ 2 then J ≥ 1.

# This means: for every phase, J + K ≥ 1, and (Odd J ∨ Odd K).
# This is exactly "all phases normalForm" (in some sense).

# With this: sparse_phase_sum_ge gives fc(i) + fc(rr) ≥ fc(t).
# And phase_tight_of_sum_le gives: if fc(i) + fc(rr) + 1 ≤ fc(t),
# then every gap has J + K = 1.

# The counting route (from the doc): also fc(i) + fc(rr) ≤ fc(t).
# Wait, that's claimed in the route doc but I need to verify.

# Actually, the counting route says:
# 1. sparse_phase_sum_ge: fc(L) + fc(R) ≥ fc(t) [under ¬EC + normalForm]
# 2. "The existing counting route also gives the reverse"
# 3. So fc(L) + fc(R) = fc(t)

# What gives the reverse? Looking at the doc:
# "The counting route also gives the reverse: fc(left t) + fc(right t) ≤ fc(t)"
# This needs to come from somewhere. Where?

# In a sweep with 3 consecutive binary: i, t, rr are all binary.
# fc(i) even ≥ 2, fc(t) even ≥ 2, fc(rr) even ≥ 2.
# The sweep has |displacement| ≥ 2n.
# fc(i) + fc(rr) ≤ fc(t) would mean the neighbors fire less than t.

# Is this automatic from the phase structure? In each gap between
# consecutive t-fires: at most J + K fires of the neighbors.
# If every gap has J + K = 1: fc(i) + fc(rr) = fc(t).
# If some gap has J + K ≥ 2: fc(i) + fc(rr) > fc(t) (combining with J + K ≥ 1 in other gaps).

# Hmm wait: fc(i) + fc(rr) = sum over gaps of (J_k + K_k).
# If all gaps have J_k + K_k ≥ 1: sum ≥ fc(t).
# This is sparse_phase_sum_ge.
# The reverse: sum ≤ fc(t) would require each gap has J_k + K_k ≤ 1.

# But under ¬EC + normalForm: what gives J_k + K_k ≤ 1?
# The doc says phase_tight_of_sum_le provides this under fc(p₁) + fc(p₂) + 1 ≤ fc(t).

# So we need fc(i) + fc(rr) + 1 ≤ fc(t) as a HYPOTHESIS for phase_tight_of_sum_le.
# But that's what we're trying to PROVE (the reverse direction).
# This seems circular!

# Unless we can establish fc(i) + fc(rr) + 1 ≤ fc(t) from OTHER constraints.

# Key: binary procs have fc even ≥ 2. So fc(i) ≥ 2 and fc(rr) ≥ 2.
# Combined with fc(i) + fc(rr) ≥ fc(t): fc(t) ≤ fc(i) + fc(rr).
# We need fc(t) ≥ fc(i) + fc(rr) + 1 for phase_tight_of_sum_le.
# But fc(i) + fc(rr) ≥ fc(t) contradicts fc(t) ≥ fc(i) + fc(rr) + 1.

# So phase_tight_of_sum_le can't be applied directly!

# The doc says the two bounds together give equality. But sparse_phase_sum_ge
# gives ≥, and we need the ≤ direction from somewhere else.

# I think the ≤ direction comes from:
# fc(t) ≥ sum of phases' (J_k + K_k) - (wrap contribution)
# Hmm, it's not clear.

# Let me look at the problem from the SWEEP perspective.
# In a sweep, each processor has a specific number of CW and CCW fires.
# The binary proc t has fc_CW(t) CW fires and fc_CCW(t) CCW fires.
# fc(t) = fc_CW(t) + fc_CCW(t).
# Since t is binary: fc(t) even ≥ 2.

# In a CW pass through t: ..., i fires, t fires, rr fires, ...
# In a CCW pass through t: ..., rr fires, t fires, i fires, ...

# Each CW t-fire is preceded by an i-fire and followed by an rr-fire.
# Each CCW t-fire is preceded by an rr-fire and followed by an i-fire.

# So in the gap between a CW t-fire and the next t-fire:
# If next is also CW: i fires (at end), rr fires (at start of next CW).
#   Wait, this gets complicated with alternating CW/CCW.

# SIMPLEST IDEA: forget about sweep structure. Just use:
# 1. Assume ¬EC (by contradiction)
# 2. Under ¬EC: all phases at t have J + K ≥ 1 (normalForm)
# 3. sparse_phase_sum_ge: fc(i) + fc(rr) ≥ fc(t)
# 4. Binary constraints: fc(i), fc(rr), fc(t) all even ≥ 2
# 5. The "reverse" bound: ???

# I think I need to find where the reverse bound comes from in the codebase.

print("Need to find the reverse bound fc(i) + fc(rr) <= fc(t).")
print("Searching codebase...")
