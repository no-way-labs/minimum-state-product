#!/usr/bin/env python3
"""
PA Domino Exploration 3: Understanding the actual sorry branch.

The sorry is in consec_isolated_false. The key conditions are:
1. sweep cycle (uniform sweep)
2. 3 consecutive binary at {i, right(i), right²(i)}
3. t = right(i) has fc(t) ≥ 2, fires in isolated fashion
4. odd parity at both neighbors in min firing gap
5. phase dispatch fails: extracted phase has J+K ≤ 1

The phase extraction looks at the min firing gap of t. In a sweep cycle,
t fires every n steps. The gap between consecutive t-fires is n steps.

Wait — in a SWEEP cycle, every proc fires exactly once per sweep direction.
For binary: fc = 2 (one CW, one CCW). For ternary: fc = 3.

Actually for a sweep cycle of the form CW+CCW (zero winding):
- Each proc fires exactly twice (once CW, once CCW)... no.

Let me re-read the sweep cycle definition.
A sweep is when the movers visit processors in ring order (CW or CCW).
A zero-winding sweep visits every proc exactly fc(p) times total,
going CW through all procs, then CCW through all, etc.

For ms=(2,2,2,3,3) with n=5:
- Binary procs fire 2 times, ternary fire 3 times
- Cycle length = sum of fc(p) = 2+2+2+3+3 = 12? No, cycle length = product...

Actually no. The cycle length is the number of steps. For a sweep:
CW: 0,1,2,3,4 then CCW: 3,2,1,0,4... this depends on the sweep structure.

Let me think about this differently. The normalForm residual is about the
general case, not sweep-specific. The sweep hypothesis gives us that
the mover word visits processors in a sweep pattern.

Actually, re-reading the problem statement: "sweep" and "fc(t) >= 2,
fires in isolated fashion" and the parity/phase conditions.

Let me look at the Lean code to understand the exact hypothesis set.
"""

# Let me instead think about the abstract argument more carefully.
# The exploration 1 showed that EC at t is impossible from phase structure alone
# because the S-component always flips between mover and non-mover observations.

# But we know EC holds computationally. So either:
# (a) EC happens at a different processor than t, or
# (b) There are additional constraints from the sweep structure that we're not using

# Key insight from exploration 1: the mover contexts at t all have
# S_k = (s0+k)%2, and non-mover contexts all have S = (s0+k+1)%2.
# These partition {0,1} by parity of k. No overlap possible.

# This is actually a FUNDAMENTAL observation. It means:
# The domino argument as stated in the problem CANNOT work at proc t.
# The S-flip is an inherent feature of binary processors: at every mover step,
# S changes; at every non-mover step, S stays. So mover observations always
# see the "about-to-change" value and non-mover observations see the "just-changed" value.
# For binary, these are always different.

# Wait, that's not right for general cycles! The S-flip only holds for
# CONSECUTIVE t-fires. In general:
# At some step a, t fires: context has c_t = v. After firing: c_t = (v+1)%2.
# At step b (not t's fire): context at t has c_t = whatever it currently is.
# If t fired at step a, and b > a with no t-fire between, then c_t at b = (v+1)%2.
# At step c > b, t fires again: context has c_t = (v+1)%2. After: c_t = v.

# So BETWEEN consecutive t-fires, the non-mover context at t has the OPPOSITE
# S-value from the previous t-fire's mover context, AND the SAME S-value as
# the next t-fire's mover context.

# Wait, that's the key! The non-mover context MATCHES the next t-fire context
# in the S-component. Let me re-check:

# At t-fire k: S_k = c_t before firing = some value v.
# In phase k (between t-fire k and k+1): c_t = (v+1)%2 = (S_k+1)%2.
# Non-mover context in phase k has S = (S_k+1)%2.
# At t-fire k+1: S_{k+1} = c_t before firing = (S_k+1)%2.
# So YES: non-mover S in phase k = S_{k+1} (mover S at next t-fire).

# But the L and R values: the non-mover context at the neighbor-fire step has
# the PRE-fire neighbor value, while the mover context at t-fire k+1 has the
# POST-fire neighbor value (because the neighbor fired in between).

# Specifically for phase k with left firing (phase_seq[k]=0):
# Non-mover ctx at left-fire step: (L_k, (S_k+1)%2, R_k)  [L before left fires]
# Mover ctx at t-fire k+1: ((L_k+1)%2, (S_k+1)%2, R_k)  [L after left fired]
# These differ in L.

# Non-mover ctx AFTER left fires (any subsequent non-mover step):
# ((L_k+1)%2, (S_k+1)%2, R_k) = mover ctx at t-fire k+1.
# But we established there might be no non-mover step after left fires and before t fires.

# HERE'S THE CRITICAL QUESTION: in a sweep cycle, is there ALWAYS at least one
# non-mover step between left's fire and t's fire (or between right's fire and t's fire)?

# In a sweep cycle, processors fire in ring order. If the sweep goes CW:
# ..., i-1, i, i+1, i+2, i+3, ...
# So left(t) = i fires, then ALL procs between i+1 and t-1 fire, then t fires.
# Wait, t = i+1 (right of i). So left(t) = i fires, then t = i+1 fires.
# In a CW sweep: i fires, then i+1 fires. These are CONSECUTIVE in the sweep!

# That's the problem. In a sweep, left(t) fires immediately before t.
# So there's NO step between left's fire and t's fire where a non-mover
# observation at t can be made.

# Similarly, in a CCW sweep, right(t) fires immediately before t.

# So the non-mover context after the neighbor fires is never observed as a
# non-mover step at t in a sweep.

# What about the non-mover context BEFORE the neighbor fires?
# In phase k with left firing: at the step when left fires,
# non-mover ctx at t = (L_k, (S_k+1)%2, R_k).
# But this is the non-mover observation at the LEFT-FIRE step, which has
# L_k (pre-fire value of left).

# So the observable non-mover contexts are exactly:
# (L_k, (S_k+1)%2, R_k) at the neighbor-fire step.

# For EC at t: need this to equal some mover context at t-fire j.
# Mover ctx at t-fire j: (L_j, S_j, R_j).
# Need: L_j = L_k, S_j = (S_k+1)%2, R_j = R_k.

# S_j = (s0+j)%2 = (S_k+1)%2 = (s0+k+1)%2 → j ≡ k+1 (mod 2).

# But wait! There are OTHER non-mover steps at t besides the neighbor-fire step.
# In a sweep, between t-fire k and t-fire k+1, EVERY processor fires once
# (in a CW sweep: i+2, i+3, ..., n-1, 0, 1, ..., i, i+1
# where i+1 = t fires last in this half-sweep).
# So there are many non-mover steps at t in between!

# At each of these steps (proc p fires, p ≠ t), the context at t = (c_{left(t)}, c_t, c_{right(t)}).
# But only left(t) and right(t) changes affect this context.

# In phase k (J+K=1), exactly one of {left(t), right(t)} fires.
# So the context at t changes only when that neighbor fires.
# Before the neighbor fires: context = (L_k, (S_k+1)%2, R_k)
# After the neighbor fires: context = (L_k ± 1, (S_k+1)%2, R_k) or (L_k, (S_k+1)%2, R_k ± 1)

# In a CW sweep through phase k, the processors fire in order.
# If phase k is CW: procs fire as t+1, t+2, ..., n-1, 0, 1, ..., t-1, t
# where t fires last (at t-fire k+1).

# left(t) = t-1 fires just before t. right(t) = t+1 fires first.

# So in a CW sweep:
# right(t) fires FIRST (at the beginning of the sweep)
# left(t) fires LAST (just before t)

# In phase k = CW sweep:
# - If it's a right-fire phase: right(t) fires first. After that, context at t changes.
#   Then many procs fire without changing t's context.
#   Then left(t) fires just before t — but left doesn't fire in this phase (J+K=1, right fires).
#   Wait, (J,K)=(0,1): right fires once, left doesn't fire.
#   So: right fires early in the sweep. Context at t changes once at that point.
#   Before right fires: (L_k, S_after, R_k) — non-mover obs.
#   Hmm wait, what fires before right(t) in a CW sweep? Nothing — right(t) = t+1
#   fires first in the CW sweep (starting from t+1 going to t).
#   Actually it depends on the sweep structure.

# I think I need to reconsider. In a sweep cycle for a ring of size n:
# CW pass: 0, 1, 2, ..., n-1
# CCW pass: n-1, n-2, ..., 0
# Total length = 2n? No, that's for a full sweep with all procs firing once each way.

# For binary procs (fc=2), they fire once CW and once CCW.
# For ternary procs (fc=3), they fire once CW and twice in the other parts?
# Actually I'm overcomplicating this. Let me go back to the abstract argument.

print("="*70)
print("KEY FINDING: EC at t is blocked by S-parity flip")
print("="*70)
print()
print("At every t-fire step k: S_k = (s0 + k) % 2")
print("At every non-mover step in phase k: S = (S_k + 1) % 2 = (s0 + k + 1) % 2")
print("Since S_k and (S_k+1)%2 are always different,")
print("no mover context can match a non-mover context in the S-component")
print("IF we only consider the phase's own non-mover observations vs the")
print("bracketing t-fire observations.")
print()
print("BUT: non-mover context in phase k has S = (s0+k+1)%2 = S_{k+1}.")
print("So it matches the S-component of t-fire k+1 (and t-fire k-1).")
print("The question is whether the L and R components can also match.")
print()

# Let me reconsider. The non-mover observations in phase k have S = S_{k+1}.
# And the mover context at t-fire j has S = S_j.
# For a match: S_j = S_{k+1}, i.e., j = k+1 (mod 2) and same parity.
# Actually j must equal k+1 mod the S-period, but S alternates, so j ≡ k+1 (mod 2).

# Non-mover ctx at neighbor-fire in phase k: (L_k, S_{k+1}, R_k) [pre-fire L/R]
# But after the neighbor fires, ctx becomes different.
# If phase_seq[k] = 0 (left fires): post-fire ctx = ((L_k+1)%2, S_{k+1}, R_k)
# If phase_seq[k] = 1 (right fires): post-fire ctx = (L_k, S_{k+1}, (R_k+1)%2)

# And the mover context at t-fire k+1:
# L_{k+1} = L_k + left_in_phase[k] (mod 2)
# R_{k+1} = R_k + right_in_phase[k] (mod 2)
# So:
# If phase_seq[k] = 0: L_{k+1} = (L_k+1)%2, R_{k+1} = R_k
#   Post-fire non-mover ctx = ((L_k+1)%2, S_{k+1}, R_k) = (L_{k+1}, S_{k+1}, R_{k+1})
#   This EQUALS the mover context at t-fire k+1!
#   BUT: in a CW sweep, left(t) fires right before t, so there's no
#   non-mover step at t between left-fire and t-fire.

# If phase_seq[k] = 1: R_{k+1} = (R_k+1)%2, L_{k+1} = L_k
#   Post-fire non-mover ctx = (L_k, S_{k+1}, (R_k+1)%2) = (L_{k+1}, S_{k+1}, R_{k+1})
#   Again equals mover context at t-fire k+1!
#   In a CCW sweep, right(t) fires right before t.

# So the POST-fire non-mover context always equals the next mover context.
# The question is: is there a guaranteed non-mover step with that context?

# In a sweep: the firing neighbor fires adjacent to t in the sweep order.
# Specifically:
# - CW phase: left(t) fires just before t → no gap after left fires
# - CCW phase: right(t) fires just before t → no gap after right fires

# But what if the LEFT-fire phase is a CCW sweep?
# In CCW: ..., t+1, t, t-1, ...
# So right(t) fires just before t, then t fires, then left(t) fires.
# In a CCW phase where left fires (phase_seq = 0, (J,K) = (1,0)):
# left(t) fires AFTER t! Wait, that can't be — this phase is between t-fire k
# and t-fire k+1. The whole phase is between consecutive t-fires.
# t fires at step k, then the phase occurs, then t fires at step k+1.
# In a CCW sweep: after t fires, the sweep continues: t-1, t-2, ...
# left(t) = t-1 fires right AFTER t fires! Then the sweep continues.
# Eventually the sweep reverses (CCW → CW), and the CW sweep goes through
# ..., t-1, t — and t fires at step k+1.

# Wait, I need to think about sweep structure more carefully.
# A sweep cycle has the form: CW pass followed by CCW pass (or vice versa).

# CW pass: 0, 1, 2, ..., n-1  (each fires once)
# CCW pass: n-1, n-2, ..., 0  (each fires once)

# For binary procs: fc = 2 (once per pass) ✓
# For ternary: fc = 3 (NOT accounted for by just 2 passes)

# Hmm, ternary procs need to fire 3 times. In a sweep cycle, the standard
# structure might not be just CW+CCW. Let me look at the actual sweep
# structure for sub-threshold products.

# For ms=(2,2,2,3,3) at n=5:
# Product = 2*2*2*3*3 = 72 < 4*3^3 = 108
# Cycle length = ?? Actually for a sweep:
# CW: 0,1,2,3,4 (5 steps, each fires once)
# CCW: 4,3,2,1,0 (5 steps, each fires once)
# After 2 passes (10 steps): binary procs fired 2 times ✓
# Ternary procs fired 2 times (need 3). Not enough.

# So a pure CW+CCW sweep won't work for ternary.
# Need 3 passes: CW+CCW+CW or similar.
# CW: all fire once. CCW: all fire once. CW: all fire once.
# Total: 15 steps. Binary fired 3 times — but binary needs fc even!
# So binary would need to fire 4 times (2 CW + 2 CCW).

# Actually, the sweep cycle structure is more nuanced.
# From the project: cycle length = 3n-2 for the CUP construction,
# and different for different constructions.

# Let me look at this from the ABSTRACT side, forgetting sweep structure.
# The claim is that under the normalForm residual hypotheses,
# every phase has J+K=1 and fc(left)+fc(right)=fc(t).

# The S-parity argument shows that EC at t requires matching between
# non-mover phase k and mover phase j where j ≡ k+1 (mod 2).

# The PRE-fire non-mover context (at the neighbor-fire step) is:
# (L_k, S_{k+1}, R_k) — this is the non-mover observation.

# We need this to match a mover context at some t-fire j:
# (L_j, S_j, R_j) where S_j = S_{k+1} (so j ≡ k+1 mod 2).

# For match: L_j = L_k and R_j = R_k.

# L_j = (l0 + sum of left fires in phases 0..j-1) % 2
# L_k = (l0 + sum of left fires in phases 0..k-1) % 2
# R_j = (r0 + sum of right fires in phases 0..j-1) % 2
# R_k = (r0 + sum of right fires in phases 0..k-1) % 2

# L_j = L_k iff sum of left fires in phases k..j-1 is even (assuming j > k)
# R_j = R_k iff sum of right fires in phases k..j-1 is even

# Since each phase has exactly one of {left, right} firing:
# sum of left fires in k..j-1 = number of left-fire phases in k..j-1
# sum of right fires in k..j-1 = (j-k) - (number of left-fire phases in k..j-1)

# For both to be even: both the number of left-fire phases and right-fire phases
# in k..j-1 must be even. Since their sum is j-k, we need j-k even.
# Combined with j ≡ k+1 (mod 2) → j-k is odd. CONTRADICTION!

# j-k must be both ODD (from S-parity) and EVEN (from L/R parity). Impossible!

# Wait, let me double-check. j ≡ k+1 (mod 2) means j-k ≡ 1 (mod 2), so j-k is odd.
# But we need the number of left-fire phases and right-fire phases in k..j-1 to both be even.
# Their sum is j-k, which is odd. An odd number cannot be the sum of two even numbers.
# So it's IMPOSSIBLE for both L_j = L_k and R_j = R_k simultaneously with S_j = S_{k+1}.

# THEREFORE: EC at t is impossible from the pre-fire non-mover observations!

# Now what about the POST-fire non-mover observations?
# We showed post-fire ctx = (L_{k+1}, S_{k+1}, R_{k+1}) = mover ctx at t-fire k+1.
# For this to be observable as a non-mover step, we need at least one step
# after the neighbor fires and before t fires where mover ≠ t.

# In a sweep: this depends on whether the neighbor fires adjacent to t.
# But in a general cycle (not necessarily sweep), there might be other procs
# firing between the neighbor and t.

# HOLD ON. The problem says this is a SWEEP cycle. In a sweep:
# t and its neighbors fire in a specific order within each sweep direction.

# But more fundamentally: even if post-fire ctx is unobservable at t,
# the argument above shows PRE-fire non-mover observations at t NEVER
# match any mover observation at t. Combined with post-fire being the only
# other non-mover observation type, and post-fire matching t-fire k+1,
# EC at t comes down to: is the post-fire context observable?

# And we noted: in a sweep, it might not be. But in a NON-sweep cycle...
# this is the sweep branch. So EC at t is indeed problematic.

# CONCLUSION: EC must come from a DIFFERENT processor than t.
# The sorry needs to find EC somewhere in the system, not specifically at t.

print("="*70)
print("PARITY OBSTRUCTION THEOREM (proved)")
print("="*70)
print()
print("Theorem: Under the normalForm residual hypotheses (J+K=1 for all phases,")
print("fc(left)+fc(right)=fc(t)), the PRE-fire non-mover context at proc t")
print("can NEVER match any mover context at proc t.")
print()
print("Proof:")
print("  Non-mover ctx in phase k (at neighbor-fire step): (L_k, S_{k+1}, R_k)")
print("  Mover ctx at t-fire j: (L_j, S_j, R_j)")
print("  For S-match: j ≡ k+1 (mod 2), so j-k is odd.")
print("  For L-match: #left-fire phases in [k..j-1] must be even.")
print("  For R-match: #right-fire phases in [k..j-1] must be even.")
print("  Sum of these counts = j-k (odd). Two even numbers sum to even. Contradiction.")
print()
print("Corollary: EC at processor t requires additional non-mover observations")
print("beyond the neighbor-fire steps (e.g., post-fire observations, or observations")
print("from OTHER processors firing in the phase).")
print()

# Now: what about EC at left(t) or right(t)?
# These are also binary. The same S-parity argument applies there too!
# At any binary processor p, the mover and non-mover observations differ
# in the S-component (c_p) because binary processors toggle every fire.

# Wait, that's not quite right. At proc p, c_p changes when p fires (mover step)
# and stays the same otherwise. So:
# - Mover observation: c_p = current value (about to change)
# - Non-mover observation: c_p = whatever it is

# Between consecutive p-fires, c_p is constant. Specifically:
# After p fires at step a: c_p = v (new value)
# Before p fires at step b: c_p = v (same, hasn't fired)
# At step b (p fires): c_p = v

# So non-mover observations between fires a and b see c_p = (old+1)%2.
# And the mover observation at fire b sees c_p = (old+1)%2 (same!).
# And the mover observation at fire a sees c_p = old.

# So for binary p: mover observation at fire k sees c_p = (init + k) % 2.
# Non-mover observations between fire k and fire k+1 see c_p = (init + k + 1) % 2.
# The non-mover c_p matches NEXT mover c_p and differs from current mover c_p.

# For EC at p: need same (L, S, R) at mover and non-mover step.
# The S (= c_p) at non-mover step between fires k and k+1 is S_{k+1}.
# For L-match: c_{left(p)} must match between the non-mover step and some mover step j.
# And R-match similarly.

# For binary proc p with binary neighbors: the same parity argument applies.
# The neighbors' values change when they fire. If we have the "tight phase" structure
# (each neighbor fires exactly once per p-fire gap), the same odd/even parity
# argument blocks EC at p.

# But: is the "tight phase" structure true for left(t) and right(t)?
# We know fc(left(t)) + fc(right(t)) = fc(t), all even ≥ 2.
# The phases of t are well-characterized.
# But what about the phases of left(t)? The phases of left(t) involve
# left(left(t)) and right(left(t)) = t.

# At left(t) = i (binary):
# Between consecutive i-fires, t fires some number of times, and left(i) fires some.
# We DON'T have the same tight structure for i's phases.

# So EC at left(t) might involve a different mechanism.
# And left(left(t)) is likely ternary (not binary), which breaks the S-parity argument.

print("="*70)
print("WHERE DOES EC ACTUALLY COME FROM?")
print("="*70)
print()
print("EC at t: blocked by parity obstruction (proved above).")
print("EC at left(t) = i: left(i) is ternary (for n≥5 with exactly 3 binary).")
print("  Context at i includes c_{left(i)} which is ternary.")
print("  The S-parity argument doesn't directly block EC at i.")
print("EC at right²(i): right(right²(i)) is ternary. Similar.")
print("EC at ternary procs: more states, easier for pigeonhole.")
print()
print("The domino argument should target EC at the BOUNDARY binary procs")
print("(i or right²(i)) where one neighbor is ternary.")
