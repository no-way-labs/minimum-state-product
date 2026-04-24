"""
Definitive proof: why Approach D (direct) FAILS and Approach C (rotation) is NECESSARY.

The core issue:
- Interior TernaryPhases have a < s, so h_phase_le1 applies
- There are fc(t)-1 interior phases (between min and max t-fire)
- fc(t)-1 phases each with J+K <= 1 gives sum <= fc(t)-1
- But we need fc(L) + fc(R) <= fc(t), not fc(t)-1

The missing "+1" comes from the wrap-around phase (last t-fire to first t-fire cyclically).
This phase IS NOT a TernaryPhase (because a > s), so h_phase_le1 doesn't apply.

Approach C (rotation) fixes this by rotating so that:
- t fires at step 0
- ALL fc(t) phases become TernaryPhases (a < s)
- h_phase_le1 applies to all of them
- sum <= fc(t)

Approach D would need to separately prove J+K <= 1 for the wrap-around,
which requires re-proving the mechanism arguments (BothEvenReturn, ToggleFR, etc.)
for intervals that cross the cycle boundary. This is equivalent to building
CyclicTernaryPhase from scratch — more work than rotation.

HOWEVER: there's a SUBTLETY with rotation. After rotation:
- The good cycle gc' = gc.rotate(k) has a DIFFERENT config list
- We need to prove gc' satisfies all GoodCycle properties
- We need h_phase_le1 to hold for gc' (which needs hall_normal for gc')
- The rotation must preserve the "all phases are normal form" property

This means we need:
  hall_normal_gc' : ∀ phase : TernaryPhase gc' t, isNormalFormGap gc' t phase

which requires:
  1. gc'.moverAt i = gc.moverAt ((i + k) % CL)
  2. gc'.intervalFireCount p a b = gc.intervalFireCount_cyclic p a b (relative to rotation)
  3. The mechanism-triggering predicates transfer

This is MORE work than just proving the wrap-around phase satisfies J+K <= 1.

WAIT. Let me reconsider. The ACTUALLY cleanest approach is:

APPROACH E: Prove h_sparse directly by contradiction WITHOUT phase decomposition.

h_sparse needs: fc(L) + fc(R) <= fc(t).

Proof by contradiction: assume fc(L) + fc(R) > fc(t).

Step 1: From exists_consecutive_tfire_with_zero_qfire (already proved!), since
  fc(L) + 2 <= fc(t) is NOT given (we want the opposite), we can't directly
  use that lemma.

BUT: h_phase_le1 gives J+K <= 1 for each TernaryPhase. The existing
ifc_q_ge_ifc_t_of_all_consec_pos shows that if every consecutive t-pair
has ifc(q) >= 1, then ifc(q, s_min, s_max) >= ifc(t, s_min, s_max) = fc(t)-1.

So for EACH of L and R:
  ifc(L, s_min, s_max) + ifc(R, s_min, s_max)
  >= sum over fc(t)-1 interior phases of (J_i + K_i)
  >= ... (need each >= 1)

Wait, we need each phase to have J+K >= 1 as well. normalForm gives:
  J=0 -> K=1, K=0 -> J=1. So J+K >= 1.

So: sum over fc(t)-1 interior phases of (J_i + K_i) >= fc(t)-1.

And: ifc(L, s_min, s_max) + ifc(R, s_min, s_max) = this sum.

Plus boundary: ifc(L, 0, s_min) + ifc(R, 0, s_min) >= 0
               ifc(L, s_max+1, CL) + ifc(R, s_max+1, CL) >= 0

So fc(L) + fc(R) >= fc(t) - 1.

If fc(L) + fc(R) = fc(t) - 1, then the boundary contributions are 0,
meaning no L or R fires before s_min or after s_max.

APPROACH F: Prove wrap-around phase has J+K <= 1 using a DIFFERENT argument.

The wrap-around phase covers [0, s_min) ∪ (s_max, CL). If J+K >= 2 in this
region, we can construct an entry conflict by finding two fires that bracket
a t-fire... but this is complicated.

Actually, the SIMPLEST approach is the one the existing code already hints at:

APPROACH G: Bypass the wrap-around entirely.

The existing ifc_q_ge_ifc_t framework already proves:
  fc(L) >= fc(t) - 1  (if every interior phase has L-fire >= 1)
  fc(R) >= fc(t) - 1  (if every interior phase has R-fire >= 1)

But that gives fc(L) + fc(R) >= 2(fc(t)-1), which is the OPPOSITE direction.

We need <= not >=.

OK, I think the cleanest path really IS:

APPROACH H: Direct proof using the EXISTING ifc_q_ge_ifc_t framework
but applied to fc(L) + fc(R) as a combined quantity.

Key insight: the fc(t)-1 interior phases each have J+K <= 1 (from h_phase_le1).
The interior sum = sum_{i=0}^{fc(t)-2} (J_i + K_i) <= fc(t) - 1.
The boundary sum = (wrap_J + wrap_K) >= 0.
So fc(L) + fc(R) = interior_sum + boundary_sum >= interior_sum.

We need to show fc(L) + fc(R) <= fc(t), i.e., interior_sum + boundary_sum <= fc(t).

Since interior_sum <= fc(t) - 1, we need boundary_sum <= 1.

CAN WE PROVE boundary_sum <= 1?

The boundary consists of steps [0, s_min) and (s_max, CL).
In these steps, t does NOT fire (since s_min is the first t-fire and
s_max is the last t-fire).

So in the boundary region, t is a non-mover at every step. If L or R
fires in this region, it creates a situation where t has been continuously
non-moving since s_max (or before s_min).

Key observation: the boundary region [0, s_min) ∪ (s_max, CL) is exactly
the wrap-around phase. If we could show it satisfies the same normalForm
constraint (J+K <= 1 under h_phase_le1 + normalForm), we'd be done.

The wrap-around phase IS a TernaryPhase if we "close" it:
- t fires at s_max (the last fire) and at s_min (the first fire, cyclically)
- Between s_max and s_min (cyclically), t doesn't fire
- The nonmover step is s_max + 1 (or 0 if s_max = CL - 1)

This IS a cyclic TernaryPhase: a = s_max, s = s_min (cyclically).

In the rotated cycle (rotation by s_min), this becomes:
a' = s_max - s_min (> 0), s' = CL (or equivalently, s' = 0 + CL).

After rotation, s' = CL > a' = s_max - s_min. So a' < s' = CL.
THIS IS A VALID TernaryPhase in the extended list.

But we can't index CL in gc.configs. We need configs[CL] which doesn't exist.

THE ACTUAL FIX: After rotation, the last phase goes from the last t-fire
step (in rotated indices) to CL. But the TernaryPhase needs s < CL.

RESOLUTION: In the rotated cycle, the last t-fire is at some step s'_{fc-1} < CL.
The "phase" after it contains steps s'_{fc-1}+1, ..., CL-1.
The "mover step" that ends this phase is step 0 (cyclically), which is step CL.
But CL is NOT a valid step index.

HOWEVER: we don't need the mover step to be a valid index. We just need:
1. t doesn't fire in (s'_{fc-1}, CL) -- true since s'_{fc-1} is last t-fire
2. The J and K counts in this interval are well-defined
3. J+K <= 1 for this interval

For (3), we can prove J+K <= 1 by the SAME mechanism arguments, using:
- The nonmover step at s'_{fc-1}+1 (if it exists)
- The fact that t fires at step 0 = step CL (cyclically), which gives
  the mover context

The mover step for the wrap phase IS step s_min (= step 0 in rotated coords).
In the original coords, step s_min has gc.moverAt(s_min) = t.
After rotation, this is step 0 with gc'.moverAt(0) = t.

So the wrap phase CAN be expressed as: a = s'_{fc-1}, s = 0.
But a > 0 > s doesn't work.

ALTERNATIVELY: express it as a = s'_{fc-1}, with the understanding that
the phase extends to the cyclic return to step 0.

OK, enough deliberation. Let me just figure out what MINIMAL new Lean
infrastructure is needed.
"""

print("=" * 70)
print("DEFINITIVE ANALYSIS OF THE CYCLIC PHASE GAP")
print("=" * 70)

print("""
THE GAP: In AllNormalFormFalse2.lean line 1129, we need:
  fc(L) + fc(R) <= fc(t)

AVAILABLE:
  h_phase_le1: For every TernaryPhase (a < s), J + K <= 1
  intervalFireCount_split: ifc additive over sub-intervals
  fireCount_eq_intervalFireCount_full: fc(p) = ifc(p, 0, CL)
  normalForm_gap_constraint: J=0 -> K=1, K=0 -> J=1 (so J+K >= 1)

MISSING:
  Phase decomposition: fc(p) = sum over fc(t) phases of ifc(p, a_i, s_i)

THE FUNDAMENTAL ISSUE:
  TernaryPhase requires a.val < s.val.
  With fc(t) fires at positions s_0 < s_1 < ... < s_{fc-1}:
  - Interior phases: (s_0, s_1), (s_1, s_2), ..., (s_{fc-2}, s_{fc-1})  -- fc-1 phases
  - Wrap phase: (s_{fc-1}, CL) ∪ [0, s_0)  -- 1 phase (CANNOT be TernaryPhase)

  Interior sum of (J+K): each <= 1, so sum <= fc-1.
  Wrap (J+K): unknown bound.
  Total: fc(L) + fc(R) <= fc-1 + wrap(J+K).
  Need: wrap(J+K) <= 1 to get fc(L) + fc(R) <= fc.

APPROACH: PROVE WRAP(J+K) <= 1 DIRECTLY.

The wrap-around phase has:
  wrap_J = ifc(L, 0, s_0) + ifc(L, s_{fc-1}+1, CL)
  wrap_K = ifc(R, 0, s_0) + ifc(R, s_{fc-1}+1, CL)

In this region, t does not fire. The same normalForm constraint applies
(if both even -> mechanism, if one-sided >= 2 -> mechanism, etc.)
because the mechanism proofs only need:
  (a) t fires at the endpoint (TRUE: t fires at s_{fc-1} and s_0 cyclically)
  (b) t doesn't fire between (TRUE: no t fires in [s_{fc-1}+1, CL) or [0, s_0))
  (c) The interval has a definite "start" nonmover step and "end" mover step

For (c), the wrap phase has mover step s_0 (where t fires) and the nonmover
region is the wrap interval. But s_0 < s_{fc-1}, so a = s_{fc-1}, s = s_0
gives a > s -- invalid for TernaryPhase.

SOLUTION: CONSTRUCT A VALID TernaryPhase FOR THE WRAP.

If s_{fc-1} + 1 < CL (there exists a step after the last t-fire):
  Let a_wrap = CL - 1 (or any step in (s_{fc-1}, CL) that's a nonmover for t)
  This is only valid if a_wrap < s_0... but a_wrap = CL - 1 >= s_0.

If s_0 > 0 (there exists a step before the first t-fire):
  There must be a step between s_{fc-1} and s_0 (cyclically) that is not a t-fire.
  One such step is s_{fc-1} + 1 (mod CL) if s_{fc-1} + 1 != s_0.
  But if s_{fc-1} + 1 = CL and s_0 = 0, then the wrap has zero non-t-fire steps.
  In that case, wrap_J + wrap_K = 0 <= 1. Done.

If s_{fc-1} + 1 < CL and s_0 > 0:
  The wrap has nonzero steps. We need to show J+K <= 1.
  But these steps might span both [s_{fc-1}+1, CL) and [0, s_0).

HERE IS THE KEY INSIGHT:

By rotation, we can always ensure the wrap phase is a SUFFIX of the list:
  Rotate by s_0 -> t fires at step 0.
  The wrap phase becomes [s'_{fc-1}+1, CL) where s'_{fc-1} < CL.
  This IS a contiguous interval with start < end!

In the rotated cycle, the wrap phase is just an ordinary interval (a', CL)
where a' = s'_{fc-1}. It doesn't cross the boundary.

Now, the wrap phase has:
  - t fires at step 0 (= step CL cyclically) -- this is the "mover step"
  - t fires at step s'_{fc-1} -- this is the start
  - t doesn't fire in (s'_{fc-1}, CL)

If the wrap has no steps (s'_{fc-1} = CL - 1), then J+K = 0 <= 1. Done.

If the wrap has steps, we need a nonmover step. Take a' = s'_{fc-1} + 1
or any step in (s'_{fc-1}, CL). Then:

WE CANNOT FORM A TernaryPhase because the mover step (step CL = step 0)
is NOT > a'. In the list indexing, CL is out of bounds, and 0 < a'.

BUT: in the rotated cycle, step 0 IS step CL wrapped. The configs satisfy
  configs[0] = configs[CL] (cyclic property of good cycle: step CL leads back to step 0).

So the value preservation argument still holds:
  t doesn't fire in (s'_{fc-1}, CL), and then t fires at step 0 (= step CL).
  The config at step CL (= step 0) is gc'.configs[0].
  The config at any step k in (s'_{fc-1}, CL) has the same t-value as
  gc'.configs[s'_{fc-1}+1] (since t doesn't fire between).

FOR THE ENTRY CONFLICT ARGUMENT:
  If the wrap has J+K >= 2, we'd need step indices a < s with t not firing
  in [a, s). But a is in (s'_{fc-1}, CL) and s = 0, giving a > s.

THIS IS THE FUNDAMENTAL OBSTACLE. The mechanism proofs use a < s.

CLEAN RESOLUTION: Prove a SINGLE new lemma:

LEMMA (CyclicPhaseEC):
  If t fires at steps a' and b' with a' > b' (cyclically: b' is the NEXT fire
  after a', wrapping around), and J+K >= 2 in the cyclic interval (a', b'),
  then hasEntryConflict gc.

PROOF: The cyclic interval (a', b') decomposes into [a'+1, CL) ∪ [0, b').
  The J fires of L are spread across this interval.
  The K fires of R are spread across this interval.
  If both even -> BothEvenReturn still works (parity is the same cyclically).
  If one-sided >= 2 -> ToggleFR still works.
  If mixed -> the cross-neighbor EC still works.

The mechanism proofs depend ONLY on:
  1. Value preservation of t between two steps (t doesn't fire between)
  2. Binary parity of L/R (even fires => same value)
  3. Two distinct nonmover contexts for binary dichotomy

For (1): t doesn't fire in (a', CL) ∪ [0, b'), so t's value is preserved
  from step a'+1 to step b' (going through the cycle boundary). This uses
  configVal_eq_of_noFire_between applied twice and the cyclic property:
    config[CL] = config[0].

For (2): The parity of L/R fires in the wrap interval is the same as
  in any linear interval. Binary parity doesn't care about linearity.

For (3): We need two steps in the interval where L (or R) has different
  values. These steps can be on different sides of the boundary.
  The value preservation still holds because t doesn't fire between them.

CONCLUSION: The mechanism arguments transfer to the wrap-around phase
with ONE additional lemma: configVal_eq_of_cyclic_noFire.

FINAL CLEAN APPROACH:

1. Prove cyclic_configVal_eq: if t doesn't fire in (a, CL) ∪ [0, b),
   then config[a+1](t) = config[b](t).

2. Prove cyclic_intervalFireCount_even: the parity of fires in a cyclic
   interval equals ifc(p, a+1, CL) + ifc(p, 0, b).

3. Use these to prove wrap_phase_ec: if J+K >= 2 in the wrap, then EC.

4. Then: wrap(J+K) <= 1, so fc(L)+fc(R) <= (fc(t)-1) + 1 = fc(t).

LEAN INFRASTRUCTURE NEEDED:
  ~ 40 lines: cyclic_configVal_eq
  ~ 10 lines: wrap_J_plus_K_le_1 (applying mechanisms to wrap)
  ~ 20 lines: the final inequality

Total: ~70 lines of new Lean code, NO gc.rotate needed.
""")

# Verify the "+1 gap" computationally
print("=" * 70)
print("VERIFYING THE +1 GAP")
print("=" * 70)

def cup2_mw(n):
    return list(range(n)) + list(range(n-2, 0, -1)) + list(range(n))

for n in [5, 7, 9, 11]:
    mw = cup2_mw(n)
    CL = len(mw)
    print(f"\nn={n}, CL={CL}:")
    for t in range(n):
        ts = [i for i, m in enumerate(mw) if m == t]
        fc_t = len(ts)
        if fc_t < 2:
            continue

        s_min = ts[0]
        s_max = ts[-1]

        # Interior phases
        interior_phases = []
        for i in range(fc_t - 1):
            a, s = ts[i], ts[i+1]
            interior_phases.append((a, s))

        left_t = (t-1) % n
        right_t = (t+1) % n

        int_JK = 0
        for a, s in interior_phases:
            J = sum(1 for k in range(a+1, s) if mw[k] == left_t)
            K = sum(1 for k in range(a+1, s) if mw[k] == right_t)
            int_JK += (J + K)

        # Wrap
        wrap_J = sum(1 for k in range(0, s_min) if mw[k] == left_t)
        wrap_J += sum(1 for k in range(s_max+1, CL) if mw[k] == left_t)
        wrap_K = sum(1 for k in range(0, s_min) if mw[k] == right_t)
        wrap_K += sum(1 for k in range(s_max+1, CL) if mw[k] == right_t)

        fc_L = sum(1 for m in mw if m == left_t)
        fc_R = sum(1 for m in mw if m == right_t)

        print(f"  t={t}: fc(t)={fc_t}, s_min={s_min}, s_max={s_max}")
        print(f"    Interior: {fc_t-1} phases, sum(J+K)={int_JK} <= {fc_t-1}")
        print(f"    Wrap: J={wrap_J}, K={wrap_K}, J+K={wrap_J+wrap_K}")
        print(f"    fc(L)={fc_L}, fc(R)={fc_R}, fc(L)+fc(R)={fc_L+fc_R}")
        print(f"    int + wrap = {int_JK + wrap_J + wrap_K} = fc(L)+fc(R) = {fc_L+fc_R} CHECK: {int_JK + wrap_J + wrap_K == fc_L + fc_R}")
        print(f"    NEED: wrap(J+K)={wrap_J+wrap_K} <= 1? {wrap_J+wrap_K <= 1}")

print("\n" + "=" * 70)
print("RANDOM STRESS: wrap J+K <= 1 when each interior phase has J+K <= 1?")
print("=" * 70)
print("NOTE: This is NOT necessarily true for arbitrary mover words.")
print("It IS true under the normalForm constraint + mechanism arguments.")
print("The computation below just shows the wrap values empirically.")

import random
total = 0
wrap_le1 = 0
for seed in range(1000):
    rng = random.Random(seed)
    n = rng.randint(5, 12)
    CL = rng.randint(n+2, 4*n)
    mw = [rng.randint(0, n-1) for _ in range(CL)]
    t = rng.randint(0, n-1)
    ts = [i for i, m in enumerate(mw) if m == t]
    if len(ts) < 2: continue

    fc_t = len(ts)
    left_t = (t-1) % n
    right_t = (t+1) % n

    s_min, s_max = ts[0], ts[-1]

    # Check interior J+K <= 1 for each phase
    all_le1 = True
    for i in range(fc_t - 1):
        a, s = ts[i], ts[i+1]
        J = sum(1 for k in range(a+1, s) if mw[k] == left_t)
        K = sum(1 for k in range(a+1, s) if mw[k] == right_t)
        if J + K > 1:
            all_le1 = False
            break

    if not all_le1:
        continue  # Only test cases where interior phases have J+K <= 1

    total += 1

    wrap_J = sum(1 for k in range(0, s_min) if mw[k] == left_t)
    wrap_J += sum(1 for k in range(s_max+1, CL) if mw[k] == left_t)
    wrap_K = sum(1 for k in range(0, s_min) if mw[k] == right_t)
    wrap_K += sum(1 for k in range(s_max+1, CL) if mw[k] == right_t)

    if wrap_J + wrap_K <= 1:
        wrap_le1 += 1
    else:
        # This is expected! Random mover words don't satisfy normalForm.
        pass

print(f"Cases where ALL interior phases have J+K <= 1: {total}")
print(f"  Of those, wrap J+K <= 1: {wrap_le1}/{total}")
print(f"  (Note: wrap J+K > 1 is EXPECTED for random words without normalForm)")

print("""
FINAL ANSWER:

For the Lean proof, the cleanest approach is:

1. DO NOT build gc.rotate infrastructure (too much overhead).

2. Instead, prove the wrap-around phase has J+K <= 1 by showing
   the mechanism arguments (BothEvenReturn, ToggleFR, etc.)
   extend to cyclic intervals.

3. The key new lemma is cyclic value preservation:
   If t doesn't fire in steps (s_max, CL) ∪ [0, s_min),
   then config(s_max+1)(t) = config(s_min)(t).

4. With this, BothEvenReturn and ToggleFR apply to the wrap phase
   exactly as they do to interior phases.

5. Then: wrap(J+K) <= 1, giving fc(L) + fc(R) <= fc(t).

LEAN CODE: ~70 lines of new infrastructure.
""")
