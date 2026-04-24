#!/usr/bin/env python3
"""
Investigate whether the third binary processor makes the sorry case impossible.

Setup: n ≥ 9, t ternary with binary neighbors L and R.
h3bin: ≥ 3 binary processors in the ring.
sub-threshold: product < 4·3^(n-2).

The third binary processor b ∉ {L, R, t}. Where is it on the ring?
With ≥ 3 binary total and L, R already binary: b is somewhere else.

Key constraint: b has m_b = 2. In a good cycle, fc(b) must be even (≥2).

In the sorry phase (full ring walk from R to L):
  b fires exactly once (it's somewhere in the walk).
  So fc(b) in sorry phase = 1 (odd).
  Over the full cycle: fc(b) must be even.
  So other phases contribute odd fires for b.

With h3bin: there are ≥ 3 binary. Let binaries be L, R, and b_1, ..., b_k (k ≥ 1).
Each binary fires even total. Each fires once in the sorry phase (odd).
Other phases: each binary fires odd total.

Under J+K ≤ 1 per non-sorry phase: how do other binaries fire?
b_i is NOT L or R. So b_i's fires aren't counted by J or K.
b_i can fire any number of times per phase.

But the fire count of b_i is constrained by: fc(b_i) even, fc(b_i) ≥ 2.
1 fire in sorry phase → ≥ 1 fire in other phases.

This doesn't directly contradict anything. Let me think harder.

ALTERNATIVE: Use the sub-threshold product constraint.

sub-threshold: product = ∏ m_i < 4·3^(n-2).
With ≥ 3 binary and rest ternary: product = 2^b · 3^(n-b) where b ≥ 3.
For b = 3: product = 8·3^(n-3).
Threshold: 4·3^(n-2) = 12·3^(n-3).
8·3^(n-3) < 12·3^(n-3). ✓ sub-threshold.

Now: the cycle length CL ≤ product = 8·3^(n-3) (for b=3).

In the sorry phase, n steps are used (one per processor).
With fc(t) phases, minimum CL ≥ n · (minimum phase length).
But phases can have different lengths.

Actually, the KEY might be that the sorry phase uses n steps, and with the
binary parity constraints + J+K ≤ 1, we can bound fc(t) and show a
contradiction with the sub-threshold product.

But this seems complex. Let me try a different angle.

APPROACH: Use ec_caseC_RL at a CROSS-PHASE boundary.

In the sorry phase (phase i): R fires at step a, L fires at step fL = a+n-2.
Between fR = a and fL: movers are R, RR, ..., LL, L. LL fires.
ec_caseC_RL(fR, fL) needs no LL in [fR, fL). Fails.

But what about ACROSS the phase boundary?
At step s = a+n-1: t fires (end of sorry phase).
At step s+1: start of next phase. moverAt(s+1) is adj to t.

If moverAt(s+1) = L: next phase starts with L.
At step s+1, L fires. boundary at L = (LL_new, L_new, t_new).
This is a mover triple for L.

In the sorry phase, at step a: L is non-mover. boundary = (LL_old, L_old, t_new).
(t_new because t fired at step a-1, before the sorry phase. t_val doesn't change
during the sorry phase, then t fires again at step s, changing to t_new2.)

Wait, let me be more careful.
- Step a-1: t fires (previous phase end). t_val changes from t_prev to t_new.
- Step a: R fires. L is non-mover. L boundary = (LL_old, L_old, t_new).
- Steps a+1 to a+n-4: intermediate fires. L is non-mover.
  L boundary = (LL_old, L_old, t_new) until LL fires at step a+n-3.
  After LL fires: L boundary = (LL_new, L_old, t_new).
- Step a+n-2 (= fL): L fires. L boundary = (LL_new, L_old, t_new). Mover triple.
- Step a+n-1 (= s): t fires. t_val changes from t_new to t_new2.
- Step s+1: next phase starts. If L fires: L boundary = (LL_new, L_new, t_new2).
  Different from sorry phase mover triple (LL_new, L_old, t_new) in t component.

So the cross-phase L fire doesn't match the sorry-phase L fire.
EC at L requires matching across ALL three components.

Hmm. What if L is non-mover at step s (t fires)?
L boundary at step s = (LL_new, L_new, t_new). L_new because L fired at fL.
L's mover triple at fL = (LL_new, L_old, t_new). L_old ≠ L_new (L fired).
So no EC between step s (non-mover) and step fL (mover) at L.

What about OTHER phases where L is non-mover?
In a non-sorry phase where L doesn't fire: L_val stays constant.
L boundary = (LL_val, L_val, t_val).
For EC with L's mover triple (LL_new, L_old, t_new):
need LL_val = LL_new, L_val = L_old, t_val = t_new.
t_new is t's value during the sorry phase. In a different phase, t_val
could be different (t fires between phases).

THIS IS HARD TO TRACK without the full cycle.

Let me take yet another angle. The sorry cases in the Lean proof might
be closable by a much simpler observation that I'm missing.

Let me re-read the sorry at line 1077 one more time:
  left³(t) fires in [a, fLL) where fR = a, fL > a,
  last LL at fL-1, first LL at fLL.

The interval [a, fLL): moverAt(a) = R. Between a and fLL, no LL fires
(fLL is the first). No L fires (fL > fLL > any step in [a, fLL)).
What movers CAN fire? Not t, not L, not LL. So movers ∈ {R, RR, other non-{t,L,LL} procs}.

Under all-adjacent movers: starting from R, the walk goes outward.
R → RR → right³t → ... reaching left³(t) before reaching LL.

But left³(t) = (t-3)%n. LL = (t-2)%n. For left³(t) to fire before LL,
the walk must reach left³(t) before LL. On the ring, going from R in the
CW direction: R, RR, ..., left³(t), LL, L. So left³(t) IS reached before LL.

The length of the walk from R to left³(t) is n-4 steps (for n=9: 5 steps).
The walk: R(2), RR(3), 4, 5, 6, 7 (=left³(t) for n=9, t=1).

At step a+5 (for n=9): left³(t) = 7 fires. Then next mover at a+6 is
adj to 7: {6, 8}. 8 = LL. So moverAt(a+6) = LL = fLL.

So the interval [a, fLL) = [a, a+6) = {a, a+1, a+2, a+3, a+4, a+5}.
Movers: R(2), RR(3), 4, 5, 6, 7.
left³(t) = 7 fires at step a+5 (last step of interval).
THIS IS ALWAYS THE CASE: in the ring walk from R to LL, left³(t)
fires as the LAST processor before LL.

So fL3 (first left³(t) fire in [a, fLL)) is at step a+(n-4) = a+5 (for n=9).
The interval [a, fL3) = [a, a+5) has movers R, RR, 4, 5, 6.
left³(t) doesn't fire in [a, fL3). That's the no-left³(t) case, which
the code ALREADY HANDLES (line 1059-1074)!

WAIT: unless left³(t) fires EARLIER in the phase, before the walk reaches it.
Can left³(t) fire before the walk reaches it? Only if some OTHER walk
pattern brings a mover to left³(t) position.

Under all-adjacent movers: starting from R, the walk builds step by step.
Each new mover is adjacent to the previous. The walk must go through
RR, then right³(t), etc., in order. It CAN'T skip to left³(t) without
going through all intermediate processors.

But: could a processor fire TWICE? E.g., R fires, RR fires, R fires again
(toggle back), RR fires again, etc. In this case, the walk "oscillates"
near R without progressing toward left³(t).

If the walk oscillates: does left³(t) fire? Only when the walk reaches
position left³(t) on the ring. The walk starts at R and can only extend
one position per step (ring-adjacent constraint). So the walk must traverse
all intermediate positions to reach left³(t).

BUT: the sorry condition says left³(t) fires in [a, fLL). If the walk
oscillates near R, it might never reach left³(t) in the interval [a, fLL).
In that case, left³(t) doesn't fire in [a, fLL) → no sorry (handled by
the existing code).

The sorry case specifically requires left³(t) to fire. For that, the walk
must reach left³(t). But the walk can only progress by one ring position
per step. To reach left³(t) from R: need n-4 forward steps.

Any backward steps (re-visiting a position) add to the total steps but
don't progress. So the walk needs AT LEAST n-4 steps to reach left³(t).
The interval [a, fLL) has exactly n-3 steps (from a to fLL-1 inclusive).
left³(t) fires at fLL-1 (the step just before LL fires).
So fL3 = fLL - 1 at the latest.

But fL3 could be earlier if the walk reaches left³(t) earlier (with some
oscillation). In that case, left³(t) fires before the walk reaches LL.

CRUCIAL OBSERVATION: If left³(t) fires at step fL3 < fLL - 1:
  Then there's a gap between fL3 and fLL.
  In this gap: no left³(t) fire (it already fired), no LL fire (first at fLL).
  So the code's existing mk_ec at LL uses the step after fL3 as non-mover.
  WAIT: the code checks for left³(t) in [a, fLL). If fL3 < fLL-1:
  left³(t) fires at fL3 in [a, fLL). The sorry triggers.
  But the code then tries EC at left³(t)... no, the sorry is about
  left³(t) firing in [a, fLL), not about a gap.

Let me re-read: line 1055 says "by_cases hnoL3 : ∀ j, fR.val ≤ j.val → j.val < fLL.val → moverAt j ≠ left³(t)".
  If no left³(t) in [a, fLL): EC at LL (lines 1059-1074). DONE.
  If left³(t) fires in [a, fLL): sorry (line 1077).

In the sorry case: left³(t) fires somewhere in [a, fLL).

Now can we do mk_ec at left³(t)? Find first left³(t) fire (fL3) in [a, fLL).
Try EC at left³(t) between fL3 and a.
Need: no left⁴(t), left³(t), LL in [a, fL3).
  No left³(t): fL3 is first. ✓
  No LL: fLL > fL3. ✓ (LL hasn't fired yet)
  left⁴(t): case split.
    If no: EC at left³(t). DONE.
    If yes: continue induction.

This induction eventually reaches the mover at step a (which is R).
The induction depth is at most n-4 (from left³(t) to R on the ring).

At the FINAL level: checking if left^(n-2)(t) = RR fires in [a, fRR_first).
RR needs to fire in [a, first_fire(right³(t))).
moverAt(a) = R. moverAt(a+1) adj to R: could be RR.
If moverAt(a+1) = RR: RR fires at step a+1. first_fire(RR) = a+1.
Interval [a, a+1) = {step a}. moverAt(a) = R.
left(RR) = R fires at step a.
So R fires in [a, a+1). The EC construction at RR needs no left(RR)=R fire.
R fires at a. FAILS.

So the EC at RR between fRR and a FAILS because R fires at a.

BUT: can we use a DIFFERENT non-mover step for the EC?
Instead of step a, use step a+2 (AFTER RR fires at a+1).
At step a+2: mover = right³(t) (next in the walk). RR is non-mover. ✓
boundary at RR at step a+2: (R_new, RR_new, right³(t)_old).
Wait: R fired at a (R_new), RR fired at a+1 (RR_new).
boundary at RR at step a+2: (R_new, RR_new, right³(t)_old).
But we need this to match the MOVER triple at RR.
RR's mover triple at a+1: (R_old, RR_old, right³(t)_old).
R_new ≠ R_old (R fired). RR_new ≠ RR_old (RR fired).
So boundary at a+2 ≠ mover triple at a+1. No EC.

The adjacent-step approach never works because the left neighbor
always changes value between the non-mover step and the mover step.

SO: the induction DEFINITIVELY CANNOT close the sorry using mk_ec alone.

=== ACTUAL SOLUTION ===

Re-examine the sorry case. It happens when left³(t) fires in [a, fLL).
But we're inside the proof of h_phase_le1 which proves J+K ≤ 1 per phase.
The goal is to show: in a mixed phase, ¬EC is contradicted.

Instead of proving EC within the phase, we can prove that the PHASE STRUCTURE
is impossible. Specifically: the mixed phase with J=1, K=1, and the backward
chain extending to left³(t), implies a specific mover pattern that contradicts
the NORMALFORM assumption for an ADJACENT phase.

But this requires understanding the normalForm condition deeply.

Actually, wait. Let me reconsider. The current code structure is:
1. h_phase_le1: each phase has J+K ≤ 1 → sorry for mixed case
2. h_sparse: fc(L)+fc(R) ≤ fc(t) → sorry (uses h_phase_le1)
3. Combined with fire counts → False

The sorry at h_sparse (line 1129) is SEPARATE from sorrys 2,3.
Lines 1077 and 1121 are inside h_phase_le1.
Line 1129 is h_sparse (which USES h_phase_le1).
Lines 1172 is the final sorry.

So there are actually 5 sorrys. Let me count:
1012: inside h_phase_le1 (sorry 1 - vacuous)
1077: inside h_phase_le1 (sorry 2)
1121: inside h_phase_le1 (sorry 3)
1129: h_sparse (sorry 4 - depends on h_phase_le1)
1172: final (sorry 5)

If we close sorrys 1-3, then h_phase_le1 is proved. Then sorry 4 needs
the summation argument (fire count decomposition). Then sorry 5 needs
the cross-phase EC argument.

For sorrys 2 and 3: we KNOW they can't be closed locally.
The cleanest approach is to BYPASS them entirely.

BYPASS STRATEGY: Instead of proving J+K ≤ 1 for EVERY phase,
prove the conclusion (fc(L)+fc(R) ≤ fc(t)) DIRECTLY.

From normalForm_gap_constraint:
- J=0 → K=1
- K=0 → J=1
- J≥1, K≥1 → ¬(both even)

Per phase: J+K ≥ 1 (from the first two).
Summing: fc(L)+fc(R) ≥ fc(t).

For J+K ≤ 1: we need the mixed case to be excluded.
For fc(L)+fc(R) ≤ fc(t): summing J+K ≤ 1 gives ≤ fc(t).
But we CAN'T prove J+K ≤ 1 in the mixed case (sorry).

So: can we prove fc(L)+fc(R) ≤ fc(t) even allowing J+K = 2?
If some phases have J+K = 2 and others J+K = 1:
fc(L)+fc(R) = sum J_i + K_i. If one phase has J+K = 2: sum = fc(t) + 1.
Then fc(L)+fc(R) = fc(t) + 1 > fc(t). This contradicts h_sparse.

But h_sparse IS what we're trying to prove. So if J+K = 2 occurs,
fc(L)+fc(R) > fc(t), which means the conclusion of sparse_phase_false
(False) should follow from the FACT that fc(L)+fc(R) > fc(t).

Wait, sparse_phase_false concludes False from:
- h_sparse: fc(L)+fc(R) ≤ fc(t)
- omega (final line 1130)

If we CAN'T prove h_sparse, we need a different path to False.
"""

print("The sorry cases 2 and 3 cannot be closed by any local-phase EC construction.")
print("The proof needs restructuring. See analysis in comments above.")
print()
print("CONCRETE RECOMMENDATIONS:")
print("1. Close sorry 1 (line 1012): trivial, fL>a ∧ fR>a impossible.")
print("2. Close sorry 4 (line 1129): fire count decomposition (mechanical).")
print("3. Close sorry 5 (line 1172): domino/cross-phase argument.")
print("4. For sorrys 2,3: RESTRUCTURE to avoid per-phase mixed-EC proof.")
print("   Either:")
print("   (a) Show mixed phases imply a phase with both-even J,K (contradicts normalForm)")
print("   (b) Use the sub-threshold product to get fc(t) large enough that")
print("       the mixed-phase contribution is absorbed by the budget")
print("   (c) Prove the full ring walk forces a global EC using cross-phase")
print("       boundary triple propagation")
