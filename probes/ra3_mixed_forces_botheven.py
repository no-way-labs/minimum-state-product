#!/usr/bin/env python3
"""
Check: If a mixed phase exists (J≥1, K≥1), does it force another phase
to have both-even (J,K)? If yes, that contradicts normalForm.

At n=5 with ¬EC cycles having mixed phases: check ALL phase types.

From earlier data: cycles with all-mixed phases exist at n=5.
Phase type combos included ('mixed', 'mixed') and ('mixed', 'neither', 'mixed').

normalForm_gap_constraint says: J=0→K=1, K=0→J=1, mixed→¬(both even).
'neither' type has J=0 AND K=0. But J=0→K=1 means K≥1. Contradiction?

Wait: 'neither' means J=0 AND K=0. But normalForm says J=0→K=1.
So if J=0 AND K=0: normalForm gives K=1. Contradiction with K=0.
So 'neither' type VIOLATES normalForm!

But in our n=5 data, we found 'neither' phases in ¬EC cycles.
This means those cycles are NOT normalForm. The Lean theorem assumes
ALL phases are normalForm.

If ALL phases are normalForm: J=0→K=1 and K=0→J=1 means J+K ≥ 1.
So 'neither' (J=0,K=0) is impossible.

Let me recheck: the combo ('L-only', 'neither', 'L-only') at n=5.
This has a 'neither' phase. This would violate normalForm.

So under normalForm: only 'L-only', 'R-only', 'mixed' are possible.
Each phase has J+K ≥ 1.

With fc(L) even ≥ 2, fc(R) even ≥ 2, fc(t) ≥ 3:
fc(L)+fc(R) ≥ 4.
Sum over phases: ∑(J_i+K_i) = fc(L)+fc(R) ≥ 4.
Number of phases = fc(t) ≥ 3.

If each phase has J+K ≤ 1: ∑(J+K) ≤ fc(t). Need ≥ 4, so fc(t) ≥ 4.
If each phase has J+K ≤ 2: ∑(J+K) ≤ 2·fc(t). Always fine.

The key bound: fc(L)+fc(R) ≤ fc(t) requires J+K ≤ 1 per phase.
With mixed phases (J+K=2): ∑(J+K) = fc(L)+fc(R) could exceed fc(t).

Specific example: fc(t)=4, fc(L)=2, fc(R)=2. ∑(J+K)=4.
If one phase is mixed (J=K=1): contributes 2.
Other 3 phases: contribute 2 total, so at least one has J+K=0.
But normalForm says J+K ≥ 1. Contradiction!

So if fc(t)=4, fc(L)=2, fc(R)=2 with 4 phases:
Each phase has J+K ≥ 1. Total = 4 = fc(t).
If one is mixed (J+K=2): other 3 have total 2, so one has J+K=0. ⊥

WAIT: 4 phases with total J+K=4 and one phase using 2:
other 3 phases need total 2, each ≥ 1. So all 3 have J+K=1 except
one has J+K=0. But J+K ≥ 1 means we need 3·1 = 3 ≤ 2. ⊥.

So: with fc(t)=4, a mixed phase is IMPOSSIBLE (under normalForm + binary parity).

What about fc(t)=3? fc(L)+fc(R) ≥ 4 > 3 = fc(t).
This means fc(L)+fc(R) > fc(t) when fc(t)=3.
So with 3 phases, ∑(J+K) = fc(L)+fc(R) ≥ 4 > 3.
Pigeonhole: some phase has J+K ≥ 2 (mixed). But mixed is what we're
trying to rule out!

CRITICAL: if fc(t)=3, mixed phases are FORCED by pigeonhole.
fc(L)=2, fc(R)=2, fc(t)=3, 3 phases each with J+K ≥ 1.
∑(J+K) = 4. 3 phases with J+K ≥ 1 and sum = 4.
At least one phase has J+K ≥ 2 (mixed).

So the proof MUST handle mixed phases when fc(t) = 3.
The per-phase J+K ≤ 1 bound is IMPOSSIBLE when fc(t) = 3.
This means h_sparse (fc(L)+fc(R) ≤ fc(t)) is FALSE when fc(t)=3.

But wait: fc(t) ≥ 3 (ternary fires ≥ 3). If fc(t) = 3:
fc(L)+fc(R) ≥ 4 > 3. h_sparse fails. omega at line 1130 fails.

The proof MUST be wrong as structured. Unless fc(t) ≥ 4 can be proved.

CAN fc(t) ≥ 4 be proved? From the code:
hfc2: fc(t) ≥ 2 (input hypothesis).
h_sparse: fc(L)+fc(R) ≤ fc(t) (if we could prove it).
fc(L) ≥ 2, fc(R) ≥ 2: fc(t) ≥ 4.
But h_sparse is what we're trying to prove! Circular.

HMMMM. Let me re-read the structure more carefully.
"""

# Re-reading the flow:
# sparse_phase_false receives:
#   hfc2: fc(t) ≥ 2
#   hall_normal: all phases normalForm
# It tries to prove False.
#
# Step 1: fc(L) ≥ 2, fc(R) ≥ 2.
# Step 2: h_sparse: fc(L)+fc(R) ≤ fc(t). SORRY.
#   Inside: h_phase_le1: each phase J+K ≤ 1. SORRY for mixed case.
# Line 1130: omega (False from h_sparse + fc counts)
#   Wait, what does omega prove? fc(L) ≥ 2, fc(R) ≥ 2, fc(L)+fc(R) ≤ fc(t).
#   So fc(t) ≥ 4. Then Step 3 uses fc(t) ≥ 4.
#
# Step 3: fc(t) ≥ 4. Uses pigeonhole + sparse bound.
#   sparse_phase_sum_ge: fc(L)+fc(R) ≥ fc(t) (under normalForm + ¬EC).
#   Combined with h_sparse: fc(L)+fc(R) = fc(t).
#   Then: each phase has J+K = 1. No mixed phases.
#   Pigeonhole: a phase with K=0 (or J=0) exists.
#   That phase triggers the "domino" argument.
# SORRY at line 1172.

# So the flow is:
# h_sparse → fc(t) ≥ 4 → sparse_phase_sum_ge → fc equality → no mixed → domino → False
# But h_sparse REQUIRES J+K ≤ 1 (no mixed), which requires fc(t) ≥ 4,
# which requires h_sparse. CIRCULAR!

# Unless h_sparse can be proved INDEPENDENTLY of J+K ≤ 1.

# Actually, let me re-read h_sparse proof attempt:
# It proves h_phase_le1 first: each phase J+K ≤ 1.
# h_phase_le1 is proved by contradiction: if J+K ≥ 2, case split:
#   J≥2,K=0 → mechanism (normalForm contradiction)
#   J=0,K≥2 → mechanism (normalForm contradiction)
#   J≥1,K≥1 → mk_ec constructions → sorry for backward chain
#
# Then h_sparse: fc(L)+fc(R) = ∑(J_i+K_i) ≤ ∑1 = fc(t). sorry.
#
# The h_sparse sorry (line 1129) is DIFFERENT from sorrys 2,3.
# h_sparse needs the SUMMATION of intervalFireCount equals fireCount.
# That's a mechanical lemma (fire count decomposition).

# IF sorrys 2,3 could be closed, then h_phase_le1 is proved,
# h_sparse follows from summation, and the rest follows.

# The problem: sorrys 2,3 can't be closed locally.

# ALTERNATIVE: prove h_sparse WITHOUT h_phase_le1.
# If J+K = 2 for some phase i, and J+K = 1 for others:
# ∑(J+K) = fc(L)+fc(R) = fc(t) + (number of mixed phases).
# So fc(L)+fc(R) = fc(t) + M where M = number of mixed phases.
# h_sparse says fc(L)+fc(R) ≤ fc(t), so M = 0.
# But we can't prove M = 0 without the per-phase bound.

# WAIT: from normalForm, mixed phases have ¬(both even J,K).
# With J=1,K=1: both odd. OK, doesn't help.
# With J=1,K=3: J odd, K odd. Both odd, not both even. OK.
# With J=2,K=1: J even, K odd. Not both even. OK.

# The constraint ¬(both even) allows J=1,K=1 (sum 2).
# So mixed phases contribute J+K ≥ 2.

# To prove False without per-phase bound:
# fc(L)+fc(R) ≥ fc(t) (from normalForm J+K ≥ 1 per phase).
# If fc(L)+fc(R) > fc(t): some phase has J+K ≥ 2 (mixed).
# In that mixed phase: need to derive EC or contradiction.
# The EC is exactly what the sorry blocks.

# So the proof IS fundamentally about mixed phases.
# The sorry can't be avoided.

# LAST RESORT: prove that at n ≥ 9 with ≥ 3 binary + sub-threshold,
# mixed phases in normalForm cycles ALWAYS have EC (even if not local to the phase).

print("ANALYSIS OF FIRE COUNT CONSTRAINTS")
print()
print("Under normalForm + binary parity:")
print("  fc(L) even ≥ 2, fc(R) even ≥ 2")
print("  Each phase has J+K ≥ 1 (normalForm)")
print("  fc(L)+fc(R) = ∑(J_i+K_i) ≥ fc(t)")
print()
print("If fc(t) = 3: fc(L)+fc(R) ≥ 4 > 3 = fc(t)")
print("  → pigeonhole: some phase has J+K ≥ 2 (mixed)")
print("  → mixed phases are FORCED when fc(t) = 3")
print()
print("If fc(t) = 4: fc(L)+fc(R) ≥ 4 = fc(t)")
print("  → each phase can have J+K = 1 (no mixed needed)")
print()
print("The sorry blocks proving J+K ≤ 1 in mixed phases.")
print("If fc(t) = 3: J+K ≤ 1 is IMPOSSIBLE (pigeonhole forces mixed).")
print("So h_sparse (fc(L)+fc(R) ≤ fc(t)) is FALSE when fc(t) = 3.")
print()
print("This means the proof's logic REQUIRES fc(t) ≥ 4.")
print("But fc(t) ≥ 4 is DERIVED from h_sparse + fc(L) ≥ 2 + fc(R) ≥ 2.")
print("CIRCULAR DEPENDENCY!")
print()
print("RESOLUTION: The proof needs to handle fc(t) = 3 SEPARATELY.")
print("When fc(t) = 3: fc(L)+fc(R) ≥ 4 > 3 gives a mixed phase.")
print("That mixed phase must produce EC through a DIFFERENT argument")
print("(not the per-phase J+K ≤ 1 bound).")
print()
print("For fc(t) = 3 with one mixed phase (J=1,K=1):")
print("  3 phases: (1,1), (J2,K2), (J3,K3) with J+K ≥ 1 each.")
print("  fc(L) = 1+J2+J3 (even), fc(R) = 1+K2+K3 (even).")
print("  J2+J3 odd, K2+K3 odd. So J2+K2+J3+K3 even, ≥ 2.")
print("  fc(L)+fc(R) = 2 + (J2+J3) + (K2+K3) = 2 + 2+ = 4.")
print("  With J2+J3 ≥ 1, K2+K3 ≥ 1: fc(L) ≥ 2, fc(R) ≥ 2. ✓")
