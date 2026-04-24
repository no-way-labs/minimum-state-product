#!/usr/bin/env python3
"""
PA Domino Final 3: Check if the counterexample is a VALID good cycle.

A good cycle requires:
1. Each step: the mover changes its state (is privileged)
2. Consecutive movers must be adjacent on the ring
3. Returns to start config

The counterexample word starts with (0, 0, ...). Proc 0 fires twice
consecutively. For this to be valid:
- At step 0: mover = 0, config c. Proc 0 is privileged (f_0(L,S,R) ≠ S).
  After firing: c_0 changes.
- At step 1: mover = 0, config c'. Need proc 0 privileged again.
  Since 0 is ternary (m=3), after firing once: c_0 went from v to (v+1)%3.
  For proc 0 to be privileged again: f_0(L', (v+1)%3, R') ≠ (v+1)%3.
  This is possible but the mover word requires ADJACENT movers.

Wait — does the Lean definition require consecutive movers to be adjacent?
Let me check.
"""
import sys

# Actually, in the Lean code, a GoodCycle has:
# - configs : Vector (Vector (Fin (max (ms i) 1)) n) (L + 1)
# - moverAt : Fin L → Fin n
# - Each step: config changes by the mover's transition
#
# But does it require adjacent movers? Let me check.

# Looking at the GoodCycle structure, the mover can be ANY processor at each step.
# There's no adjacency constraint on the mover word.
# The privileged condition is: f_p(L, S, R) ≠ S.
# But the mover can jump arbitrarily around the ring.

# HOWEVER: the displacement calculation assumes movers are adjacent.
# The totalDisplacement sums +1 for CW moves and -1 for CCW moves.
# If movers are not adjacent (e.g., same proc fires twice), the
# displacement for that step is 0 (neither CW nor CCW).

# Let me re-read the displacement code more carefully.

# From GoodCycleBasics.lean:
# totalDisplacement = sum over k of stepDisplacement
# where stepDisplacement compares moverAt k to moverAt (k+1 mod L)
# If they're the same: 0. If adjacent CW: +1. CCW: -1. Non-adjacent: ???

# Actually, the Lean code probably handles this differently.
# Let me look at the CW/CCW step counting.

# From Sweep.lean:
# sweep_edgeNetFlow_ge2 uses totalDisplacement_eq_n_mul_edgeNetFlow
# which relates displacement to edge net flow.

# The key: in the Lean code, displacement is defined via the mover positions,
# not via adjacency. If consecutive movers are the same proc, the step
# is neither CW nor CCW and contributes 0 to displacement.

# For the counterexample:
# Step 0→1: mover 0 → mover 0 (same proc, displacement 0)
# Step 1→2: mover 0 → mover 8 (CCW, displacement -1)
# etc.

# Let me recompute displacement properly:
n = 9
word = [0,0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1]
ell = len(word)

disp = 0
for idx in range(ell):
    curr = word[idx]
    nxt = word[(idx+1) % ell]
    if nxt == (curr + 1) % n:
        disp += 1
    elif nxt == (curr - 1) % n:
        disp -= 1
    elif nxt == curr:
        pass  # same proc, 0 contribution
    else:
        print(f"  Non-adjacent non-same at step {idx}: {curr} -> {nxt}, d={disp}")

print(f"Corrected displacement: {disp}")
print(f"|displacement| = {abs(disp)}, 2n = {2*n}")
print(f"Is sweep? {abs(disp) >= 2*n}")

# Now: is same-proc consecutive allowed in a GoodCycle?
# In the Lean definition: the mover at each step is the privileged processor.
# Can the same processor fire twice in a row?
# Yes! If the proc's transition function makes it privileged again after firing.
# For ternary proc 0: after firing, c_0 = (old+1)%3.
# If f_0(L, (old+1)%3, R) ≠ (old+1)%3: proc 0 is privileged again.
# This is certainly possible.

# BUT: does the Lean GoodCycle require movers to be adjacent?
# Let me check the definition.

# From the code structure: GoodCycle.moverAt gives the mover at each step.
# The transition rules don't require adjacency.
# The displacement is computed from the mover word.

# For the sweep condition: |displacement| ≥ 2n.
# The counterexample has displacement = -18 = -2*9. So |disp| = 18 = 2*9.
# This is exactly the sweep threshold.

# Now: is this actually a valid GoodCycle?
# It depends on whether the transition functions exist that make it work.
# Key requirements:
# 1. At each step, the mover is privileged (f(L,S,R) ≠ S).
# 2. No EC means mover and non-mover contexts are disjoint at each proc.
# 3. Consistent transition function (each context maps to a unique output).

# The route doc says this is a "locally consistent witness" with no overlap.
# So yes, transition functions can be defined.

# But: does the resulting system CONVERGE?
# That's the hconv hypothesis. If we can show the system doesn't converge,
# the sorry can use hconv to derive a contradiction.

# Actually: the sorry doesn't need to find EC. It needs False.
# If we can show ¬converges, then hconv ∧ ¬converges = False. Done!

# But showing ¬converges for a specific cycle structure is very hard.
# And the sorry works for ALL cycles satisfying the hypotheses, not just this one.

# WAIT. Let me reconsider. Does the counterexample REALLY satisfy all hypotheses?
# Let me check hconv. hconv : converges sys gc means the SYSTEM converges.
# For the counterexample to be a problem, there must exist a system with
# this good cycle that converges.

# The no-EC condition allows consistent transition functions.
# But convergence is an additional requirement.
# If no converging system has this cycle, hconv eliminates this case.

# In practice: can we build a converging system from this cycle?
# That requires:
# - Transition functions consistent with the cycle
# - From every initial config, the system reaches a legitimate state
# - A legitimate state has exactly one privileged processor

# This is a very strong requirement. For ms=(3,2,...,2):
# Total configs = 3 * 2^8 = 768.
# The cycle visits 19 configs (all distinct).
# The remaining 749 configs must all lead to a legitimate state.
# And legitimate states must have exactly 1 privileged proc.

# For a ring of 9 processors with these state counts:
# Dijkstra's self-stabilization requires specific properties.
# Whether a converging system with this cycle structure exists
# is a non-trivial question.

# PRACTICAL ASSESSMENT:
# The counterexample blocks a PURE EC argument (without hconv).
# But hconv might provide the needed contradiction.
# The question: is hconv actually necessary for the sorry?

# For the lower bound proof: we're trying to show that no system with
# sub-threshold product converges. The proof structure assumes
# "converges sys gc" and derives False. The sorry is part of this.

# If the counterexample has a non-converging system: hconv blocks it.
# If it has a converging system: we have a genuine counterexample
# to the lower bound, which would be WRONG (since M_n = 4·3^(n-2) is proved).

# Since M_9 = 8748 > 768 = 3*2^8: any system with product 768 < 8748 can't converge.
# So hconv is FALSE for any system with this product!
# Therefore: hconv directly gives the contradiction!

# Wait, but that's the WHOLE THEOREM we're trying to prove.
# We can't use "M_n > product" to prove M_n > product — that's circular.

# The proof structure: show converges → False for sub-threshold products.
# Within the proof: decompose into sweep/zero-winding/odd-winding cases.
# In the sweep case: decompose into consecutive/non-consecutive binary.
# In the consecutive binary case: isolated/non-isolated.
# In the isolated case: parity/dispatch.
# The sorry is the final residual.

# The sorry needs to derive False from the hypotheses.
# The counterexample shows that EC-based arguments are insufficient.
# We need either hconv or another structural argument.

print()
print("="*70)
print("CRITICAL FINDING")
print("="*70)
print()
print("The counterexample ms=(3,2,...,2) at n=9 satisfies ALL hypotheses")
print("of consec_isolated_false EXCEPT possibly hconv.")
print()
print("It has NO entry conflict. Therefore, the sorry CANNOT be closed")
print("purely via entryConflict_impossible.")
print()
print("PROOF ROUTES:")
print()
print("Route 1: Use hconv to derive contradiction.")
print("  The counterexample has product 768. If we can show that")
print("  the cycle structure (isolated binary, odd parity, no dispatch)")
print("  combined with convergence implies a specific structural property")
print("  that contradicts subThreshold, we're done.")
print()
print("Route 2: Add hsweep and use a sweep-specific argument.")
print("  But the counterexample IS a sweep, so hsweep alone doesn't help.")
print()
print("Route 3: Use hconv + subThreshold together.")
print("  subThreshold: product < 4·3^(n-2).")
print("  hconv: the system converges.")
print("  The key: under convergence, the transition functions have")
print("  specific properties. Maybe these properties, combined with")
print("  the cycle structure, force EC.")
print()
print("Route 4: Rethink the proof architecture.")
print("  Maybe the sorry should be eliminated by restructuring the")
print("  proof so that the sweep case uses a different decomposition.")
print("  For example: instead of isolated-parity-dispatch, use")
print("  shadow orbit or some other obstruction for consecutive binary.")
