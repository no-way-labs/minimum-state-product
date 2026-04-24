"""
ra11_summary.py — Summary of findings and proposed proof approach.
"""

print("""
================================================================================
INVESTIGATION SUMMARY: Odd-Winding Non-Uniform Non-Consecutive Isolated
================================================================================

PROBLEM:
  oddWinding_nonUniform_sub_threshold_false (CaseObstructions.lean line 1053)
  has a recursion in its non-consecutive isolated-firings branch (line 1119).
  The isolated branch calls subThreshold_binary_core_false_residual, which
  ultimately invokes oddWinding_nonUniform_false (a sorry in CaseObstructionsCore)
  — creating a genuine recursive dependency.

RECURSION CHAIN:
  CaseObstructions.lean:1119 → subThreshold_binary_core_false_residual
  → binary_ring_impossibility_residual_callbacks (PhaseExtraction.lean:185)
  → CaseObstructionsCore.lean:38 oddWinding_nonUniform_false (sorry)
  → binary_ring_impossibility (PhaseExtraction.lean:32)
  → line 121: hOddNonUnifFalse callback invoked
  → RECURSION

WHY THE RECURSION IS CONTENT-FREE:
  The global dispatch adds NO information for the non-consecutive isolated case.
  It classifies the cycle as |Z|=0 (all fire), no pivot (no proc with both binary
  neighbors), not zero-winding, not sweep, odd-winding, non-uniform — then uses
  the callback. No actual work is done between entry and callback invocation.

COMPUTATIONAL FINDINGS:

1. Mover-word level (no configs):
   - 752/1000 random mover words at n=9 with ≥3 non-consec binary, odd-winding,
     non-uniform SATISFY all-binary-isolated. So isolated is NOT impossible at
     the mover-word level.

2. System level (with configs and transitions):
   - 52/52 odd-winding non-uniform all-isolated cycles at n=9 HAVE entry conflict
   - EC is 100% at system level (consistent with the theorem being true)

3. EC mechanism classification:
   - EC occurs at binary procs (276 instances) and ternary-binary boundary procs
     (478 instances), NEVER at interior ternary procs (0 instances)
   - ALL binary ECs (160/160) are DIFFERENT-GAP: the mover step and non-mover
     step are in different gaps of the binary proc
   - Between the EC pair: ternary neighbors fire 0-8 times (0 fires = 56,
     2 fires = 53, 3 fires = 18, etc.)
   - The ternary value match is NOT just from 0-fire preservation; it depends
     on the actual transition function

4. Distance-2 binary pairs:
   - At n=9 with binary at {0,3,6}: NO distance-2 pairs exist
   - No processor has both binary neighbors → the "pivot" approach fails
   - Many non-consec binary configurations at n=9 have no distance-2 pairs

5. parity-based EC (procMinGap_hasEntryConflict):
   - CANNOT be used: requires threeConsecutiveBinary, which we don't have
   - 0/106 mover words produced parity EC for non-consecutive binary

AVAILABLE TOOLS THAT DON'T RECURSE:
  - binary_isolated_firings_or_ec: gives EC ∨ permanent ∨ isolated (already used)
  - permanent_mover_totalDisplacement_zero: eliminates permanent (already used)
  - allIsolated_gap_ge2: gap ≥ 2 from isolated (available)
  - MinFiringGap: provides gap boundaries (available)
  - no_safeProcessor_of_nonZeroWinding: no safe processor (already derived)
  - edgeTraversalCount_pos_of_isOddWinding: all procs fire (already derived)

PROPOSED APPROACH:
================================================================================

STRATEGY: Break the recursion by handling the non-consecutive isolated case
DIRECTLY in CaseObstructions.lean, without calling subThreshold_binary_core_false.

The proof needs a NEW theorem:

  theorem nonConsecutive_isolated_oddWinding_false
    (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) (h3bin : hasGe3Binary sys.rs)
    (hnocons : ¬∃ i, threeConsecutiveBinary sys.rs i)
    (hodd : gc.isOddWinding) (hnonunif : ¬gc.uniformDirection)
    (p : Fin sys.rs.n) (hbin : isBinary sys.rs p)
    (hfc : 2 ≤ gc.fireCount p)
    (hiso : ∀ a, gc.moverAt a = p → gc.moverAt (nextIndex gc.configs a) ≠ p)
    : False

PROOF APPROACHES (ranked by feasibility):

1. **Reduction to existing tools** (easiest if applicable):
   Since the sweep non-consec isolated case has the SAME recursion pattern,
   both cases might be resolved simultaneously by:
   - Factoring out a shared "non-consec + isolated → EC" lemma
   - Proving it directly using MinFiringGap + gap analysis

   The gap analysis would need to show: for binary p with isolated firings
   and ternary neighbors, across all gaps, some pair of mover/non-mover
   steps must have matching full context.

2. **Pigeonhole on transition function** (moderate):
   Binary p has 2 states. Ternary neighbors each have 3 states.
   So p sees 2*3*3 = 18 possible contexts (L, S, R).
   With fc(p) ≥ 2 mover contexts and at least some non-mover contexts,
   pigeonhole might force a match.

   More precisely: p fires at steps a1, a2, ..., ak (k ≥ 2, k even).
   At each fire step ai: context = (L_ai, S_ai, R_ai).
   At each non-mover step in the gaps: context = (L_t, S_t, R_t).

   For EC: need some fire-step context = some non-mover context.

   With isolated firings: after firing at ai, p's value changes.
   At step ai+1 (first non-mover step): p's new value ≠ p's old value.
   So config[p] at ai ≠ config[p] at ai+1. No immediate EC at p.

   But at some later non-mover step t in a different gap:
   config[p] at t might = config[p] at some fire step aj.
   This happens when p's prefix-fire parity at t matches at aj.

   For binary p: parity match iff fires between aj and t is even.
   Since p has isolated firings: each gap has 0 fires of p.
   From aj to t: p fires the number of times = (fires of p in [aj, t)).
   If t is in a later gap, fires of p between = number of fire-steps
   between aj and t.

3. **Use oddWinding structure more deeply** (hardest):
   Odd-winding gives specific edge traversal counts.
   Each edge is traversed an odd number of times.
   Combined with isolated binary firings: strong constraints on
   the mover word structure.

   singletonEdge_or_edgeTraversalCount_ge_three_of_isOddWinding
   (NonConsecutive.lean line 79): each edge is traversed either 1 or ≥3 times.

   Singleton edges create opportunities for EC because the mover crosses
   that edge exactly once in each direction → very constrained transition.

RECOMMENDATION:

Start with approach 2 (pigeonhole). The binary proc p has:
- k ≥ 2 fire-steps, each with a context from {0,1} × {0,1,2} × {0,1,2} = 18 values
- Many non-mover steps, each also with a context from the same 18 values
- Sub-threshold (product < 4*3^7) constrains the transition function
- Convergence further constrains it

The pigeonhole argument: with k ≥ 2 fire-step contexts and L - k ≥ 22
non-mover contexts (L ≥ 24 at minimum), and only 18 possible context values,
some fire-step context must appear as a non-mover context.

BUT: the fire-step contexts might all be distinct from non-mover contexts
(up to 18 possible values, k=2 fire contexts, leaving 16 for non-movers).
So pure pigeonhole on context count doesn't work.

REFINED PIGEONHOLE: The issue is that non-mover contexts can avoid fire contexts.
But sub-threshold constrains this: with 18 possible contexts and the transition
function being constrained by convergence, there aren't enough "escape" contexts.

ACTUALLY: This is exactly what the UEC 4-mechanism proof handles computationally.
The 4 mechanisms cover all cases. But formalizing them in Lean is the challenge.

BOTTOM LINE: This is a genuine mathematical gap requiring new Lean formalization.
The most promising approach is to formalize a direct pigeonhole/context-counting
argument for binary procs with isolated firings and ternary neighbors.
""")


if __name__ == "__main__":
    pass
