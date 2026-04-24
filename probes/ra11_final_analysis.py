"""
ra11_final_analysis.py — Final analysis of the recursion-breaking problem.

ARCHITECTURE SUMMARY:

The recursion for odd-winding non-uniform non-consecutive isolated:
  oddWinding_nonUniform_sub_threshold_false (CaseObstructions.lean line 1119)
  → subThreshold_binary_core_false_residual (PhaseExtraction.lean)
  → binary_ring_impossibility_residual_callbacks (produces 4 callbacks from CaseObstructionsCore sorrys)
  → binary_ring_impossibility (PhaseExtraction.lean line 32)
  → |Z|=0, no pivot, not zero-winding, not sweep, odd-winding, non-uniform
  → uses hOddNonUnifFalse callback (line 121)
  → CaseObstructionsCore::oddWinding_nonUniform_false (sorry)
  → RECURSION

The ONLY sorry invoked is #4 (oddWinding_nonUniform_false).

TWO STRATEGIES TO BREAK THE RECURSION:

STRATEGY 1: Fill the sorry in CaseObstructionsCore directly.
  oddWinding_nonUniform_false can call oddWinding_nonUniform_sub_threshold_false
  (from CaseObstructions)... but CaseObstructionsCore can't import CaseObstructions.

  HOWEVER: CaseObstructionsCore DOESN'T import PhaseExtraction.
  It imports CycleTypes and GlobalMinGap. So it could import other files
  that have the needed proof, as long as they don't create an import cycle.

  Can we prove oddWinding_nonUniform → False WITHOUT PhaseExtraction?
  This would need to avoid:
  - subThreshold_binary_core_false (in PhaseExtraction)
  - binary_ring_impossibility (in PhaseExtraction)
  - allNormalForm_false (in AllNormalFormFalse, imported by PhaseExtraction)

  What's available in CaseObstructionsCore's import tree:
  - CycleTypes: cycle type classification
  - GlobalMinGap: global minimum gap crossing analysis
  - Everything they transitively import

  GlobalMinGap provides:
  - global_min_gap_ec: entry conflict from global minimum gap crossings
  - Used for zero-winding cases with consecutive binary

  CycleTypes provides:
  - zeroWinding_or_isOddWinding_of_not_sweep
  - isSweep, isOddWinding, uniformDirection definitions
  - Cycle type classification

  Neither provides the needed tools for non-consecutive binary.

STRATEGY 2: Modify CaseObstructions.lean to not call subThreshold_binary_core_false_residual
  for the non-consec isolated case.

  Instead of routing through the global dispatch, prove False directly:
  - We have: binary p, isolated firings, fc ≥ 2
  - We have: odd-winding (|W| = n), non-uniform
  - We have: ≥3 non-consec binary, sub-threshold, converges
  - We have: no safe processor (from odd-winding)

  What new theorem would we need?

  OPTION 2A: Prove entry conflict from isolated binary firings of a
  NON-CONSECUTIVE binary processor directly, without phase extraction.

  This would need a way to get EC from:
  - Binary p with isolated firings
  - At least one ternary neighbor
  - Sub-threshold, converges

  The difficulty: for non-consec binary, the parity-based EC argument
  doesn't work because the ternary neighbor's value isn't determined
  by fire parity.

  OPTION 2B: Use the MNU / shadow machinery for non-sweep cycles.
  The shadow cycle approach is primarily for sweeps.
  The wiggle shadow approach is for single-wiggle words.
  Can either be adapted for odd-winding non-uniform?

  OPTION 2C: Use convergence more directly.
  converges sys gc + sub-threshold + ≥3 non-consec binary implies
  strong structural constraints on the transition tables.
  Combined with isolated binary firings + odd-winding, maybe we can
  derive EC.

  OPTION 2D: Show that the isolated firings condition is impossible
  for binary procs in odd-winding cycles with non-consecutive binary.
  That is: binary procs MUST have consecutive firings (contradicting "isolated"),
  giving us EC from the binary_isolated_firings_or_ec trichotomy.

  This seems unlikely based on the mover-word-level analysis (752/1000 words
  have all binary isolated).

STRATEGY 3 (SIMPLEST): Factor out the |Z|=0, no-pivot, non-zero-winding case
  from binary_ring_impossibility into its own theorem that doesn't need callbacks.

  At line 113-121 of binary_ring_impossibility:
  ```
  · -- Non-zero-winding, no pivot, all fire: dispatch on cycle type
    by_cases hsweep : gc.isSweep
    · exact hSweepFalse hsweep
    · rcases gc.zeroWinding_or_isOddWinding_of_not_sweep hsweep with hzw | hodd
      · exact (hzero hzw).elim
      · by_cases hunif : gc.uniformDirection
        · exact (gc.not_uniformDirection_and_isOddWinding_of_hasGe3Binary _h3bin)
            ⟨hunif, hodd⟩
        · exact hOddNonUnifFalse hodd hunif
  ```

  This block dispatches on cycle type. For odd-winding non-uniform, it uses
  the callback. But we could REPLACE this dispatch with a direct argument.

  The |Z|=0 + no pivot + non-zero-winding hypotheses are:
  - All procs fire (|Z|=0)
  - No proc has both binary neighbors and fires (equivalent to no pivot)
  - Non-zero winding

  Combined with hsub, h3bin, hconv, hno_safe, hn.

  CLAIM: These hypotheses directly imply a SAFE PROCESSOR exists or
  the system can't converge.

  Actually, hno_safe says NO safe processor. So we need a different approach.

  KEY INSIGHT: "no pivot" means no proc has both binary neighbors.
  For ≥3 non-consec binary: this means all binary gaps ≥ 3.
  With n ≥ 9 and ≥ 3 binary (each at distance ≥ 3): n ≥ 3*3 = 9. OK.
  But with k=3 binary: n = 3*gap = 3*3 = 9 exactly.
  So binary at {0,3,6} with all gaps = 3.

  In this case: there are exactly 3 "ternary runs" of length 2 each
  (procs 1-2, 4-5, 7-8). Each run is flanked by binary procs.

  CONVERGENCE ARGUMENT:
  With all procs firing and no safe processor, the mover visits every
  proc's neighborhood. But the binary procs have isolated firings,
  so the mover alternates between binary fires and ternary traversals.

  For sub-threshold product: prod(ms) < 4*3^7 = 8748.
  With binary at {0,3,6}: product = 2^3 * 3^6 = 5832.

  The convergence property means: from ANY bad configuration, the system
  reaches a good configuration in finite steps. This constrains the
  transition function heavily.

  But I don't see how to use this directly without essentially
  re-deriving the phase extraction argument.

CONCLUSION:

The simplest path forward is likely STRATEGY 1 variant:
  Create a NEW file (e.g., OddWindingDirect.lean) that:
  1. Imports everything CaseObstructionsCore can import
  2. Proves oddWinding + non-uniform + ≥3 non-consec binary + sub-threshold → False
  3. Without importing PhaseExtraction
  4. Then CaseObstructionsCore imports this file and fills the sorry

  But this requires a proof of the odd-winding non-uniform case that
  doesn't use PhaseExtraction. That's the hard part.

ACTUAL SIMPLEST FIX:

The sweep non-consec isolated case has the SAME recursion problem but
goes through hSweepFalse instead of hOddNonUnifFalse.

For SWEEP: the mover makes ≥ 2n non-stay steps, ALL in the same direction.
This is much more constrained than odd-winding non-uniform.

For sweep + non-consec + isolated: the mover sweeps around the ring,
firing each binary proc exactly 2 times (min), with no consecutive fires.
The sweep direction gives a specific traversal pattern.

Actually, sweeps are UNIFORM direction, so sweep + ≥3 non-adj binary:
The mover goes one direction consistently. It visits each proc in order.
With isolated binary firings: binary p fires, mover moves to next proc,
eventually comes back and fires p again.

For sweep cycles, the shadow cycle obstruction is already proved
(Shadow.Theorem). Can we use that directly?

CHECK: Does sweep_sub_threshold_false (the caller) already have a
sorry-free proof for the consecutive case? Yes (line 1007:
consecutive_binary_isolated_false). Only the non-consecutive case recurses.

For sweep + non-consecutive:
The shadow cycle theorem says: every sweep good cycle with ≥3 non-adj
binary at sub-threshold has a shadow cycle, which creates an entry conflict.

Is this available as a sorry-free theorem in Shadow.Theorem?
"""

print("=" * 70)
print("FINAL ARCHITECTURE ANALYSIS")
print("=" * 70)
print()
print("RECURSION POINTS:")
print("  1. sweep + non-consec isolated → hSweepFalse callback (sorry #3)")
print("  2. oddWinding + non-consec isolated → hOddNonUnifFalse callback (sorry #4)")
print()
print("BOTH go through subThreshold_binary_core_false_residual → binary_ring_impossibility")
print("and hit their respective sorry in CaseObstructionsCore.")
print()
print("PROPOSED FIX (for odd-winding only, as requested):")
print()
print("In CaseObstructions.lean, oddWinding_nonUniform_sub_threshold_false,")
print("at line 1113 (isolated firings, non-consecutive), INSTEAD of calling")
print("subThreshold_binary_core_false_residual, call a NEW theorem:")
print()
print("  nonConsecutive_isolated_oddWinding_false")
print("    (requires: binary p, isolated, fc ≥ 2, odd-winding, non-consec,")
print("     sub-threshold, converges, no safe processor)")
print("    → False")
print()
print("This theorem needs to be provable WITHOUT PhaseExtraction.")
print()
print("THE KEY PROOF IDEA:")
print("  odd-winding → non-zero winding → no safe processor (already derived)")
print("  + sub-threshold + ≥3 non-consec binary + converges")
print("  This is the SAME hypotheses as the entire main theorem!")
print()
print("  The non-consec isolated case for odd-winding IS the odd-winding case itself")
print("  (since EC and permanent are already handled). So the recursion is inherent:")
print("  proving the odd-winding case for non-consec = proving the odd-winding case.")
print()
print("  There's no 'extra information' from having isolated firings — isolated")
print("  is the COMPLEMENT of EC and permanent.")
print()
print("RESOLUTION: The recursion can be broken by proving the odd-winding")
print("case via a COMPLETELY DIFFERENT method than phase extraction.")
print()
print("Options:")
print("  A. Shadow cycle / wiggle for odd-winding cycles (need new math)")
print("  B. Direct EC from isolated binary + odd-winding structure (need new math)")
print("  C. Show isolated is impossible for odd-winding non-consec (need new math)")
print()
print("None of these exist in the codebase yet. This is a GENUINE MATHEMATICAL GAP.")


if __name__ == "__main__":
    main()
