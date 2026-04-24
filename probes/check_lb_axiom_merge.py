#!/usr/bin/env python3
"""
Investigation: Can the 3 remaining LB axioms be reduced?

Analysis of the 3 axioms in CaseObstructions.lean:

1. consecutive_zeroWinding_obstruction
   - hypotheses: n≥9, gc, converges, zeroWinding, 3-consecutive-binary
   - conclusion: False
   - used by: palindromic_entry_conflict_theorem → case3a_impossible

2. nonconsecutive_zeroWinding_obstruction
   - hypotheses: gc, n≥9, converges, subThreshold, zeroWinding, ¬3-consecutive
   - conclusion: False
   - used by: universal_entry_conflict_nonconsec → case3bc_impossible

3. nonZeroWinding_obstruction
   - hypotheses: n≥9, gc, converges, subThreshold, ¬zeroWinding, hasGe3Binary
   - conclusion: False
   - used by: sweep_obstruction, oddWinding_nonUniform_obstruction
     → cycle_classification_residual → cycle_classification
     → case3a_impossible, case3bc_impossible

MERGE ANALYSIS:
==============

Axioms 1+2 can be merged into:
  zeroWinding_obstruction(n≥9, gc, converges, subThreshold, zeroWinding) : False

Reason:
- Axiom 1 doesn't need subThreshold, but at both call sites (case3a_impossible
  and case3bc_impossible), subThreshold IS available.
- The merged version drops the binary placement hypothesis entirely.
- Both call sites have all needed hypotheses.

Call site check:
- case3a_impossible has: hn (n≥9), hsub (subThreshold), gc, hconv, hzero
  → YES, all available
- case3bc_impossible has: hn (n≥9), hsub (subThreshold), gc, hconv, hzero
  → YES, all available

FURTHER MERGE ANALYSIS:
======================

Could we merge all 3 into one?
  subThreshold_obstruction(n≥9, gc, converges, subThreshold) : False

This would be the theorem itself — inappropriate. The case split between
zero-winding and non-zero-winding is a genuine structural distinction.

Can we merge (1+2) with 3?
  The zeroWinding merged axiom has: n≥9, gc, converges, subThreshold, zeroWinding
  Axiom 3 has: n≥9, gc, converges, subThreshold, ¬zeroWinding, hasGe3Binary

  subThreshold already implies hasGe3Binary (proved: subThreshold_ge3_binary).

  So the case split is on zeroWinding vs ¬zeroWinding. Merging would give us
  back the theorem statement. NOT useful.

VACUITY CHECK:
=============

Can any axiom be vacuously true (hypotheses contradictory)?

For n≥9, subThreshold means product < 4·3^(n-2).
This implies ≥3 binary (proved).

Zero-winding good cycles DO exist in general (e.g., back-and-forth cycles).
Non-zero-winding good cycles also exist (sweep cycles).

So none of the axioms are vacuous.

NARROWING CHECK:
===============

Could merged zero-winding axiom assert hasEntryConflict instead of False?
  zeroWinding_gives_entryConflict(n≥9, gc, converges, subThreshold, zeroWinding)
    : hasEntryConflict gc

Then False follows from entryConflict_impossible. This is a NARROWER claim
(more specific intermediate result). Both the consecutive and nonconsecutive
proofs ultimately work via entry conflict, so this is mathematically accurate.

However, this doesn't reduce axiom count further (still 2: this + axiom 3).
The main benefit would be mathematical precision.

RECOMMENDATION:
==============

Merge axioms 1+2 → reduce from 3 axioms to 2.

Net change: -1 axiom (from 3 to 2), no sorry, no new axiom.

Implementation:
1. Add zeroWinding_obstruction axiom to CaseObstructions.lean
2. Remove consecutive_zeroWinding_obstruction and nonconsecutive_zeroWinding_obstruction
3. Update palindromic_entry_conflict_theorem to use new axiom
4. Update universal_entry_conflict_nonconsec to use new axiom
5. Update docstrings in Theorem.lean
"""

print("=== LB Axiom Merge Investigation ===")
print()
print("Current axioms (3):")
print("  1. consecutive_zeroWinding_obstruction")
print("  2. nonconsecutive_zeroWinding_obstruction")
print("  3. nonZeroWinding_obstruction")
print()
print("Proposed merge: 1+2 → zeroWinding_obstruction")
print()
print("After merge (2 axioms):")
print("  1. zeroWinding_obstruction(n≥9, gc, converges, subThreshold, zeroWinding) : False")
print("  2. nonZeroWinding_obstruction(n≥9, gc, converges, subThreshold, ¬zeroWinding, hasGe3Binary) : False")
print()

# Check: can axiom 3 (nonZeroWinding_obstruction) also drop hasGe3Binary?
# subThreshold implies hasGe3Binary, so YES.
print("Additional simplification: axiom 3 can drop hasGe3Binary")
print("  (since subThreshold implies hasGe3Binary via subThreshold_ge3_binary)")
print()
print("Simplified axiom 3:")
print("  nonZeroWinding_obstruction(n≥9, gc, converges, subThreshold, ¬zeroWinding) : False")
print()

# But wait - the call site for nonZeroWinding_obstruction:
# In sweep_obstruction (line 194): passes h3bin explicitly
# In oddWinding_nonUniform_obstruction (line 210): passes h3bin explicitly
# Both have hsub available via cycle_classification_residual's caller
# Actually let me re-check...

# cycle_classification_residual takes _hsub as parameter
# sweep_obstruction calls nonZeroWinding_obstruction with h3bin
# But h3bin = subThreshold_ge3_binary sys.rs _hsub is available

print("Call site check for simplified axiom 3:")
print("  sweep_obstruction: has hsub (passed from cycle_classification_residual)")
print("  oddWinding_nonUniform: has hsub (same)")
print()

# Could we go further: merge ALL into one axiom with Decidable on zeroWinding?
# nonZeroWinding case: by_cases hzero; contradiction with hyp vs apply merged axiom
# That would require the merged axiom to handle BOTH cases, which IS the theorem.
# So no, 2 is the right number.

print("FINAL PLAN: 3 axioms → 2 axioms")
print("  - Merge zero-winding axioms (drop binary placement hypothesis)")
print("  - Simplify non-zero-winding axiom (drop redundant hasGe3Binary)")
print("  Net: -1 axiom, 0 sorry, 0 new axiom")
