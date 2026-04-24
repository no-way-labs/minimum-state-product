#!/usr/bin/env python3
"""
RA12 SUMMARY: Clean proof path for CL ≤ 2n (or equivalently fc = 2 for all procs).

==========================================================================
FINDINGS
==========================================================================

1. CL ≤ 2n does NOT follow from walk structure + run-length constraints alone.
   Abstract ZW walks with fc ≥ 2, binary run ≤ 1, ternary run ≤ 2 can have
   CL = 11, 12, 13, ... > 2n = 10 at n=5.

2. CL > 2n walks CAN produce distinct configs (no state collision).
   All 5 tested L=11 walks at n=5 have value assignments giving 11 distinct configs.

3. CL > 2n walks CANNOT be transition-consistent (entry conflict is universal).
   100% of distinct-config assignments at L=10,11,12,13,14 have entry conflicts.
   Tested exhaustively at n=5 for ms=(2,2,2,3,3) and ms=(2,3,2,3,2).
   Also at n=6 for ms=(2,2,2,3,3,3). All show 100% EC.

4. The entry conflict mechanism for CL > 2n:
   - For ternary fc=3: one of the 3 firing contexts matches a non-mover context.
   - For binary fc≥4: entry conflict occurs (not config collision).
   - The EC uses entryConflict_impossible (same (L,S,R) as both mover and non-mover).

5. Config collision (1st and 3rd binary firing identical) does NOT happen.
   Binary fc=4 cases have 0 config collisions. The argument in the Lean sketch
   about "binary parity + config distinctness → config collision" is WRONG.

==========================================================================
RECOMMENDED PROOF PATH
==========================================================================

The sorry at line 86 of CaseObstructionsCore.lean should be proved by:

APPROACH: By contradiction using entry conflict.

Assume CL > 2n. Then ∑ fc(p) > 2n with fc(p) ≥ 2 for all p.
So some proc q has fc(q) ≥ 3.

STEP 1: Show that fc(q) ≥ 3 at ANY proc q forces an entry conflict.

The argument: with fc(q) ≥ 3, proc q fires ≥ 3 times.
The key property: the zero-winding walk's back-and-forth structure causes
q's neighborhood context (c[left(q)], c[q], c[right(q)]) at one of q's
firing steps to exactly match q's context at some non-mover step.

More precisely: consider the step k where q fires for the first time (or
the last time, depending on which is easier). After the full CW+CCW
traversal returns to q's neighborhood, the context has been "restored"
by the palindromic structure. But q's value may have changed (due to its
own firings), creating an entry conflict.

STEP 2: Apply entryConflict_impossible to derive False.

This gives CL ≤ 2n by contradiction.

==========================================================================
ALTERNATIVE (SIMPLER): Bypass CL ≤ 2n entirely
==========================================================================

Instead of the current proof structure:
  fc ≥ 2 → CL ≥ 2n → (CL ≤ 2n sorry) → CL = 2n → fc = 2 → palindromic → EC → False

Use:
  fc ≥ 2 → (fc = 2 for all procs) → CL = 2n → palindromic → EC → False

Where "fc = 2 for all procs" is proved by:
  Suppose fc(q) ≥ 3 for some q. Entry conflict at q → False.

This requires a new lemma: fc_ge3_entryConflict that doesn't depend on CL = 2n.

This would be cleaner but requires building the entry conflict argument for
the fc ≥ 3 case, which is different from the existing palindromic EC.

==========================================================================
EASIEST IMPLEMENTATION
==========================================================================

The EASIEST way to fill the sorry might be:

For binary procs: fc is even and ≥ 2. If fc ≥ 4: binary fires 4+ times.
  By the "no binary 2-cycle" lemma (already proved): binary run length ≤ 1.
  So between any two firings of binary p, another proc must fire.

  Consider binary p with fc(p) = 4. It fires at steps a₀, a₁, a₂, a₃.
  Values: v, 1-v, v, 1-v at these steps.
  At step a₂: p has value v (same as a₀).
  Since p didn't fire between a₁+1 and a₂: p stayed at value v.
  All other procs at step a₂ have values determined by the walk between a₁ and a₂.

  The configs at a₀ and a₂ both have p = v. If they're identical: collision.
  They're not always identical (Part 8 showed this).

  BUT: the context (left, v, right) at a₀ and a₂ may differ.
  When it DOES match some non-mover step's context: EC.
  When it doesn't: we need another argument.

For ternary procs: fc ≥ 3, fires 3 times. Values cycle through all 3 values.
  After 3 firings: returns to original. The third value appears exactly once
  in the firing sequence.

  The walk structure (zero winding) means: after traversing CW and CCW,
  the neighborhood returns (approximately) to its original state.
  The third firing's context tends to match a non-mover context.

BOTTOM LINE: The sorry requires a non-trivial entry conflict argument
for the fc ≥ 3 case. This is NOT just "binary parity + config distinctness"
as the current sketch claims. It requires the full power of the entry
conflict machinery applied to the fc ≥ 3 scenario.
"""

print(__doc__)
