#!/usr/bin/env python3
"""
RA10 SUMMARY: Direct proof that sweep + non-consecutive binary → False.

FINDINGS:
=========

1. Sweep mover words DO EXIST for ≥3 binary (no triple), contrary to initial hope.
   Found at n=7 (4 words per config) and n=9 (8 words per config).
   All have |disp| = 2n exactly (minimum sweep displacement).

2. These sweep words are NOT uniform (have CCW wiggles):
   - n=7: 2 CCW steps, 16 CW steps
   - n=9: 3 CCW steps, 21 CW steps
   Formula: CCW = (n-3)/2 for n odd, (n-4)/2 for n even (with exactly 3 binary)

3. ALL sweep good cycles have NO ENTRY CONFLICT:
   - n=7: 0/64 have EC (7 binary configs × ~9 transition combos)
   - n=9: 0/512 have EC per binary config (many configs checked)
   This means the trichotomy approach (EC ∨ permanent ∨ isolated) will
   ALWAYS give "isolated" for sweep non-consecutive binary.

4. The existing WaterfallBridge/shadow approach handles ONLY uniform sweeps
   (length 2n, all procs fire exactly 2). Our sweeps have length 3n-k with
   mixed fire counts (binary=2, ternary=3).

5. Default-transition convergence check shows sweep cycles DON'T converge
   (136-140 trapped non-good configs at n=7).

PROOF STRATEGY:
===============

The recursion in `sweep_sub_threshold_false` can be eliminated by providing
a DIRECT proof for the non-consecutive binary sweep case. Three approaches:

APPROACH 1: Displacement-parity impossibility (FAILS for n odd)
  For n even: CL = 3n-3 is odd, disp must be odd. So |disp| ≥ 2n+1.
  Need CL ≥ 2n+1, i.e., 3n-3 ≥ 2n+1, i.e., n ≥ 4. True.
  But |disp| = 2n+1 CAN be achieved. No contradiction.
  For n odd: CL is even, |disp| = 2n is achievable. No contradiction.

APPROACH 2: Wiggle Shadow Cycle (WORKS)
  The sweep words with ≥3 non-adjacent binary are "single-wiggle" words.
  The Wiggle Shadow Cycle theorem (CIC Expl 12-15) constructs a second
  good cycle of length 2n+2, disjoint from the original.
  Two disjoint good cycles → ¬converges → contradiction with hconv.

  Lean implementation: need to verify that:
  a) The sweep mover word satisfies the wiggle word conditions
  b) The wiggle shadow construction is formalized (or can be applied)
  c) This doesn't import anything that creates a cycle

APPROACH 3: Direct shadow on projected walk (CLEANEST)
  Extract the uniform 2n sub-walk by removing wiggle pairs.
  Build shadow configs for the 2n-walk.
  Show shadow configs are disjoint from original cycle configs.
  Apply shadowTrap_not_converges.

  This reuses the existing shadow machinery (WaterfallCycle + shadow theorem)
  by reducing the wiggle sweep to a uniform sweep.

APPROACH 4: fc-parity argument (NEW, SIMPLEST)
  Key observation: uniformCW → all fireCount equal → contradiction with
  binary+ternary. So sweep with binary → NOT uniformDirection.
  But: does NOT uniformDirection + sweep → False directly?
  The Lean codebase has not_uniformDirection_and_isOddWinding_of_hasGe3Binary
  but that's for odd winding, not sweep.
  There might be an analogous theorem for sweep.

APPROACH 5: Binary fire-count constraint (NEW IDEA)
  In a sweep with fc(p) = ms(p):
  - Binary proc p fires exactly 2 times
  - Between the two firings, the walk wraps around ~once
  - The walk visits p's left neighbor and right neighbor
  - At the second firing, c[p] is flipped (binary), so the mover triple differs
  - The TWO mover triples at p have different c[p] values (0 vs 1)
  - Non-mover triples at p during the wrap cycle through many (L,R) combos
  - BUT: the mover triples have specific (L,R) values
  - If these (L,R) values happen to NOT appear among non-mover triples → no EC
  - This is consistent with our observation (no EC at binary procs)

  So EC doesn't help. Must use shadow or convergence directly.

RECOMMENDATION:
===============

APPROACH 2 (Wiggle Shadow Cycle) is the most mathematically solid and
aligns with the existing proof infrastructure. The key facts are:

1. Sweep + ≥3 binary (no triple) → walk has isolated CCW wiggles
2. Walk satisfies single-wiggle conditions
3. Wiggle Shadow Cycle theorem gives second good cycle
4. Two good cycles → ¬converges
5. Combined with hconv → False

In Lean: this would replace the `subThreshold_binary_core_false_residual`
call at line 1034 of CaseObstructions.lean with a direct application of
the wiggle shadow cycle theorem (once formalized).

However, if the wiggle shadow cycle is not yet formalized in Lean,
APPROACH 3 might be more practical: reduce to the existing uniform
shadow machinery by extracting a 2n sub-walk.

ALTERNATIVE (SIMPLEST Lean change):
====================================

Instead of proving sweep + non-consec binary → False via shadow,
prove it by showing sweep → uniformDirection for minimum-length cycles
(fc = ms), then contradiction:

  Sweep (|disp| ≥ 2n) + fc(p) = ms(p) + ≥3 binary →
  uniformDirection → fireCount constant → binary=ternary → contradiction.

But this doesn't work because sweep cycles are NOT uniformDirection!
The data clearly shows they have CCW wiggles.

ACTUAL SIMPLEST APPROACH:
=========================

The n ≥ 9 constraint in sweep_sub_threshold_false might help.
For n ≥ 9 with exactly 3 binary: CL = 3n-3, |disp| = 2n.
For n ≥ 9 with ≥ 4 binary: CL = 3n-k ≤ 3n-4.
The data at n=8 shows NO sweep words exist for k ≥ 4 (CL = 20 < 16 needed).
Wait: n=8 has CL = 3*8-4 = 20, need |disp| ≥ 16. 20 ≥ 16. But no words found.

Actually the data at n=8 k=4 DID find sweeps! bins=[0,1,4,5] has sweep.
So k=4 binary can have sweeps too.

The sweep existence depends on the specific binary placement.

BOTTOM LINE: The direct proof must use shadow/convergence machinery.
There's no simple counting argument that rules out sweeps.
"""

print(__doc__)
