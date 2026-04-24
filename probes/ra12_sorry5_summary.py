"""
RA12 SORRY 5 — SUMMARY OF FINDINGS

QUESTION: Can the sorry at CaseObstructionsCore.lean:468 be discharged?

ANSWER: NO, not with entry conflict alone. But the fix is clear.

KEY FINDINGS:

1. THE ODD-PARITY CASE IS NON-VACUOUS.
   At n=9 with ms=[2,2,2,3,3,3,3,3,3], the double-sweep mover word
   [0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1] produces valid good cycles
   (distinct configs, cycle closes, no EC) that fall in the odd-parity residual.
   46,656 such EC-free cycles exist.

2. ENTRY CONFLICT IS NOT FORCED IN THE ODD-PARITY CASE.
   The double-sweep cycle has:
   - 3 consecutive binary at {0,1,2}
   - ri=1 has isolated firings, fc=2, gap=9
   - Both neighbors have ODD parity in the gap
   - NO entry conflict at ANY processor (all 9 procs clean)
   This is a genuine counterexample to closing the sorry via EC.

3. THE CORRECT FIX: ADD CONVERGENCE AS A HYPOTHESIS.
   CaseObstructions.lean has the CORRECT proof in
   `consecutive_binary_isolated_false_noSafe_outsideMover` (lines 899-938)
   which uses convergence (hconv) via `palindromic_phase_ec_residual`.

   CaseObstructionsCore.lean's `consecutive_binary_isolated_false'` dropped
   convergence from its hypotheses — that's why it has the sorry.

   The calling chain DOES have convergence available:
     subThreshold_obstruction_v2 (has hconv)
     -> nonZeroWinding_false (has hconv)
     -> oddWinding_nonUniform_false (has hconv at line 630)
     -> consecutive_binary_isolated_false' (DOES NOT take hconv!)

   FIX: Either:
   (a) Add `hconv : converges sys gc` to consecutive_binary_isolated_false'
       and use the palindromic_phase_ec_residual approach, OR
   (b) Replace the call to consecutive_binary_isolated_false' with a call to
       consecutive_binary_isolated_false from CaseObstructions.lean (which
       already takes hconv).

4. THE GOOD CYCLE WITHOUT EC DOESN'T FORM A VALID SYSTEM.
   At n=5, the EC-free cycle from the double-sweep word was tested as a
   complete system: it fails liveness (22 dead configs). This confirms
   M_5 = 96 is correct. The impossibility comes from convergence/liveness
   failure, not from entry conflict.

5. MATHEMATICAL MECHANISM:
   The odd-parity case needs convergence because EC alone cannot distinguish
   between "this mover word could be a good cycle" and "this good cycle
   belongs to a valid system." The convergence hypothesis provides the
   additional power needed to derive a contradiction.
"""

print(__doc__)
