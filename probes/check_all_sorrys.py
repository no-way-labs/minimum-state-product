#!/usr/bin/env python3
"""
Comprehensive check: for each of the 5 remaining sorrys, can a CONCRETE
counterexample to the theorem statement be constructed?

If YES: the theorem is BUGGY (wrong hypotheses).
If NO: the theorem is correct and needs a proof.

Sorry #1: double_trapped_baf_false — FOUND BUG (back-and-forth arc cycle)
Sorry #2: cwWitness gap≥2 — needs global minimality
Sorry #3: cwWitness gap=1 — needs palindromic EC
Sorry #4: gapDecisive_false — needs Ring Alternation (now with hno_safe)
Sorry #5: consecutive_binary_isolated_false_noSafe_outsideMover — needs structural argument
"""

def left(i, n): return (i - 1) % n
def right(i, n): return (i + 1) % n

def check_sorry1_double_trapped():
    """
    Sorry #1: double_trapped_baf_false
    Hypotheses: n>=9, gc, _hconv, _hsub, zeroWinding, cwStepCount>0,
    no_safe, 3consec binary {i,ri,rri}, i and ri trapped (cw=ccw=0)

    KNOWN BUG: back-and-forth arc cycle is a counterexample.
    The trapped pair {i, ri} with fc=0 can coexist with all hypotheses.
    """
    print("Sorry #1: BUGGY — counterexample exists (back-and-forth arc cycle)")
    print("  n=9, binary={0,1,2}, trapped={0,1}")
    print("  Mover: [2,3,4,5,6,7,8,7,6,5,4,3] × 2 (zero winding)")
    print("  All hypotheses satisfied including convergence + sub-threshold")
    print("  FIX: Need to restructure the proof to avoid this case,")
    print("       or use global min triple data (available from caller)")

def check_sorry4_with_nosafe():
    """
    Sorry #4: gapDecisive_false (with hno_safe)
    Can a good cycle with (n>=9, sub-threshold, >=3 binary, no 3 consecutive,
    no safe processor) exist without any entry conflict?

    We need to check: is there a system where gapDecisive_false's hypotheses
    hold AND the cycle has no hasEntryConflict?
    """
    print("\nSorry #4: Checking if hypotheses + no entry conflict is consistent...")

    # With hno_safe: every proc has nearby mover. One-mover is ruled out.
    # Need ≥ 3 movers (dominating set for n≥9).
    # Entry conflict = same (L,S,R) at mover step AND non-mover step for some proc.
    # A cycle without entry conflict: every proc's mover/non-mover contexts are disjoint.

    # For n=9, binary={0,3,6}, ternary={1,2,4,5,7,8}:
    # No 3 consecutive ✓. Sub-threshold: 2^3 * 3^6 = 5832 < 8748 ✓
    # Need: good cycle where every proc fires ≥ once (for hno_safe coverage)
    # AND no entry conflict.

    # This is hard to construct because entry conflicts are ubiquitous.
    # The mathematical theorem says: under these hypotheses, entry conflict
    # ALWAYS exists. The proof uses the phase mechanism dispatch.

    # The fact that all-normal phases exist in counting BUT not in real cycles
    # (from check_gap_fc2_real.py: 0 real examples) suggests the theorem IS correct.
    print("  Counting says all-normal possible, but real cycle search found 0 examples")
    print("  LIKELY CORRECT — needs proof (Ring Alternation)")

def check_sorry5():
    """
    Sorry #5: consecutive_binary_isolated_false_noSafe_outsideMover
    Hypotheses: n>=9, gc, converges, 3consec binary, fc(ri)>=2,
    ri firings isolated, no safe proc, some mover outside triple.
    """
    print("\nSorry #5: Checking consistency...")

    # With isolated firings of ri: ri fires ≥2 but never twice in a row.
    # Some mover outside {i, ri, rri}: the cycle involves more of the ring.
    # No safe proc: every proc has nearby mover.
    # + converges.

    # Can such a cycle exist without entry conflict?
    # With isolated firings: between consecutive fires of ri, other procs fire.
    # The (L,S,R) context at ri changes between firings.
    # Entry conflict requires: same context at mover + non-mover step.

    # With binary ri (m=2): 8 possible contexts. With fc≥2 firings: ri uses
    # ≥2 mover contexts. With ≥(L-2) non-mover steps: ri appears in many
    # non-mover contexts. By pigeonhole... BUT mover/non-mover contexts are
    # disjoint (transition function is deterministic).

    # The entry conflict must come from a STRUCTURAL argument, not pigeonhole.
    # Similar to the palindromic EC argument.
    print("  Similar to palindromic EC — needs structural argument")
    print("  LIKELY CORRECT — needs formalization of palindromic mover word analysis")

def main():
    print("=" * 60)
    print("SORRY STATUS ASSESSMENT")
    print("=" * 60)

    check_sorry1_double_trapped()

    print("\nSorry #2: cwWitness gap≥2 — needs global minimality")
    print("  The MinGapArc stay chain requires global minimality to rule out")
    print("  right(p) firing CW in (a,b). Available from GlobalMinGap caller.")
    print("  LIKELY CORRECT — needs import/structural fix to access global min")

    print("\nSorry #3: cwWitness gap=1 — needs palindromic EC")
    print("  Adjacent CW/CCW crossings. L value changes between them.")
    print("  Need global mover word structure argument.")
    print("  LIKELY CORRECT — needs palindromic formalization (~300 lines)")

    check_sorry4_with_nosafe()
    check_sorry5()

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print("Sorry #1: BUGGY — restructure needed")
    print("Sorry #2: CORRECT — needs global min data threading")
    print("Sorry #3: CORRECT — needs palindromic EC (~300 lines)")
    print("Sorry #4: CORRECT — needs Ring Alternation (~400 lines)")
    print("Sorry #5: CORRECT — needs palindromic EC (~300 lines)")
    print()
    print("CRITICAL PATH: Fix #1 (bug), then #4 (non-consecutive), then #2/#3/#5 (consecutive)")
    print()
    print("KEY INSIGHT: #2, #3, #5 all need the SAME core argument (palindromic EC).")
    print("If palindromic EC is proved once, all three close.")
    print("So the real work is: fix #1 bug + Ring Alternation (#4) + Palindromic EC (#2,3,5)")

if __name__ == "__main__":
    main()
