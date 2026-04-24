"""
Cross-Phase EC: Final summary (fast version).
"""

def main():
    print("=" * 60)
    print("CROSS-PHASE EC ANALYSIS: DEFINITIVE RESULTS")
    print("=" * 60)

    print("""
THEOREM STRUCTURE (3 steps):

STEP 1 (PROVED): Phase balance + normalForm => all phases one-sided.
  fc(bL) + fc(bR) = fc(t), J_i + K_i <= 1, fc(t) terms => all J_i + K_i = 1.

STEP 2 (PROVED): Some phase has length >= 2.
  Sum of lengths = CL - fc(t) >= fc(t) + 2(n-3) > fc(t) for n >= 4.
  Since all fc(t) phases have length >= 1, some has length >= 2.

STEP 3A (PROVED): In a phase where binary fires at position j < length-1:
  Forward window [j+1, end] has constant triple at t.
  Step j+1 (nonmover) and step s (mover) have same triple => EC at t.

STEP 3B (GAP): Binary-Fires-Last (BFL) case.
  When binary fires at the LAST interior step (j = length-1):
  No forward window exists. Triple at t CHANGES at t-fire (S component).
  EC at binary procs impossible (S always differs mover vs nonmover).
  This case CANNOT give EC from the constant-triple argument alone.

COMPUTATIONAL EVIDENCE:
  At n=4, CL=10: 150/540 (27.8%) of valid mover words are all-BFL.
  At n=4, CL=12: 1350/8580 (15.7%) are all-BFL.
  These are genuine abstract mover words satisfying ALL constraints.

BINARY EC IMPOSSIBILITY (PROVED):
  At every mover step for binary proc bL: S = pre-fire value v.
  At every nonmover step: S = post-fire value 1-v.
  v != 1-v always. No EC at binary procs. QED.

IMPLICATIONS FOR AllNormalFormFalse2.lean:1265:
  The sorry needs hasEntryConflict gc.
  The cross-phase argument at t covers the non-BFL case (~73-89%).
  The BFL case (11-28%) requires a DIFFERENT mechanism.

  The sorry CANNOT be filled by the cross-phase EC at t alone.

OPTIONS TO COMPLETE THE PROOF:
  (A) Show BFL mover words are impossible under full hypotheses
      (n >= 9, sub-threshold, converges, etc.)
  (B) Find EC at far ternary procs in the BFL case
  (C) Use the universal EC theorem (BinSCC Expl 10, analytically proved)
  (D) Bypass this sorry via the zero-winding / shadow cycle approach

SCRIPTS:
  cross_phase_ec_proof.py   - Main analysis
  cross_phase_ec_verify.py  - Step-by-step verification
  cross_phase_ec_compute.py - Abstract mover word enumeration
  cross_phase_ec_bfl.py     - BFL mechanism analysis
  cross_phase_ec_n5plus.py  - BFL feasibility at n >= 5
""")


if __name__ == "__main__":
    main()
