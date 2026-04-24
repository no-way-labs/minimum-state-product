#!/usr/bin/env python3
"""
Investigate whether the 3rd binary processor's parity constraint kills
the sorry case at n ≥ 9.

At n=5, ms=[2,3,2,3,3], t=1: binaries at 0,2. Only 2 binary.
The h3bin condition (≥ 3 binary) is NOT satisfied at n=5!

At n=9, ms=[2,3,2,3,2,3,3,3,3], t=1: binaries at 0,2,4. Has 3 binary.

In the sorry-case phase (full ring walk), each binary fires once (odd).
With 3 binary processors all firing odd times in the sorry phase,
and needing even total fires over the cycle:
  Each binary needs odd fires in other phases.

But the sorry is trying to show J+K ≤ 1 per phase.
If ALL phases have J+K ≤ 1 (no mixed phases), what are the constraints?

fc(L) + fc(R) ≤ fc(t) (the sparse bound, sorry line 1129).
fc(L) even, fc(R) even (binary).
fc(t) ≥ 3 (ternary fires at least 3 times).

If fc(t) = 3: fc(L) + fc(R) ≤ 3. With fc(L) even, fc(R) even:
  fc(L) = 0 or 2, fc(R) = 0 or 2, sum ≤ 3.
  Options: (0,0), (0,2), (2,0), (2,2). Sum: 0, 2, 2, 4.
  (2,2) sum=4 > 3: excluded. So fc(L) ≤ 2, fc(R) ≤ 2, fc(L)+fc(R) ≤ 2.

But hfull says ALL processors fire: fc(L) ≥ 1, fc(R) ≥ 1.
  fc(L) ≥ 1 and even: fc(L) = 2.
  fc(R) ≥ 1 and even: fc(R) = 2.
  fc(L) + fc(R) = 4 > 3 = fc(t). Contradiction!

Wait, this contradicts the sparse bound fc(L)+fc(R) ≤ fc(t)!
If fc(t) = 3: fc(L) = 2, fc(R) = 2, sum = 4 > 3. Contradiction.
So fc(t) ≥ 4.

If fc(t) = 4: fc(L)+fc(R) ≤ 4. fc(L)=2, fc(R)=2: OK.

But then: 4 phases, each with J+K ≤ 1. fc(L)=2 means L fires in 2 phases.
fc(R)=2 means R fires in 2 phases. Total J+K across phases = 4.
4 phases with J+K ≤ 1 each: max total = 4. Exactly 4. Each phase has J+K=1.
2 phases have L fire (J=1, K=0), 2 phases have R fire (J=0, K=1).
All one-sided!

What about the THIRD binary processor (proc 4 at n=9)?
proc 4 has binary m=2. Its fire count is even and ≥ 2 (by hfull and binary parity).
In each phase, how many times does proc 4 fire?

Proc 4 is NOT a first-neighbor of t (first-neighbors are L=0 and R=2).
Proc 4 is a "second-neighbor" of t (or further). Its fires within phases
are not directly constrained by the J+K ≤ 1 bound.

Actually, the key insight might be different. Let me think about what
the Lean proof actually needs.

The Lean theorem `allNormalForm_false2` assumes ALL phases are normalForm,
then derives False. It doesn't need to show mixed phases have EC -- it
assumes they've already been eliminated!

The normalForm condition means: each phase is one-sided (J+K ≤ 1) and
has a specific tight structure. The theorem then uses the sparse bound
and fire counts to derive a contradiction.

Wait, re-reading: the h_sparse sorry at line 1129 IS the "J+K ≤ 1" bound.
The sorrys at 1012/1077/1121 are inside the proof of h_phase_le1 (line 897),
which proves J+K ≤ 1 per phase.

h_phase_le1 is used to prove h_sparse (fc(L)+fc(R) ≤ fc(t)).
Then h_sparse + fire counts lead to contradiction.

So the sorrys at 1012/1077/1121 ARE about showing mixed phases have EC.
And we showed that at n=5, mixed phases CAN exist without EC.
But at n=9, they DON'T (computationally).

The question: WHY don't they exist at n=9?

HYPOTHESIS: The third binary processor (proc 4) at n=9 provides the
additional constraint that kills mixed phases. At n=5, there are only
2 binary processors, so the constraint is weaker.

Let me check: at n=9, does the all-adjacent + ¬EC + mixed phase imply
that some processor has duplicate configs?
"""

def check_config_space(n, ms, t):
    """Check if a full-ring-walk phase can fit in the config space without EC."""
    lt = (t - 1) % n
    rt = (t + 1) % n
    prod = 1
    for m in ms:
        prod *= m
    threshold = 4 * 3**(n-2)

    print(f"n={n}, ms={ms}, t={t}")
    print(f"Product: {prod}, threshold: {threshold}, sub: {prod < threshold}")
    print(f"Binaries: {[i for i in range(n) if ms[i] == 2]}")

    # A full-ring-walk phase has n steps (n-1 non-t fires + 1 t-fire).
    # Each step produces a distinct config.
    # In the full cycle with mt phases: mt * (n_steps_per_phase) configs total.
    # But phases can have different lengths.
    # Minimum cycle length for all-adjacent + mixed with mt=4: at least 4*(n-1)+4 = 4n.
    # At n=9: minimum ~36 configs. Product = 5832. 36 << 5832, so space is not the issue.

    # The issue is more subtle: it's about boundary triple collisions.
    # In the sorry phase, each proc's mover triple is determined by the walk.
    # With n=9 and 3 binary procs, each binary has m=2, contributing 1 bit
    # to boundary triples. The constraint is that no proc's mover triple
    # appears as a non-mover triple.

    # For the full ring walk at n=9:
    # Phase: 2, 3, 4, 5, 6, 7, 8, 0, then 1.
    # Proc 4 fires at step 2 (0-indexed from phase start).
    # Its mover triple: (val_3_after_3fires, val_4_old, val_5_old)
    # Non-mover triples at proc 4:
    #   Step 0 (R fires): (val_3_old, val_4_old, val_5_old)
    #   Step 1 (RR fires): (val_3_old, val_4_old, val_5_old) [3 hasn't fired yet... wait]

    # Actually step 1 is when proc 3 fires. At step 0: proc 2 fires.
    # After step 0: proc 2's value changed. Proc 3's value = old.
    # Step 1: proc 3 fires. Before: (val_2_new, val_3_old, val_4_old).
    # Boundary at proc 4 at step 1: (val_3_old, val_4_old, val_5_old). Same as step 0!
    # But step 0 boundary at proc 4: (val_3_old, val_4_old, val_5_old).

    # So boundary at proc 4 is IDENTICAL at steps 0 and 1 (both non-mover for proc 4).
    # That's fine for non-mover-to-non-mover -- EC requires mover == non-mover.

    # Mover triple at proc 4 (step 2): boundary = (val_3_new, val_4_old, val_5_old).
    # val_3_new ≠ val_3_old (proc 3 fired). So mover triple ≠ non-mover triple.
    # NO EC at proc 4.

    # For proc 4's later non-mover steps:
    # Step 3 (proc 5 fires): boundary at 4 = (val_3_new, val_4_new, val_5_old). ← proc 4 fired at step 2!
    # So val_4 changed at step 2. Now it's val_4_new.
    # Steps 3-7 have val_4 = val_4_new (proc 4 doesn't fire again).
    # Mover triple was (val_3_new, val_4_old, val_5_old).
    # Non-mover at step 3: (val_3_new, val_4_new, val_5_old). Different in val_4.
    # No EC.

    # This analysis shows that WITHIN the phase, no EC at any processor.
    # (Same as the simulation confirmed earlier.)

    # The question is about CROSS-PHASE EC: mover triple in sorry phase
    # matching non-mover triple in another phase.

    print("\n  Cross-phase analysis:")
    print("  In sorry phase, proc 4 mover triple = (val_3_new, val_4_old, val_5_old)")
    print("  In another phase, proc 4 non-mover triple = (val_3', val_4', val_5')")
    print("  EC requires all three components equal.")
    print("  val_4_old = proc 4's value at START of sorry phase.")
    print("  In another phase, val_4' = proc 4's value at some step in that phase.")
    print("  Proc 4 is binary: only values 0 and 1. So val_4' = val_4_old with prob ~1/2.")
    print("  The constraint that proc 4's value matches across phases is meaningful.")
    print()

    # At n=9 with sub-threshold product, the cycle is trying to visit
    # many configs without repeating boundary triples. With 3 binary procs,
    # there are only 2^3 = 8 possible combinations of binary values.
    # Each combination constrains boundary triples at neighboring processors.

    # The sub-threshold product constraint (prod < 4·3^(n-2)) means the
    # total config space is small. With binary procs limiting the space,
    # cross-phase EC becomes increasingly likely as n grows.

    # Let me compute: how many distinct boundary triples can proc 4 have?
    # proc 4 neighbors: proc 3 (m=3) and proc 5 (m=3 at n=9).
    # No wait: ms = [2,3,2,3,2,3,3,3,3]. proc 4 has m=2, neighbors:
    # proc 3 (m=3) and proc 5 (m=3).
    # wait, ms[4] = 2 at n=9 with ms=[2,3,2,3,2,3,3,3,3].
    # proc 4's boundary: (ms[3], ms[4], ms[5]) = (3, 2, 3).
    # Total triples: 3*2*3 = 18. Mover triples: those where proc 4 fires.
    # Non-mover triples: those where proc 4 doesn't fire.
    # Over the cycle, proc 4 fires fc(proc4) ≥ 2 times (even).
    # Non-mover steps: CL - fc(proc4).
    # Each mover triple must differ from all non-mover triples (no EC).
    # With only 18 possible triples, after ~18 steps, pigeonhole forces
    # some triple to repeat. But repeat of non-mover triples is OK;
    # repeat of mover triples is OK. EC requires mover = non-mover overlap.

    # How many mover triples can proc 4 have? fc(proc4) ≥ 2.
    # If all mover triples are distinct: at most 18.
    # Non-mover triples must avoid all mover triples. So at most 18 - fc4
    # distinct non-mover triples. But non-mover steps = CL - fc4.
    # If CL > 18: some non-mover triples must repeat. That's fine.
    # EC requires mover triple IN non-mover set. That's what we're avoiding.

    # With 18 total triples and fc4 mover triples + (18-fc4) possible
    # non-mover triples: feasible if CL ≤ 18 / pigeonhole doesn't force overlap.

    print(f"  Proc 4: boundary space = {ms[(4-1)%n]} * {ms[4]} * {ms[(4+1)%n]} = {ms[3]*ms[4]*ms[5]}")
    print(f"  Under sub-threshold: plenty of room.")
    print()
    print("  The sorry case is NOT impossible by simple counting.")
    print("  It requires a structural argument about the ring topology + binary parity.")

check_config_space(9, [2, 3, 2, 3, 2, 3, 3, 3, 3], 1)

print("\n" + "="*60)
print("CONCLUSION: At n=5, sorry cases exist in ¬EC cycles (but n=5 has only 2 binary).")
print("At n≥7 with 3+ binary, no sorry cases found computationally.")
print("The additional binary processor's parity constraint likely kills sorry cases.")
print()
print("The PROOF STRATEGY should be:")
print("1. Sorry 1 (line 1012): Prove vacuously true (fL>a ∧ fR>a impossible).")
print("2. Sorrys 2,3 (lines 1077, 1121): Use the third binary processor's")
print("   parity constraint + sub-threshold product to show the sorry case")
print("   forces a global EC (cross-phase boundary triple collision).")
print("3. Alternative: prove the backward chain terminates by using the")
print("   sub-threshold product bound to limit the number of distinct configs.")
print()
print("SIMPLEST FIX: For sorrys 2,3, instead of extending the mk_ec chain")
print("indefinitely, use gap1_ec on the FIRST step of the phase.")
print("moverAt(a-1) = t. moverAt(a) = R or L.")
print("gap1_ec checks: moverAt(a) adj to moverAt(a-1). If not: EC.")
print("Under ¬EC: always adjacent. So gap1_ec doesn't help.")
print()
print("ALTERNATIVE FIX: The mixed phase requires J≥1 AND K≥1.")
print("The phase starts at R (if fR=a) or L (if fL=a).")
print("It must reach the other side (L or R) through a ring walk.")
print("Under gap1_ec: consecutive movers adjacent. Walk goes one direction.")
print("In an n=9 ring, the walk covers n-2 intermediate processors.")
print("Each fires at least once. Each contributes configs.")
print("The third binary proc (proc 4) fires once in this walk.")
print("Its parity requires odd fires in other phases too.")
print("Combined with J+K=1 per phase and fc(t)≥3:")
print("This creates an over-constrained system that forces EC.")
