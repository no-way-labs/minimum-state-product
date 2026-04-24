#!/usr/bin/env python3
"""
The inductive closure for the sorry cases.

Sorry 2 context (fR = a, fL > a):
  - moverAt(a) = rt (= R)
  - LL fires in [a, fL), with last LL fire at fL-1
  - First LL fire at fLL
  - left³(t) fires in [a, fLL)
  - Goal: EC somewhere

The backward chain extends:
  a: R fires
  a+1: must be adj to R, not R (first R at a, or R could re-fire?)
  Actually wait: R fires at a, and fR is first R fire, so fR = a.
  But R could fire AGAIN later. However fR = first fire, not only fire.

  The chain for the mk_ec_left approach goes backward from fL:
  fL-1: LL fires (wmax3 = fL-1)
  fLL: first LL fire
  Need: no left³t in [a, fLL).
  If left³t fires in [a, fLL): sorry.

  The question: can we do the same trick at left³t?
  Find first left³t fire fL3 in [a, fLL).
  Between a and fL3: no left⁴t?
  If no left⁴t: EC at left³t between fL3 (mover) and a (non-mover).
  If left⁴t: continue to left⁴t.

  This INDUCTION terminates because we're walking backward on the ring
  (left³t, left⁴t, ...) and eventually reach rt (which fired at step a).

  When we reach a processor p such that leftⁱ(t) = rt, then we have
  i = n (since left^n(t) = t, and left^(n-1)(t) = rt).

  Wait: left^k(t) for k = 1,...,n-1 gives all other processors.
  left^(n-1)(t) = right(t) = rt.

  At step k = n-2 of the induction (checking left^(n-1)(t) = rt):
  We need no left^n(t) = t fires in [a, fRt). But t doesn't fire in the
  phase. So there's NO t fire in [a, fRt). EC at rt!

  Let me formalize this.
"""

def analyze_induction(n, t):
    """Trace the induction for the sorry case."""
    lt = (t - 1) % n
    rt = (t + 1) % n

    print(f"n={n}, t={t}, lt={lt}, rt={rt}")
    print()

    # The induction: for k = 2, 3, ..., n-1, check if left^k(t) fires
    # before the first left^(k-1)(t) fire.
    #
    # Base: k=2 (LL fires before first L fire at fL, gap = 0 -> sorry)
    # Step: k=3 (left³t fires before first LL fire at fLL -> sorry)
    # ...
    # Step: k=n-1 (left^(n-1)(t) = rt fires before first left^(n-2)(t) fire)
    #
    # At k=n-1: we need to check if left^n(t) = t fires in [a, f_{n-1}).
    # But t doesn't fire in the phase [a, s). So left^n(t) = t does NOT fire.
    # Therefore: EC at left^(n-1)(t) = rt!

    print("=== Induction trace ===")
    for k in range(2, n):
        p = (t - k) % n   # left^k(t)
        pp = (t - (k-1)) % n  # left^(k-1)(t) = right neighbor of p in the chain
        ppp = (t - (k+1)) % n  # left^(k+1)(t) = needed for the next step
        print(f"  k={k}: left^{k}(t) = proc {p}")
        print(f"    Try EC at proc {p} between first-fire-of-{p} (mover) and step a (non-mover)")
        print(f"    Need: no left^{k+1}(t)={ppp}, left^{k}(t)={p}, left^{k-1}(t)={pp} fires in [a, first-fire-of-{p})")
        print(f"    No left^{k}(t): first fire of {p} is the earliest -> OK")
        print(f"    No left^{k-1}(t): first fire of {pp} is after first fire of {p} -> OK")
        if k < n - 1:
            print(f"    left^{k+1}(t) = {ppp}: CASE SPLIT (gap or no gap)")
            print(f"      If no left^{k+1}(t) in interval: EC at {p}. DONE.")
            print(f"      If left^{k+1}(t) fires: induction continues to k={k+1}")
        else:
            # k = n-1: left^n(t) = t
            assert ppp == t, f"Expected left^{k+1}(t) = t, got {ppp}"
            print(f"    left^{k+1}(t) = {ppp} = t: t DOES NOT FIRE in the phase!")
            print(f"    So no left^{k+1}(t) fires in interval -> EC at {p}. DONE!")

    print()
    print("=== Conclusion ===")
    print(f"The induction terminates at k={n-1} because left^{n}(t) = t,")
    print(f"which doesn't fire in the phase. This gives EC at left^{n-1}(t) = {rt}.")
    print()

    # But wait: is this the RIGHT EC construction?
    # At k = n-1: left^(n-1)(t) = rt.
    # EC at rt between first-fire-of-rt (= step a = fR) and... what non-mover step?
    #
    # The mk_ec construction uses: EC at p between mover step fP and non-mover step v,
    # where left(p), p, right(p) don't change in [v, fP).
    #
    # For p = left^(n-1)(t) = rt:
    #   left(rt) = t, right(rt) = rrt = right²(t)
    #   Mover step: fRt = first fire of rt in the interval
    #   Non-mover step: a
    #   Need: no t, rt, rrt fires in [a, fRt)
    #   - no t: phase condition
    #   - no rt: first fire of rt IS fRt
    #   - no rrt: ... is this guaranteed?

    print("WAIT: The EC construction at rt needs no rrt fires in [a, first-rt-fire).")
    print("But first-rt-fire IS step a (fR = a)! The interval [a, a) is empty!")
    print("So the condition is vacuously satisfied!")
    print()
    print("Hmm, but that's the BASE case: fR = a means EC at rt is trivially available.")
    print("The PROBLEM is that the EC at rt between fR (mover) and some non-mover step")
    print("requires the non-mover step to have the SAME boundary triple.")
    print("Since fR = a, we need a non-mover step for rt with the same triple as step a.")
    print("But step a IS the mover step for rt. We need ANOTHER step where rt is non-mover")
    print("with the same (t_val, rt_val, rrt_val).")
    print()
    print("Actually, the mk_ec construction works differently. Let me re-think.")
    print()

    # Re-read mk_ec_left: EC at lt between v (non-mover for lt) and fL (mover for lt).
    # Requires: no llt, lt, t fires in [v, fL). Then boundary at lt at v equals
    # boundary at lt at fL (since left(lt)=llt, lt, right(lt)=t don't change).
    # v is non-mover for lt, fL is mover for lt. Same boundary -> EC.
    #
    # For the INDUCTION at level k:
    # p = left^k(t)
    # left(p) = left^(k+1)(t), right(p) = left^(k-1)(t)
    # Mover step: fP = first fire of p in [a, f_{k-1})
    # Non-mover step: a (since moverAt(a) = rt ≠ p for k >= 2 and p ≠ rt)
    #
    # Need: no left^(k+1)(t), left^k(t), left^(k-1)(t) fires in [a, fP).
    # - no left^k(t): first fire of p is fP -> OK
    # - no left^(k-1)(t): first fire of left^(k-1)(t) is f_{k-1} > fP -> OK
    #   (since fP < f_{k-1} by construction)
    # - no left^(k+1)(t): CASE SPLIT
    #
    # At k = n-1: p = rt. left^n(t) = t. No t fires in phase -> EC at rt.
    #
    # But wait: p = rt = left^(n-1)(t).
    # Non-mover step a has moverAt(a) = rt = p. So a IS a mover step for p!
    # Can't use a as the non-mover step.
    #
    # Need a DIFFERENT non-mover step for rt near step a.

    print("PROBLEM: At k=n-1, p = rt. moverAt(a) = rt. So step a is a MOVER step for rt.")
    print("We need a non-mover step for rt as the witness.")
    print()
    print("But who is the non-mover step? It must be a step where rt doesn't fire,")
    print("AND the boundary triple at rt matches the boundary at step fRt (mover step).")
    print()
    print("Actually, the induction doesn't go all the way to k=n-1 starting from")
    print("the 'other side'. Let me re-read the sorry carefully.")
    print()

    # Re-reading sorry 2 (line 1077):
    # Context: fR = a (R fires at a), fL > a.
    # The code tries ec_caseC_RL(fR, fL), which needs no LL in [fR, fL).
    # If LL fires in [fR, fL): code finds first LL (fLL) and last LL (wmax3 = fL-1).
    # If gap after last LL: mk_ec_left works.
    # If no gap (LL at fL-1): try EC at LL between fLL (mover) and a (non-mover).
    #   moverAt(a) = R ≠ LL, so a IS a non-mover step for LL. ✓
    #   Need: no left³t, LL, L in [a, fLL).
    #   No LL: fLL is first. No L: fL > fLL. left³t: CASE SPLIT -> sorry.

    # For the induction at general k:
    # p = left^k(t)
    # Non-mover step: a. moverAt(a) = rt. Is rt different from p?
    # rt = left^(n-1)(t). So p ≠ rt iff k ≠ n-1.
    # For k = 2,...,n-2: p ≠ rt, so a IS a valid non-mover step. ✓
    # For k = n-1: p = rt = moverAt(a). Can't use a as non-mover.

    # So the induction works for k = 2,...,n-2.
    # At k = n-2: p = left^(n-2)(t) = right²(t) = rrt.
    # Need: no left^(n-1)(t)=rt, left^(n-2)(t)=rrt, left^(n-3)(t)=right³(t) in [a, fP).
    # Wait, that's wrong. The non-mover constraints at p = left^k(t) are:
    #   no left(p) = left^(k+1)(t) fires in [a, fP)
    #   no p = left^k(t) fires in [a, fP)
    #   no right(p) = left^(k-1)(t) fires in [a, fP)

    # At k = n-2: p = rrt.
    # left(rrt) = right³(t) = left^(n-3)(t)
    # Wait, left(rrt) in ring = (rrt-1)%n. rrt = (t+2)%n. left(rrt) = (t+1)%n = rt.
    # Hmm, left and right depend on ring direction.
    # In the ring: left(p) = (p-1)%n, right(p) = (p+1)%n.
    # left(rrt) = (rrt-1)%n = (t+1)%n = rt.
    #
    # So at k=n-2, p = rrt = left^(n-2)(t) = (t - (n-2))%n = (t+2)%n.
    # left(p) = rt = left^(n-1)(t).
    # right(p) = right³(t) = left^(n-3)(t).
    #
    # Need: no rt, rrt, right³t fires in [a, fP).
    # No rt: moverAt(a) = rt fires at a. Is a in [a, fP)? Yes, a ≤ a < fP.
    # So rt DOES fire at step a in [a, fP). The condition fails!

    print("CRITICAL ISSUE at k=n-2:")
    print(f"  p = rrt = {(t+2)%n}")
    print(f"  left(p) = rt = {(t+1)%n}")
    print(f"  Need: no rt fires in [a, fP). But moverAt(a) = rt fires at a!")
    print(f"  So rt fires in [a, fP) -> condition for EC at rrt FAILS.")
    print()
    print("The induction BREAKS at k=n-2 because the starting mover (rt) is the")
    print("left neighbor of rrt, and it fires within the interval.")
    print()
    print("So the induction only works for k = 2,...,n-3.")
    print("At k = n-3: p = right³(t) = left^(n-3)(t).")
    print(f"  p = {(t+3)%n}, left(p) = {(t+2)%n} = rrt")
    print(f"  Need: no rrt in [a, fP). moverAt(a) = rt ≠ rrt. So no rrt at step a. ✓")
    print(f"  But rrt could fire at step a+1 or later.")
    print(f"  If fR = a and moverAt(a+1) needs to be adj to rt: moverAt(a+1) ∈ {{t, rrt}}")
    print(f"  t doesn't fire -> moverAt(a+1) = rrt.")
    print(f"  So rrt fires at a+1, which IS in [a, fP) if fP > a+1.")
    print(f"  If fP = a+1: interval [a, a+1) has only step a, where rt fires. No rrt. OK.")
    print(f"  If fP > a+1: rrt fires at a+1 in [a, fP). EC at p FAILS.")
    print()
    print("The chain of fires starting from a looks like:")
    print("  a: rt fires")
    print("  a+1: rrt fires (adj to rt, not t)")
    print("  a+2: right³t fires (adj to rrt)")
    print("  ...")
    print("  a+k-2: left^(k-1)(t) fires")
    print("  So fP (first fire of p=left^k(t)) should be at a+k-1.")
    print("  And left^(k+1)(t) first fires at a+k-2.")
    print("  The interval [a, fP) = [a, a+k-1) contains fires at a, a+1, ..., a+k-2.")
    print("  left(p) = left^(k+1)(t) fires at a+k-2.")
    print()
    print("So for ALL k, left(p) fires in [a, fP). The mk_ec construction NEVER works")
    print("directly from step a!")
    print()
    print("We need a DIFFERENT non-mover step v > a for the EC construction.")
    print("Specifically, v should be AFTER the left(p) fire.")

    # NEW IDEA: Instead of using step a as non-mover, use step (a + k - 1)
    # which is after left(p) fires but before p fires.
    # Wait, fP = a+k-1 is p's fire step. We need v < fP.
    # At step a+k-2: left^(k+1)(t) = left(p) fires. After this step: left(p) has changed.
    # At step a+k-1: p fires. Before this: left(p) value is post-fire.
    # We need a non-mover step for p where (left(p), p, right(p)) matches the
    # boundary at p at step fP = a+k-1.
    #
    # What about step a+k-2? At that step, left(p) fires.
    # At step a+k-2: mover is left^(k+1)(t) = left(p). p is non-mover. ✓
    # Boundary at p at step a+k-2: (left(p)_old, p_val, right(p)_val)
    # Boundary at p at step a+k-1: (left(p)_new, p_val, right(p)_val)
    # left(p) changed (fired at a+k-2), so left(p)_old ≠ left(p)_new (if binary).
    #
    # So these DON'T match. The value of left(p) differs.
    #
    # What if left(p) is NOT binary? Then left(p)_old MIGHT equal left(p)_new.
    # For ternary (m=3): fire changes 0->1->2->0 or other permutation.
    # Not necessarily different from old value.

    print()
    print("=== Alternative: EC at p using step a+k-2 as non-mover ===")
    print("At step a+k-2: left(p) fires, p is non-mover.")
    print("Boundary at p: (left(p)_old, p_val, right(p)_val)")
    print("At step a+k-1: p fires.")
    print("Boundary at p: (left(p)_new, p_val, right(p)_val)")
    print("If left(p) is binary: left(p)_old ≠ left(p)_new. No EC.")
    print("If left(p) is ternary: could be equal. But transition is f(ctx) ≠ old,")
    print("so left(p)_new ≠ left(p)_old. Also no EC!")
    print()
    print("Wait: left(p) fired, so its value CHANGED: left(p)_new ≠ left(p)_old.")
    print("This is because firing means the new value differs from the old.")
    print("So boundary at p at step a+k-2 ALWAYS differs from step a+k-1")
    print("(in the left(p) component). No EC between these two steps.")
    print()

    # So adjacent-step EC doesn't work. Need to look further.
    # What about steps BEFORE a+k-2? At those steps, left(p) hasn't fired yet,
    # so left(p) value = left(p)_old. And at step a+k-1 (p fires),
    # left(p) value = left(p)_new ≠ left(p)_old. So no match.
    #
    # What about steps AFTER a+k-1? At those steps, p has already fired,
    # so p's value might differ. But p is non-mover at those later steps
    # (assuming p fires only once in this interval).
    # If p fires only once: p_val is different after step a+k-1.
    # So boundary at p changes in the p-component too.

    print("=== KEY REALIZATION ===")
    print("Within the sorry-pattern phase, EC at any interior processor p")
    print("is impossible because:")
    print("  - Before p fires: left(p) value is X (pre-fire)")
    print("  - After left(p) fires (one step before p): left(p) value is Y ≠ X")
    print("  - At p's fire step: boundary = (Y, p_old, right_old)")
    print("  - At all non-mover steps for p before left(p) fires: boundary = (X, p_old, right_old)")
    print("  - At non-mover step where left(p) fires: boundary = (X, p_old, right_old)")
    print("    Wait, at the step where left(p) fires, the config BEFORE the fire has X.")
    print("    So boundary at p = (X, p_old, right_old). This is a non-mover step for p.")
    print("    At p's fire step: boundary = (Y, p_old, right_old). Y ≠ X. No match.")
    print()
    print("So NO EC exists within the phase for any interior processor.")
    print("The EC must come from OUTSIDE the phase (global cycle constraint).")
    print()
    print("This means the sorry needs a GLOBAL argument, not a local-phase one.")
    print("The mk_ec constructions are inherently local (they use intervals within the phase).")
    print("A different approach is needed.")


analyze_induction(9, 1)
