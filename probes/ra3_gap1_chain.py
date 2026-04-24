#!/usr/bin/env python3
"""
Investigate the gap1_ec chain approach for closing the sorry.

The sorry cases have a chain of adjacent movers:
  Sorry 1: ...LL, L, [phase end t] with RR before R on the other side
  Sorry 2: ...left³t, LL, L, [fL=a, start from R side]
  Sorry 3: ...right³t, RR, R, [fR=a, start from L side]

All cases: a chain of ring-adjacent movers leading up to a fire.

KEY INSIGHT FROM THE LEAN COMMENTS: "gap1_ec at RR (step wmax2) checks
moverAt(wmax2-1): ≠ R (fR is first R), so only {RR, right³t} are problematic."

This means: for the chain ...X, LL, L, the mover before LL must be adjacent to LL.
Candidates: left³(t) or L. But L hasn't fired yet (LL fires BEFORE first L).
So mover before LL is left³(t) or LL itself (re-fire).

If left³(t): then by gap1_ec, we check mover before left³(t). If non-adjacent: EC.
If adjacent: it's left⁴(t). And so on.

This chain extends backward through the ring. Eventually it must reach a processor
that is NOT adjacent to the next one -> gap1_ec fires!

WAIT: the problem is that the chain CAN be fully adjacent all the way around.
In the sorry-L sequence: R, RR, 4, 5, 6, 7, LL, L, T -- every consecutive pair
IS ring-adjacent. So gap1_ec never fires within this chain.

But the chain is the ENTIRE ring walk. Can this happen in a phase where
both L and R fire? Let me think...

If fL > a and fR > a (sorry 1): The phase starts at moverAt(a) which is adj to t.
Let's say moverAt(a) is NOT lt or rt. But it must be adj to t, so it IS lt or rt.

If moverAt(a) = lt: then fL = a (first L fire at step a). But sorry 1 requires
fL > a. Contradiction.

If moverAt(a) = rt: then fR = a. But sorry 1 requires fR > a. Contradiction!

WAIT: Sorry 1 has BOTH fL > a AND fR > a. But moverAt(a) ∈ {lt, rt}.
If moverAt(a) = lt, then fL = a, not fL > a.
If moverAt(a) = rt, then fR = a, not fR > a.

This means the sorry 1 case (line 1012) requires fL > a AND fR > a, but the
first mover in the phase must be lt or rt. If it's lt, fL = a (since it's the
first L fire). If it's rt, fR = a. Either way, one of fL, fR equals a.

So fL > a AND fR > a is IMPOSSIBLE! The sorry at line 1012 is vacuously true!

Let me verify this by checking the Lean code structure more carefully.
"""

def check_sorry1_vacuous():
    """
    Sorry 1 (line 1012) context:
    - hfL_gt: phase.a.val < fL.val (i.e., fL > a)
    - hfR_gt: phase.a.val < fR.val (i.e., fR > a)
    - But these are under by_cases branches.

    Wait, let me re-read. Line 971: by_cases hfL_gt : phase.a.val < fL.val
    Line 989: by_cases hfR_gt : phase.a.val < fR.val

    The sorry at 1012 is inside hfL_gt (fL > a) AND hfR_gt (fR > a).

    But moverAt(a) is the first mover of the phase. It's adjacent to t
    (because moverAt(a-1) = t and all-adjacent). So moverAt(a) ∈ {lt, rt}.

    If moverAt(a) = lt: fL = a (since fL is the first L-fire in the phase,
    and L fires at step a). Then fL = a, contradicting hfL_gt.

    If moverAt(a) = rt: fR = a, contradicting hfR_gt.

    So the branch hfL_gt ∧ hfR_gt is UNREACHABLE. The sorry is vacuous!
    """
    print("=== Analysis of Sorry 1 (line 1012) ===")
    print("Context: hfL_gt (fL > a) AND hfR_gt (fR > a)")
    print()
    print("The first mover in the phase (step a) must be adjacent to t")
    print("(because moverAt(a-1) = t and gap1_ec forces adjacency under ¬EC).")
    print("So moverAt(a) ∈ {lt, rt}.")
    print()
    print("If moverAt(a) = lt: Then lt fires at step a, so fL = a. Contradicts fL > a.")
    print("If moverAt(a) = rt: Then rt fires at step a, so fR = a. Contradicts fR > a.")
    print()
    print("CONCLUSION: The conjunction fL > a ∧ fR > a is IMPOSSIBLE under ¬EC.")
    print("The sorry at line 1012 is VACUOUSLY TRUE.")
    print()
    print("BUT WAIT: Is moverAt(a) necessarily lt or rt?")
    print("moverAt(a-1) = t. Under ¬EC, gap1_ec says moverAt(a) must be")
    print("ring-adjacent to moverAt(a-1) = t. Ring-adj to t = {lt, rt}.")
    print("(Note: self-adjacency t is excluded since t fires at a-1, not at a.)")
    print()
    print("Actually: gap1_ec says moverAt(a) ∈ {left(moverAt(a-1)), moverAt(a-1),")
    print("right(moverAt(a-1))} = {lt, t, rt}. But moverAt(a) ≠ t (phase condition:")
    print("t doesn't fire in [a, s)). So moverAt(a) ∈ {lt, rt}.")
    print()
    print("This confirms: fL > a ∧ fR > a is impossible. Sorry 1 is vacuous.")


def check_sorry2_3():
    """
    Sorry 2 (line 1077): fR = a (i.e., moverAt(a) = rt), fL > a.
    left³(t) fires in [a, fLL). The chain goes:
      R (at a), ..., left³(t), LL, ..., L, T.

    Sorry 3 (line 1121): fL = a (i.e., moverAt(a) = lt), fR > a.
    right³(t) fires in [a, fRR). The chain goes:
      L (at a), ..., right³(t), RR, ..., R, T.

    These are the real sorry cases. The first mover is one of lt/rt,
    and the backward chain on the OTHER side extends to the 3rd neighbor.

    For sorry 2: starts at R(=rt), and the L-fire side has the chain
    LL fires before L, and left³(t) fires before LL. This is the walk from
    R around the ring toward L: R -> RR -> ... -> left³(t) -> LL -> L.

    Actually wait. Let me re-read sorry 2 more carefully.
    """
    print("=== Analysis of Sorry 2 (line 1077) ===")
    print("Context: fL = a (moverAt(a) = lt), fR > a.")
    print("ec_caseC_RL used between fR and fL? No, fR > fL = a -> ec_caseC_RL")
    print("needs no LL in [fR, fL), but fR > fL, so interval wraps. Complex.")
    print()
    print("The code tries ec_caseC_RL between fR and fL with no LL in between.")
    print("If LL fires in [fR, fL): finds first LL, checks if left³(t) fires before it.")
    print("If yes: sorry (adjacent chain continues).")
    print()
    print("WAIT: I need to re-read the code. fL = a, so the code enters the")
    print("else branch at line 1078. Let me look at the actual structure.")
    print()

    print("=== Analysis of Sorry 3 (line 1121) ===")
    print("Symmetric to sorry 2.")
    print()

    print("=== Key question: Is the backward chain finite? ===")
    print("The chain extends: left³t, LL, L (from the right side)")
    print("or: right³t, RR, R (from the left side).")
    print()
    print("Under ¬EC + gap1_ec, every consecutive pair in the chain is adjacent.")
    print("The chain follows ring positions: e.g., left³t = (t-3)%n, LL = (t-2)%n,")
    print("L = (t-1)%n, t. Each step is +1 on the ring. So the chain walks CW.")
    print()
    print("The chain can be extended backward: before left³t fires, what fires?")
    print("It must be ring-adj to left³t: either left⁴t or left²t = LL.")
    print("But LL hasn't fired yet at that point (we're before first LL).")
    print("So it's left⁴t. And before that: left⁵t. Etc.")
    print()
    print("This chain can wrap ALL the way around the ring. For n=9, t=1:")
    print("  Chain: ..., 4, 5, 6, 7, 8(=LL), 0(=L), 1(=T)")
    print("  Starting from R=2: 2, 3, 4, 5, 6, 7, 8, 0, 1")
    print("  This is the entire ring!")
    print()
    print("So the chain IS finite (it stops at the start of the phase, which is R),")
    print("but gap1_ec never fires because every step is adjacent.")
    print()
    print("HOWEVER: the chain starting from R walks CW all the way to L.")
    print("The starting mover is R (step a). Before step a is step a-1 with mover t.")
    print("moverAt(a-1) = t, moverAt(a) = R. These are adjacent. Fine.")
    print()
    print("But the chain within the phase goes:")
    print("  R, [some processors], ..., left³t, LL, L")
    print("  Then t fires.")
    print()
    print("The question: among the processors between R and left³t on the ring,")
    print("which ones fire? We know RR fires (since fR > a means R fires after a,")
    print("wait no, fR is first R fire, fR > a means... hmm.")
    print()
    print("Wait, fL = a means moverAt(a) = lt = L. So the phase starts with L firing.")
    print("fR > a means R hasn't fired yet at step a. R fires later at fR.")
    print("Before R fires, the chain of movers from L(=step a) to R(=step fR) must be")
    print("adjacent. The ring walk from L to R (going CW through t) is: L, T, R.")
    print("But T doesn't fire in the phase. So the walk must go CCW: L, LL, ..., RR, R.")
    print("That's n-2 steps around the ring!")


check_sorry1_vacuous()
print()
check_sorry2_3()
