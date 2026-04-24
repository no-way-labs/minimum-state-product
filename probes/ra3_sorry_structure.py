#!/usr/bin/env python3
"""
Analyze the structural constraints of the sorry pattern.

Sorry-L at n=9, t=1: mover sequence in phase is
  R(2), RR(3), 4, 5, 6, 7, LL(8), L(0)
Then t=1 fires.

Key observations:
1. EVERY processor fires exactly once in this phase (0,2,3,4,5,6,7,8 + t=1)
2. The cycle consists of multiple such phases (one per t-fire)
3. For binary processors (m=2), firing once flips them. Over the full cycle,
   they must return to initial value, so they fire an EVEN number of times.
4. In the sorry phase, L(0) fires once, R(2) fires once. Both binary.
   So in other phases, they must fire an ODD number of additional times.

Let me check: at n=5, what does the sorry pattern look like?
n=5, ms=[2,3,2,3,3], t=1, lt=0, rt=2, llt=4, rrt=3.
Sorry-L: R(2), RR(3), llt(4)=4, L(0) -> then T(1).
Wait: walk from R=2 to LL=4: 2->3->4->0. Movers: R, RR, 4, L, T.
Check: mover before first L fire (at step 3) is mover at step 2 = 4 = llt. ✓

Actually let me reconsider: is the sorry pattern possible when both sides
are sorry simultaneously? The problem statement says:
  "left²(t) fires at step fL-1"
  "right²(t) fires at step fR-1"
  (BOTH conditions)

Let me re-read: "It gets STUCK (sorry) when:
- left²(t) fires at step fL-1 (immediately before the first left(t) fire at fL)
- right²(t) fires at step fR-1 (immediately before the first right(t) fire at fR)"

So it's BOTH conditions simultaneously. This requires the walk to go BOTH
directions from t, reaching llt AND rrt before first lt/rt fire.

For n=9,t=1: We need to reach llt=8 before first lt=0 fire, AND
reach rrt=3 before first rt=2 fire. But the walk starts at lt or rt
(adjacent to t).

Wait - both conditions can hold if the walk goes BOTH directions from t.
E.g.: start at R(2), walk CW: 2->3->4->5->6->7->8->0 (that's one arc),
then from L(0), continue to... but we already hit L.

Actually, if the walk is:
  Start at R(2), go: 2,3,4,5,6,7,8,0 (all CW around ring).
  rrt=3 fires at step 1, before first R fire? No, R already fired at step 0.

Hmm, let me reconsider. In a mixed phase:
- J >= 1 fires of lt, K >= 1 fires of rt
- fL = first lt fire in the phase
- fR = first rt fire in the phase

Both sides sorry: mover at fL-1 = llt AND mover at fR-1 = rrt.

If the phase starts at rt=2 (step 0), then fR = 0 (first rt fire at step 0).
We need mover at fR-1 = rrt=3. But fR-1 = -1 is outside the phase.

If the phase starts at something other than lt or rt... but we proved
the start must be lt or rt (adjacent to t).

So one side is immediate (first fire at step 0). The other side needs the walk.

Unless: the phase starts at rt, and rt fires again later. Then first_rt = 0,
and fR-1 = -1 outside phase. This doesn't match sorry-R.

Wait, unless rt fires more than once. If R fires at steps 0, 5, 8 (say),
then first_rt = 0, fR-1 = step -1 (outside). Can't have sorry-R.

So BOTH-SIDES sorry requires:
  - Neither lt nor rt fires first in the phase.
  - But the first mover must be adjacent to t = {lt, rt}.
  Contradiction!

CONCLUSION: Both-sides sorry is IMPOSSIBLE. The sorry is always one-sided.

Let me verify by reading the Lean source or checking what the sorry actually needs.
"""

def check_both_sides_sorry():
    """
    Show that both-sides sorry is structurally impossible:
    In a mixed phase, the first mover is lt or rt (adjacent to t).
    If first mover = lt, then fL = 0, fL-1 outside phase (not llt). Can't be sorry-L.
    If first mover = rt, then fR = 0, fR-1 outside phase (not rrt). Can't be sorry-R.

    So at most one side can be sorry.
    """
    for n in [5, 7, 9, 11]:
        for t in range(n):
            lt = (t - 1) % n
            rt = (t + 1) % n
            llt = (t - 2) % n
            rrt = (t + 2) % n

            # Phase first mover must be in {lt, rt}
            # If first = lt: fL = 0, need fL-1 = llt. But step -1 is outside phase.
            #   fL-1 is actually the t-fire at (a-1), mover = t ≠ llt (unless t = llt).
            #   t = llt means t = (t-2)%n, so 2 = 0 mod n, so n = 2. But n >= 5.
            # If first = rt: fR = 0, same argument.

            # So both-sides sorry needs first mover ∉ {lt, rt}.
            # But first mover must be adj to t, and adj = {lt, rt} (for n >= 5, t ≠ llt, t ≠ rrt).
            pass

    print("Both-sides sorry is impossible for n >= 5:")
    print("  Phase first mover must be adjacent to t, i.e., lt or rt.")
    print("  If first mover = lt, then fL = 0, fL-1 is outside the phase (previous t-fire).")
    print("  So sorry-L requires fL > 0, meaning lt doesn't fire first: first mover = rt.")
    print("  Similarly sorry-R requires first mover = lt.")
    print("  Both simultaneously requires first mover = lt AND first mover = rt. Contradiction.")
    print()
    print("  => The sorry is always one-sided.")
    print("  => Sorry-L: first mover = rt, walk CW around ring to llt, then lt fires.")
    print("  => Sorry-R: first mover = lt, walk CCW around ring to rrt, then rt fires.")
    print()

    # Now: what does the Lean proof need? It needs to close the sorry for ONE side.
    # The sorry-L case has mover sequence: R, ..., LL, L, ..., T
    # The sorry-R case has mover sequence: L, ..., RR, R, ..., T
    # These are symmetric, so we only need to handle one.

    # Key question: does the walk-around-the-ring phase force an EC
    # somewhere in the FULL cycle?

    # The walk hits n-1 processors in the phase. Each fires at least once.
    # Binary procs (lt, rt) fire odd times in this phase (1, 3, 5...).
    # In the full cycle, they must fire even times total.
    # So in other phases, they fire odd times too.

    # For the sorry-L phase (start at R, walk CW):
    # R fires at step 0 (and possibly more). At step 0, R changes.
    # Then walk: RR, 4, 5, 6, 7, LL, L.
    # L fires at step n-2 (second to last).
    # T fires at step n-1 (last).

    # In this phase, processor t doesn't fire until the very end.
    # t's value is constant until step n-1.
    # t's LEFT neighbor (lt=L) fires at step n-2 -> t's left context changes.
    # t's RIGHT neighbor (rt=R) fires at step 0 -> t's right context changes.

    # At step n-1 (t fires): boundary = (L_val', t_val, R_val').
    # We need this NOT to match any non-mover step boundary.
    # But t doesn't fire in steps 0..n-2, so all those are non-mover steps for t.

    # t_val is constant. L_val changes at step n-2 (L fires). R_val changes at step 0 (R fires).
    # So:
    #   Steps 0: L_val = L0, R_val = R0 (before R fires)
    #   Step 0 fires R: now R_val -> R1
    #   Steps 1..n-3: L_val = L0, R_val = R1 (nothing changes L or R of t)
    #   Step n-2 fires L: L_val -> L1
    #   Step n-1 fires t: boundary = (L1, t_val, R1)

    # Non-mover triples at t:
    #   Step 0: (L0, t_val, R0)
    #   Steps 1..n-3: (L0, t_val, R1)  -- all the same!
    #   Step n-2: (L0, t_val, R1)... wait, L fires at step n-2.
    #     Config at step n-2 has L=L0 (before L fires), so boundary at t = (L0, t_val, R1).
    #     After L fires, config at step n-1 has L=L1.

    # Mover triple at t (step n-1): (L1, t_val, R1)
    # Non-mover triples: {(L0, t_val, R0), (L0, t_val, R1)}

    # For EC at t: (L1, t_val, R1) must equal one of these.
    #   Case 1: L1=L0 and R1=R0 -> both binary procs unchanged. But they fired! Contradiction.
    #     (Since L is binary, firing changes its value: L1 ≠ L0.)
    #   Case 2: L1=L0 and R1=R1 -> L1=L0. But L fired: L1 ≠ L0 (binary flip). Contradiction.

    # WAIT: L1 ≠ L0 because L is binary and fired once (odd flips = different value).
    # And R1 ≠ R0 because R is binary and fired once.

    # So (L1, t_val, R1) ≠ (L0, t_val, R0) and ≠ (L0, t_val, R1).
    # EC at t DOES NOT HOLD within this phase.

    # BUT: the EC could come from OTHER phases in the cycle!
    # In another phase, t might fire, and at that step the boundary at t
    # includes (L_val'', t_val'', R_val''). Some non-mover step in that phase
    # could match.

    # The question is really about the GLOBAL cycle, not just this phase.

    print("Within the sorry phase itself, EC at t is impossible:")
    print("  L and R each fire once (binary flip), so their values at the end")
    print("  differ from all intermediate non-mover triples at t.")
    print()
    print("The sorry is about what happens when trying to prove EC using")
    print("mk_ec_left or mk_ec_right: these need a gap of steps with no")
    print("llt/lt/t fires between some non-mover step and fL.")
    print("When llt fires immediately before fL, there is no such gap.")


def analyze_what_sorry_blocks():
    """
    The sorry blocks mk_ec_left, which works as follows:

    mk_ec_left(v, fL): Given step v (non-mover for lt) and fL (lt fires),
    with no llt, lt, or t fires in (v, fL) open interval:
    => EC at lt between steps v and fL.

    Why: At step v, lt doesn't fire, boundary at lt = (llt_val, lt_val, t_val).
    At step fL, lt fires, boundary = same (llt_val, lt_val, t_val) because
    nothing in (v,fL) changes llt, lt, or t's value.

    When llt fires at fL-1: llt_val changes between v and fL. The gap has
    a llt fire in it. So mk_ec_left doesn't apply.

    But can we use the llt fire to get an EC at llt instead?
    At step fL-1, llt fires. Boundary at llt = (lllt_val, llt_val, lt_val).
    Is there a non-mover step for llt with the same boundary?

    If we look at step fL-2 (must be lllt by adjacency), then at step fL-2,
    lllt fires, and llt is non-mover. Boundary at llt at step fL-2 =
    (lllt_val_old, llt_val, lt_val). At step fL-1 (llt fires):
    boundary = (lllt_val_new, llt_val, lt_val).
    Since lllt fired at fL-2: lllt_val_old ≠ lllt_val_new (if binary).

    So EC at llt between fL-2 and fL-1 also fails (if lllt is binary).

    This cascades: the backward scan extends to lllt, llllt, ... all the way
    around the ring. That's the sorry case.
    """
    print("=== What the sorry blocks ===")
    print("mk_ec_left needs a gap with no llt/lt/t fires between v and fL.")
    print("When llt fires at fL-1, the gap is zero.")
    print("Backward scan extends: each step changes the second-neighbor,")
    print("preventing the EC construction.")
    print()
    print("The same argument applies at each position along the backward chain:")
    print("  llt fired at fL-1, preceded by lllt at fL-2, etc.")
    print("  At each position p, the fire at p is preceded by a fire at p-1,")
    print("  which changes p's left context, blocking mk_ec at p.")
    print()
    print("So mk_ec_left/right can't close it. We need a DIFFERENT construction.")
    print()
    print("Candidate: use the CYCLE CLOSURE constraint.")
    print("The walk-around-ring phase uses n-1 of the n processors.")
    print("Over the full cycle, each binary proc fires even times.")
    print("In the sorry phase, each binary proc fires odd times.")
    print("So in other phases, each binary fires odd times too.")
    print("This severely constrains the cycle structure.")


def count_phase_fire_parity():
    """
    In the sorry-L phase: R, RR, 4, 5, 6, 7, LL, L, T
    Each processor fires exactly once. Binary procs L(0) and R(2) fire once (odd).

    For cycle closure, they must fire even times total.
    So other phases contribute odd fires for L and R.

    If t fires mt times total, there are mt phases.
    Each phase has its own structure.

    For the sorry phase to exist, we need a specific full-ring walk.
    The walk uses n-1 steps before the t-fire.
    Minimum cycle length would be quite large.
    """
    print("=== Fire parity constraints ===")
    n = 9
    ms = [2, 3, 2, 3, 2, 3, 3, 3, 3]
    t = 1

    print(f"In sorry-L phase (len {n}): each of {n-1} non-t procs fires exactly once.")
    print(f"Binary procs (0, 2, 4): each fires once (odd).")
    print(f"For cycle closure, need even total fires for binary procs.")
    print(f"So OTHER phases must contribute odd fires for each binary proc.")
    print()

    # If t fires mt=3 times, there are 3 phases.
    # Each binary proc needs to fire total even times.
    # Sorry phase contributes 1 fire each.
    # Other 2 phases together contribute odd fires for each binary.
    # With 3 binary procs, that's 3 independent parity constraints.

    print("If t fires mt=3 times (minimum for ternary):")
    print("  3 phases total. Sorry phase: each binary fires 1 time.")
    print("  Other 2 phases: each binary fires total = odd (1, 3, 5, ...)")
    print("  With 3 binary procs and 2 other phases, lots of freedom.")
    print()

    # The real constraint is on what mover sequences are possible in the
    # other phases (all-adjacent) and whether they can avoid EC.

    # Key insight for closing sorry:
    # In the sorry phase, the walk goes R->RR->4->5->6->7->LL->L->T.
    # At step 0, R fires. Its boundary triple (T_val, R_val, RR_val) is the mover triple.
    # At some other step in the sorry phase, R doesn't fire. Does R's nonmover triple match?
    #
    # Actually wait -- I already showed this doesn't produce EC within the phase.
    # The EC must come from interaction between the sorry phase and other phases.

    # ALTERNATIVE APPROACH: Maybe the sorry case never actually occurs in valid
    # sub-threshold cycles. Let me check the Lean code to understand the exact context.

check_both_sides_sorry()
print()
analyze_what_sorry_blocks()
print()
count_phase_fire_parity()
