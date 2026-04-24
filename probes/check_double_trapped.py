#!/usr/bin/env python3
"""
Analyze the double_trapped sorry case.

Setup: ring of n processors, 3 consecutive binary {i, ri, rri}.
Both i and ri are "trapped": cwMoveCountAt = ccwMoveCountAt = 0.
Derived: left(i) has cw=0, ccw>0. rri has cw>0, ccw=0.

The mover never visits i or ri. It's confined to the arc
[rri, right(rri), ..., left(left(i)), left(i)] of n-2 processors.

Question: can hno_safe (no safe processor) hold in this configuration?
A processor q is safe if the mover never visits q, left(q), or right(q).

With i and ri never being movers, and left(i)/rri being movers:
- For q = i: mover visits left(i) ∈ {i, left(i), ri}. NOT safe.
- For q = ri: mover visits rri ∈ {ri, i, rri}. NOT safe.

For q on the arc far from boundaries: q's 3-neighborhood {q, left(q), right(q)}
must intersect the set of movers. The mover is confined to the arc.
If the arc has n-2 processors and the mover visits a dominating set, all q are covered.

KEY INSIGHT: if the mover visits ONLY {left(i), rri} (the two boundary procs),
then any processor q with left(q), q, right(q) ∩ {left(i), rri} = ∅ would be safe.

For n ≥ 9: the arc has ≥ 7 processors. The two boundary procs are left(i) and rri.
The middle of the arc is distance ≥ 3 from both boundaries. So middle procs q
satisfy {q, left(q), right(q)} ∩ {left(i), rri} = ∅, making them safe.

BUT: hno_safe says NO safe processor exists. So if only boundary procs fire,
we get a safe processor → contradiction with hno_safe → False!

WAIT: the mover CAN visit interior arc processors too. We need to show that
even with interior movers, hno_safe forces a contradiction.

Actually: hno_safe is a HYPOTHESIS (not something we need to prove). We need
to DERIVE False from it. Let me think about what False means here...

The theorem says: these hypotheses are CONTRADICTORY. We need to show they
can't all hold simultaneously.

Let me check: CAN the mover be confined to n-2 processors while satisfying
hno_safe (every processor has a nearby mover)?

For hno_safe: every processor q has moverAt(k) ∈ {q, left(q), right(q)} for SOME k.
For i: moverAt = left(i) works (left(i) ∈ {i, left(i), right(i)}?
  left(i) = left(i). Is left(i) ∈ {i, left(i), right(i)}? Yes! left(i) = left(i). ✓
For ri: moverAt = rri works. rri = right(ri) ∈ {ri, left(ri), right(ri)}.
  right(ri) = right(ri). ✓

So i and ri are covered by left(i) and rri respectively. No contradiction from i,ri.

For other processors on the ring NOT on the arc (none — all procs are either i, ri, or on the arc):
Wait, the ring has n processors. The arc has n-2. So i and ri are the only non-arc procs. ✓

For arc processors: they need a nearby mover. If the mover visits enough arc procs,
all neighborhoods are covered.

So the hypotheses CAN be consistent? Then why does the theorem claim False?

Let me reconsider. What ELSE is in the hypotheses?
- hzero: zero winding (total displacement = 0)
- hcw_pos: cwStepCount > 0 (there exist CW steps)

With the mover confined to n-2 processors (arc) and zero winding:
- Each edge on the arc has CW crossings = CCW crossings
- The boundary condition: left(i) fires CCW only, rri fires CW only

Zero winding at edge (left(left(i)), left(i)):
  cw(left(left(i))) = ccw(left(i)) > 0.
So left(left(i)) fires CW.

Zero winding at edge (rri, right(rri)):
  cw(rri) = ccw(right(rri)).
  cw(rri) > 0, so ccw(right(rri)) > 0.
So right(rri) fires CCW.

Continuing propagation along the arc:
- Each edge: cw = ccw.
- Starting from rri end: cw(rri) > 0, ccw(right(rri)) > 0.
- At edge (right(rri), right²(rri)): cw(right(rri)) = ccw(right²(rri)).
  We need to know cw(right(rri)). The total firings of right(rri) = cw + ccw ≥ ccw > 0.

Let me trace through numerically for n=9, i=0:
Arc: [2, 3, 4, 5, 6, 7, 8] (= [rri, ..., left(i)] since left(0)=8, rri=right(right(0))=2)

Zero winding derived facts:
- cw(8) = 0  (left(i) = 8, cw = 0)
- ccw(0) = 0, cw(0) = 0  (i = 0 trapped)
- ccw(1) = 0, cw(1) = 0  (ri = 1 trapped)
- ccw(2) = 0  (rri = 2, ccw = 0)
- cw(2) > 0  (given)
- ccw(8) > 0  (given)

From zero winding at edges:
Edge (8, 0): cw(8) - ccw(0) = 0. cw(8)=0, ccw(0)=0. ✓
Edge (0, 1): cw(0) - ccw(1) = 0. ✓
Edge (1, 2): cw(1) - ccw(2) = 0. cw(1)=0, ccw(2)=0. ✓
Edge (7, 8): cw(7) - ccw(8) = 0. cw(7) = ccw(8) > 0.
Edge (2, 3): cw(2) - ccw(3) = 0. ccw(3) = cw(2) > 0.
Edge (3, 4): cw(3) - ccw(4) = 0. ccw(4) = cw(3).
Edge (4, 5): cw(4) - ccw(5) = 0. ccw(5) = cw(4).
Edge (5, 6): cw(5) - ccw(6) = 0. ccw(6) = cw(5).
Edge (6, 7): cw(6) - ccw(7) = 0. ccw(7) = cw(6).

So: cw(7) = ccw(8) > 0, cw(6) = ccw(7), cw(5) = ccw(6), ..., cw(3) = ccw(4), ccw(3) = cw(2) > 0.

From cw(2) > 0: ccw(3) = cw(2) > 0.
From cw(3) = ccw(4): need to know cw(3).
From cw(7) = ccw(8) > 0: cw(7) > 0.
From cw(6) = ccw(7): need to know cw(6).

The total fire count of each arc processor = cw + ccw + stay ≥ 0.
But we need fireCount_ne_one: fire count ≠ 1 for each processor.

For proc 3: ccw(3) > 0. If cw(3) = 0: total directional crossings at 3 = ccw(3).
But that's only CCW crossings at 3. The FIRE COUNT includes all firings of 3
(CW + CCW + stay). With ccw(3) > 0: proc 3 fires ≥ 1 times. fireCount ≠ 1
means fireCount ≥ 2 or fireCount = 0. So proc 3 fires ≥ 2 times (or 0,
but ccw(3) > 0 means it fires at least once).

fireCount_ne_one + fires ≥ 1 → fires ≥ 2. But fireCount_ne_one says
fireCount ≠ 1, and fireCount = ccw(3) + cw(3) + stay(3) ≥ ccw(3) ≥ 1.
So fireCount ≥ 2.

Hmm, this is getting complicated. Let me think about it differently.

TOTAL CW steps = cwStepCount = sum of all cw(p) over all p.
TOTAL CCW steps = ccwStepCount.
Zero winding: cwStepCount = ccwStepCount.
hcw_pos: cwStepCount > 0.
configs.length = cwStepCount + ccwStepCount + stayStepCount.

On the arc: cw(2) > 0 and cw(7) > 0 (from propagation).
All CW comes from arc processors (i and ri don't fire).

Hmm, I keep going in circles. Let me think about the SIMPLEST possible
contradiction.

SIMPLEST ARGUMENT:
With i and ri having fireCount = 0 (never fire), there are only n-2 processors
that fire. The cycle length = sum of fire counts over all procs = sum over arc.
Each arc proc fires ≥ 0 times.

With fireCount_ne_one: each proc fires 0 or ≥2 times.
If proc i fires 0 times: it never fires. Consistent with trapped.
If proc i fires ≥ 2 times: it fires at least twice.

For the 3 consecutive binary {i, ri, rri}: i and ri fire 0 times.
rri fires ≥ 1 times (cw(rri) > 0). fireCount(rri) ≥ 1. From fireCount_ne_one:
fireCount(rri) ≥ 2.

Now: i has fire count 0. Its NEIGHBORS are left(i) and ri. ri also has fire
count 0. So the two consecutive processors i, ri both have fire count 0.

What about right(i) = ri? Already covered.
What about left(i)? ccw(left(i)) > 0, so fireCount(left(i)) ≥ 1. From
fireCount_ne_one: fireCount(left(i)) ≥ 2.

Now, consider processor ri. It has fire count 0. Its 3-neighborhood is
{ri, i, rri}. i has fc=0, ri has fc=0, rri has fc≥2.
From hno_safe: some mover visits {ri, i, rri}. That mover is rri (since i, ri
don't fire). ✓.

Wait, I think I need to look at this problem from a COMPLETELY different angle.

The key question: do these hypotheses actually LEAD to False? Or is the sorry
wrong (the theorem statement is false)?

Let me try to construct a CONCRETE example where all hypotheses hold:
- n = 9
- 3 consecutive binary at {0, 1, 2}
- A good cycle where 0 and 1 are trapped (fc=0)
- Zero winding
- CW steps > 0
- No safe processor

Can such a cycle exist?
"""

def main():
    n = 9
    # Binary at 0, 1, 2. Ternary at 3..8.
    # i=0, ri=1, rri=2
    # Trapped: 0 and 1 never fire. Mover confined to {2,3,4,5,6,7,8}.

    # For a valid good cycle:
    # - Each config has exactly 1 privileged processor
    # - All configs distinct
    # - Cycle is closed
    # - Zero winding (equal CW and CCW)
    # - CW > 0
    # - No safe processor (every proc has a nearby mover)

    # With 0 and 1 never firing: their values are CONSTANT.
    # Say val(0) = v0, val(1) = v1 throughout the cycle.
    # All configs have 0=v0 and 1=v1.

    # For 0 to not be privileged at any config:
    # f(0, L, v0, R) = v0 for all (L, R) that appear.
    # L = val(8) at that config, R = val(1) = v1.

    # Similarly for 1: f(1, L, v1, R) = v1 for all (L, R).
    # L = val(0) = v0, R = val(2) at that config.

    # For hno_safe: every proc q has moverAt(k) ∈ {q, left(q), right(q)} for some k.
    # For q=0: left(0)=8, right(0)=1. Need moverAt ∈ {0, 8, 1}.
    #   0 never fires, 1 never fires. So need 8 to fire. ✓ if fc(8) > 0.
    # For q=1: need moverAt ∈ {1, 0, 2}. 0,1 never fire. So need 2 to fire. ✓ if fc(2) > 0.
    # For q=3: need moverAt ∈ {3, 2, 4}.
    # For q=4: need moverAt ∈ {4, 3, 5}.
    # For q=5: need moverAt ∈ {5, 4, 6}.
    # For q=6: need moverAt ∈ {6, 5, 7}.
    # For q=7: need moverAt ∈ {7, 6, 8}.
    # For q=8: need moverAt ∈ {8, 7, 0}. 0 never fires. So need 8 or 7 to fire.

    # The mover must visit within dist 1 of every arc processor.
    # Arc = {2, 3, 4, 5, 6, 7, 8}.
    # For q=3: need mover in {2,3,4}.
    # For q=4: need mover in {3,4,5}.
    # For q=5: need mover in {4,5,6}.
    # For q=6: need mover in {5,6,7}.
    # For q=7: need mover in {6,7,8}.
    # So the mover must visit at least {2 or 3 or 4}, {3 or 4 or 5}, ..., {6 or 7 or 8}.
    # A minimal dominating set: {3, 6} covers {2,3,4} and {5,6,7} and partially {6,7,8}.
    # But q=8 needs {7,8,0}. 0 doesn't fire. So need 7 or 8.
    # With {3, 6, 8}: covers all.

    # So mover needs to visit at least 3 procs: e.g., 3, 6, 8 (or 2, 5, 8, etc.)

    # CAN such a cycle exist? The mover goes: 2 (CW), 3, 4, ..., 8, 8 (CCW), 7, 6, ..., 2
    # This is a sweep of the arc. Zero winding.

    # Fire counts: each arc proc fires twice (once CW, once CCW).
    # Except endpoints: 2 fires CW (from trapped region) and CCW (from sweep return).
    #                   8 fires CCW (from trapped region) and CW (from sweep approach).

    # Total CW = 7 (2→3, 3→4, ..., 8→? no, 7→8 is CW).
    # Actually: CW sweep 2→3→4→5→6→7→8 = 6 CW steps.
    # CCW sweep 8→7→6→5→4→3→2 = 6 CCW steps.
    # Plus: the boundary behavior.

    # Hmm, the mover sequence would be something like:
    # [2, 3, 4, 5, 6, 7, 8, 7, 6, 5, 4, 3, 2, ...]
    # This has displacement: +1+1+1+1+1+1-1-1-1-1-1-1 = 0. Zero winding ✓
    # CW steps: 6. CCW steps: 6. Total: 12 steps.
    # Fire counts: 2 fires twice, 3 fires twice, ..., 7 fires twice, 8 fires twice.
    # That's 7 procs × 2 = 14... but we only have 12 steps?
    # Let me recount: [2, 3, 4, 5, 6, 7, 8, 7, 6, 5, 4, 3]
    # 12 movers. Fire counts: 2→1, 3→2, 4→2, 5→2, 6→2, 7→2, 8→1.
    # Wait, 2 fires once (first step), 3 fires twice (2nd and 12th), etc.

    # Actually: mover sequence [2, 3, 4, 5, 6, 7, 8, 7, 6, 5, 4, 3]
    # Step 0: mover=2
    # Step 1: mover=3
    # Step 2: mover=4
    # Step 3: mover=5
    # Step 4: mover=6
    # Step 5: mover=7
    # Step 6: mover=8
    # Step 7: mover=7
    # Step 8: mover=6
    # Step 9: mover=5
    # Step 10: mover=4
    # Step 11: mover=3
    # (wrap to step 0: mover=2)

    # Fire counts: 2→1, 3→2, 4→2, 5→2, 6→2, 7→2, 8→1
    # But fireCount_ne_one says fc ≠ 1. So procs 2 and 8 have fc=1 → CONTRADICTION!

    # So this simple sweep doesn't work because boundary procs fire only once.

    # To get fc ≥ 2 for all: need the sweep to go back and forth TWICE.
    # [2,3,4,5,6,7,8,7,6,5,4,3,2,3,4,5,6,7,8,7,6,5,4,3]
    # 24 steps. fc: 2→2, 3→4, 4→4, 5→4, 6→4, 7→4, 8→2
    # CW: 12, CCW: 12. Zero winding ✓.
    # All fc ≥ 2 ✓.

    # hno_safe: every proc has nearby mover. The arc procs all fire. ✓
    # For q=0: mover 8 is neighbor (right(0)=1... wait, left(0)=8).
    #   Actually {0, left(0), right(0)} = {0, 8, 1}. Mover visits 8. ✓
    # For q=1: {1, 0, 2}. Mover visits 2. ✓

    # So the cycle EXISTS? Then the hypotheses are CONSISTENT and the theorem
    # statement is FALSE??

    # Wait, I need to check if this is actually a GOOD CYCLE.
    # A good cycle needs: each config has EXACTLY ONE privileged processor.
    # With procs 0, 1 having constant values and never being privileged:
    # at each step, exactly one of {2,...,8} is privileged.

    # For this to work, the transition functions must be set up correctly.
    # The mover sequence [2,3,...,8,7,...,3,2,3,...,8,7,...,3] determines
    # which proc is privileged at each step. We need NO other proc to be
    # privileged at any step.

    # For proc 0 at any step: f(0, val(8), v0, val(1)) = v0 (not privileged).
    # val(1) = v1 is constant. val(8) changes as proc 8 fires.
    # So f(0, L, v0, v1) = v0 for all L values that appear. This constrains f.

    # For proc 1: f(1, v0, v1, val(2)) = v1 for all val(2) that appear.

    # These are satisfiable constraints on the transition function. So yes,
    # such a system CAN exist.

    # BUT: does it CONVERGE? The theorem takes hypotheses that DON'T include
    # convergence! So if the cycle exists (consistent hypotheses), the theorem
    # is asserting False from consistent hypotheses → the theorem is WRONG.

    # Wait wait wait. Let me re-read the theorem signature.

    # double_trapped_baf_false takes:
    # (hn : sys.rs.n ≥ 9) (gc : GoodCycle sys)
    # (hzero : gc.zeroWinding) (hcw_pos : 0 < gc.cwStepCount)
    # (hno_safe : ¬∃ q, ...) (i : Fin sys.rs.n)
    # (hbin_i, hbin_ri, hbin_rri)
    # (hcw_i = 0, hccw_i = 0, hcw_ri = 0, hccw_ri = 0)

    # It does NOT take _hconv or _hsub!

    # If the hypotheses are consistent (a cycle satisfying all of them exists),
    # then the theorem is FALSE. You can't derive False from consistent premises.

    print("CRITICAL FINDING: double_trapped_baf_false may have WRONG hypotheses!")
    print("The theorem doesn't take 'converges' or 'subThreshold'.")
    print("A zero-winding back-and-forth cycle on the arc [rri,...,left(i)]")
    print("can satisfy all given hypotheses.")
    print()
    print("The theorem is called from consecutiveBinary_baf_false which HAS")
    print("_hconv and _hsub, but these are NOT passed to double_trapped_baf_false.")
    print()
    print("FIX: Add _hconv and/or _hsub as parameters, then use convergence")
    print("or sub-threshold to derive the actual contradiction.")

if __name__ == "__main__":
    main()
