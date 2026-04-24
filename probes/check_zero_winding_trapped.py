#!/usr/bin/env python3
"""Check the trapped-chain propagation argument.

Question: Under zero winding + no safe processor + sub-threshold,
can we show cwStepCount > 0 leads to contradiction using ONLY
the trapped-chain argument?

The argument would be:
1. Zero winding => edgeNetFlow = 0 at all edges
2. cwMoveCountAt(p) = ccwMoveCountAt(right(p)) for all p
3. No safe processor => mover visits neighborhood of every proc
4. If cwMoveCountAt(p) = 0 AND ccwMoveCountAt(p) = 0, p is trapped
5. If mover visits trapped p => contradiction (trapped_contradicts_hno_safe)
6. So for every p visited by mover: cwMoveCountAt(p) > 0 OR ccwMoveCountAt(p) > 0

Question: Can we derive cwStepCount = 0 from these constraints?

Let's check at n=5..8 with sub-threshold systems:
For each valid system, check:
- Is the cycle zero-winding?
- If yes, does it have CW > 0?
- If yes, is there no safe processor?
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system, privileged_set, apply_move


def analyze_zero_winding_cycles():
    """Look for zero-winding cycles in known sub-threshold systems."""
    # Known sub-threshold witnesses for n=5..8 use ms with 3+1+rest pattern
    # Let's check M_5 = 96 witness: ms = (2,2,2,3,4)
    # We need transition functions. Use the verifier to search.

    print("Checking if any sub-threshold witness has zero-winding cycle...")
    print()

    # For n=5, M_5=96, ms=(2,2,2,3,4)
    # Let's try to find a valid system with this ms
    # Actually, from memory: clb_witness_8748.py and similar scripts build witnesses
    # Let me just check with a brute force approach for small n

    from cup2_theorem import build_system

    # CUP-2 is AT threshold (not sub-threshold), but let's check its structure
    for n in range(5, 10):
        ms, fs = build_system(n)
        result = verify_system(ms, fs)
        if not result['valid']:
            continue

        good_set = result['good_configs']

        # Extract cycle
        succ = {}
        for c in good_set:
            priv = privileged_set(c, fs, ms)
            if len(priv) == 1:
                s = apply_move(c, priv[0], fs, ms)
                succ[c] = (s, priv[0])

        start = next(iter(good_set))
        visited = {}
        node = start
        step = 0
        while node not in visited:
            visited[node] = step
            if node not in succ:
                break
            node = succ[node][0]
            step += 1

        cycle_start = visited[node]
        cycle = []
        cur = node
        while True:
            nxt, mover = succ[cur]
            cycle.append((cur, mover))
            cur = nxt
            if cur == node:
                break

        L = len(cycle)
        movers = [m for (c, m) in cycle]

        # Step directions
        cw = ccw = stay = 0
        for k in range(L):
            m_k = movers[k]
            m_next = movers[(k + 1) % L]
            if m_next == (m_k + 1) % n:
                cw += 1
            elif m_next == (m_k - 1) % n:
                ccw += 1
            else:
                stay += 1

        disp = cw - ccw

        # cwMoveCountAt and ccwMoveCountAt
        cw_move = [0] * n
        ccw_move = [0] * n
        stay_move = [0] * n
        for k in range(L):
            m_k = movers[k]
            m_next = movers[(k + 1) % L]
            if m_next == (m_k + 1) % n:
                cw_move[m_k] += 1
            elif m_next == (m_k - 1) % n:
                ccw_move[m_k] += 1
            else:
                stay_move[m_k] += 1

        # fireCount
        fire = [0] * n
        for m in movers:
            fire[m] += 1

        # edgeNetFlow
        enf = [cw_move[p] - ccw_move[(p + 1) % n] for p in range(n)]

        # Safe processor check
        mover_set = set(movers)
        safe = None
        for q in range(n):
            is_safe = all(
                m != q and m != (q - 1) % n and m != (q + 1) % n
                for m in movers
            )
            if is_safe:
                safe = q
                break

        print(f"  n={n}: L={L}, disp={disp}, CW={cw}, CCW={ccw}, Stay={stay}")
        print(f"    cwMove:  {cw_move}")
        print(f"    ccwMove: {ccw_move}")
        print(f"    fire:    {fire}")
        print(f"    enf:     {enf}")
        print(f"    safe:    {safe}")
        print()


def check_trapped_chain_theory():
    """Verify the trapped chain propagation theory.

    Theorem: Under zero winding + no safe processor + n >= 9:
      cwStepCount > 0 leads to contradiction.

    Proof attempt:
    1. cwStepCount > 0 => some p has cwMoveCountAt(p) > 0
    2. edgeNetFlow = 0 => ccwMoveCountAt(right(p)) > 0
    3. Continue: ccwMoveCountAt(right(p)) > 0 =>
       cwMoveCountAt(left(right(p))) > 0 (edgeNetFlow at left(right(p)) = p)
       Wait: edgeNetFlow(p) = cwMoveCountAt(p) - ccwMoveCountAt(right(p)) = 0
       So ccwMoveCountAt(right(p)) = cwMoveCountAt(p) > 0. Good.
       But this doesn't tell us about cwMoveCountAt(right(p)).

    Actually, edgeNetFlow tells us: cwMoveCountAt(q) = ccwMoveCountAt(right(q))
    for all q. This links CW at q to CCW at right(q), but NOT CW at q to CW at right(q).

    The constraints are:
      cwMoveCountAt(q) = ccwMoveCountAt(right(q))  for all q (from edge flow = 0)
      fireCount(q) = cwMoveCountAt(q) + ccwMoveCountAt(q) + stayMoveCountAt(q)
      fireCount(q) != 1  (fireCount_ne_one)
      fireCount(q) >= 0

    From constraint 1: ccwMoveCountAt(q) = cwMoveCountAt(left(q))
    So: fireCount(q) = cwMoveCountAt(q) + cwMoveCountAt(left(q)) + stayMoveCountAt(q)

    If cwMoveCountAt(q) = 0 AND cwMoveCountAt(left(q)) = 0:
      fireCount(q) = stayMoveCountAt(q)
      If fireCount(q) = 0: q never fires
      If fireCount(q) >= 2: q fires >= 2 times, all stays

    Key: if q never fires AND the mover visits q's neighborhood (no safe processor),
    then q's value is constant in the cycle (config_val_const_at_neverMover).
    But this doesn't directly give a contradiction.

    Actually, trapped means cwMoveCountAt(q) = ccwMoveCountAt(q) = 0.
    From edgeNetFlow: cwMoveCountAt(q) = 0 => ccwMoveCountAt(right(q)) = 0.
    And ccwMoveCountAt(q) = 0 means cwMoveCountAt(left(q)) = 0.

    So if q is trapped: right(q) has ccwMoveCountAt = 0, and left(q) has cwMoveCountAt = 0.

    If additionally right(q) has cwMoveCountAt = 0, then right(q) is also trapped.
    Chain: if q trapped and cwMoveCountAt(right(q)) = 0, then right(q) is trapped.

    But cwMoveCountAt(right(q)) could be > 0. In that case right(q) fires CW,
    and right(q) is not trapped.

    The key insight: if a processor fires CW, it contributes to cwStepCount.
    And cwStepCount > 0 is our hypothesis. So there's no contradiction just from
    the counts.

    The ENTRY CONFLICT argument goes deeper: it looks at the actual transition
    function values and shows they must simultaneously output two different values
    for the same input. This is fundamentally different from counting arguments.
    """
    print("=" * 70)
    print("Trapped chain theory analysis")
    print("=" * 70)
    print()
    print("The trapped-chain argument alone is INSUFFICIENT to prove the axiom.")
    print("It handles the case where processors are fully trapped (cw=ccw=0).")
    print("But when cwStepCount > 0, some processors fire CW, and the chain")
    print("has 'breaks' at those processors.")
    print()
    print("The ENTRY CONFLICT argument is needed for the remaining cases.")
    print("This requires MinGapArc/BounceArc/BAFArcAdj infrastructure.")
    print()
    print("HOWEVER: looking at the sorry's more carefully...")
    print()
    print("Sorry 1-2 (lines 183, 188): CW witness found but can't connect to MinGapArc")
    print("Sorry 3 (line 228): Double-trapped, surviving active neighbors")
    print("Sorry 4 (line 232): Non-consecutive binary")
    print()
    print("ALL of these route through the SAME infrastructure.")
    print("The GlobalMinGap approach tries to find a globally-minimum-gap CW-CCW pair")
    print("and then apply BounceArc/BAFArcAdj. The sorry's are where the connection")
    print("from the global min triple to the MinGapArc/BounceArc fails.")
    print()
    print("ALTERNATIVE: Can we restructure GlobalMinGap.lean to close the sorry's")
    print("without changing the approach?")


def check_sorry_structure():
    """Analyze what each sorry actually needs."""
    print("=" * 70)
    print("Sorry structure analysis")
    print("=" * 70)
    print()
    print("Sorry at line 183 (consecutive, CW witness, CW-CCW pair):")
    print("  Context: binary_right_witness_or_trapped gives CW witness at some edge")
    print("  htypes₀ is CW-CCW or CCW-CW at the global min triple")
    print("  Need: False from having BOTH a CW witness AND a global min pair")
    print("  The CW witness gives cwMoveCountAt(p) > 0 at a binary-right edge")
    print("  But the global min triple might be at a DIFFERENT edge")
    print()
    print("  KEY INSIGHT: The CW witness IS enough by itself!")
    print("  cwMoveCountAt(p) > 0 at binary-right edge means there IS a CW crossing")
    print("  at that edge. Zero winding means there's also a CCW crossing at that edge.")
    print("  So we can build a paired crossing at the SAME binary-right edge,")
    print("  not at the global min triple's edge.")
    print()
    print("  But the global min ensures the gap is small enough for BounceArc.")
    print("  Without global min, the gap could be large and the BounceArc argument")
    print("  might not apply.")
    print()
    print("  WAIT: BounceArc doesn't need a small gap! It needs:")
    print("  1. CW-CCW paired crossing at edge (p, right p)")
    print("  2. Binary right(p)")
    print("  3. Gap >= 2 (between a and b)")
    print("  4. b+1 < L")
    print("  5. GLOBAL MINIMALITY of the gap")
    print()
    print("  The global minimality IS needed for BounceArc's mover confinement argument.")
    print("  Without it, the mover could wander far and break the entry conflict.")
    print()
    print("  So the sorry is about connecting: 'CW witness at some binary-right edge'")
    print("  to 'global min gap triple at THAT binary-right edge (or equivalent)'.")
    print()
    print("Sorry at line 228 (double-trapped, surviving):")
    print("  Context: i and right(i) are trapped (cw=ccw=0)")
    print("  Mover visits left(i) and right²(i)")
    print("  ccwMoveCountAt(left i) > 0 and cwMoveCountAt(right²(i)) > 0")
    print("  Need: False")
    print()
    print("  This means: left(i) fires CCW, right²(i) fires CW.")
    print("  left(i) firing CCW means it crosses edge (left(left(i)), left(i)) leftward")
    print("  = ccwMoveCountAt(left(i)) > 0 => cwMoveCountAt(left(left(i))) > 0")
    print("  (from edgeNetFlow at left(left(i)))")
    print()
    print("  So left(left(i)) fires CW. And right²(i) fires CW.")
    print("  Neither i nor right(i) fires at all (trapped with no stays? no, they could stay)")
    print("  Actually trapped means cw=ccw=0 but stayMoveCountAt could be > 0.")
    print("  For trapped with mover NOT visiting: they never fire at all (fireCount = 0).")
    print("  For trapped with mover visiting: they fire only stays.")
    print()
    print("  The existing code proves: if mover visits trapped proc => contradiction.")
    print("  So i and right(i) are NEVER the mover. They never fire.")
    print("  This means fireCount(i) = fireCount(right(i)) = 0.")
    print("  The mover only visits left(i) and right²(i).")
    print()
    print("  Hmm but hno_safe only says mover visits NEIGHBORHOOD of every proc.")
    print("  For proc right²(i): mover visits {right²(i), right(i), right³(i)}.")
    print("  We know mover visits right²(i) (from hk_ri with hmov_rri).")
    print("  For proc left(i): mover visits {left(i), left²(i), i}.")
    print("  We know mover visits left(i) (from hk_i with hmov_li).")
    print()
    print("  So: fireCount(i) = 0, fireCount(right(i)) = 0.")
    print("  What about procs left(left(i)), left(i), right²(i), right³(i), ...?")
    print()
    print("  With n >= 9, there are many more procs.")
    print("  This case seems genuinely hard without entry conflict.")

    print()
    print("Sorry at line 232 (non-consecutive binary):")
    print("  This is the 4-mechanism universal EC from BinSCC Expl 10.")
    print("  Completely different argument. Hard to formalize.")


def explore_new_approach():
    """Explore whether the proof can avoid GlobalMinGap entirely."""
    print()
    print("=" * 70)
    print("NEW APPROACH: Avoid GlobalMinGap entirely")
    print("=" * 70)
    print()
    print("Observation: ConsecutiveBinaryEC.lean and GlobalMinGap.lean BOTH")
    print("try to prove the same thing and BOTH have sorry's/circular deps.")
    print()
    print("What if we REPLACE large_arc_zeroWinding_direct with a proof that")
    print("delegates to ConsecutiveBinaryEC.consecutive_binary_zeroWinding_false")
    print("for the consecutive case, and a new non-consecutive argument?")
    print()
    print("But ConsecutiveBinaryEC calls cwWitness_gives_false which calls")
    print("large_arc_zeroWinding_ec_proof which IS large_arc_zeroWinding_direct.")
    print("CIRCULAR!")
    print()
    print("The circularity chain:")
    print("  large_arc_zeroWinding_direct (GlobalMinGap) --sorry-->")
    print("  large_arc_zeroWinding_ec_proof (GlobalMinGap) --def-->")
    print("  large_arc_zeroWinding_direct (GlobalMinGap)")
    print()
    print("AND:")
    print("  cwWitness_gives_false (ConsecutiveBinaryEC) --uses-->")
    print("  large_arc_zeroWinding_ec_proof (GlobalMinGap)")
    print()
    print("  double_trapped_false (ConsecutiveBinaryEC) --uses-->")
    print("  large_arc_zeroWinding_ec_proof (GlobalMinGap)")
    print()
    print("To break the circularity:")
    print("1. cwWitness_gives_false should NOT delegate to ec_proof.")
    print("   It should directly use BounceArc infrastructure.")
    print("2. double_trapped_false should use a different argument for the")
    print("   surviving case.")
    print()
    print("For cwWitness_gives_false:")
    print("  We have: CW witness at binary-right edge (p, right(p)).")
    print("  cwMoveCountAt(p) > 0.")
    print("  Zero winding => edgeNetFlow(p) = 0 => ccwMoveCountAt(right(p)) > 0.")
    print("  So there exists a CCW crossing at edge (p, right(p)).")
    print("  Combined with the CW crossing: we have a paired CW-CCW crossing")
    print("  at the SAME edge (p, right(p)) which HAS binary right(p).")
    print()
    print("  Then: find the MIN GAP pair at THIS edge (p, right(p)).")
    print("  The global min gap over ALL edges is <= the gap at this edge.")
    print("  Apply BounceArc at the global min gap.")
    print()
    print("  But we need: global min gap triple has binary right.")
    print("  The global min might be at a DIFFERENT edge without binary right!")
    print()
    print("  UNLESS we restrict to binary-right edges only.")
    print("  With >= 3 binary processors, there are >= 3 binary-right edges.")
    print("  The CW witness gives a pair at one such edge.")
    print("  We can restrict globalOppPairs to binary-right edges only!")
    print()
    print("  Define: binaryRightOppPairs = globalOppPairs filtered to edges")
    print("  with binary right endpoint. Find its global min. Apply BounceArc.")
    print()
    print("  This should work IF we can show binaryRightOppPairs is nonempty")
    print("  (which follows from the CW witness + zero winding).")
    print()
    print("  ALTERNATIVELY: we don't need global min over ALL edges.")
    print("  BounceArc.lean says the mover stays at right(p) throughout (a+1, b)")
    print("  because it can't fire CW or CCW. This uses GLOBAL minimality")
    print("  (if it fired CW, it would create a smaller pair at some edge).")
    print("  But maybe we only need minimality at THIS edge?")
    print()
    print("  Let me check BounceArc more carefully...")


if __name__ == "__main__":
    analyze_zero_winding_cycles()
    check_trapped_chain_theory()
    check_sorry_structure()
    explore_new_approach()
