#!/usr/bin/env python3
"""Check: does gap=1 EVER occur at the global min in a zero-winding cycle?

Test with actual valid systems (above threshold) that have 3+ binary procs.
The gap=1 sorry in CleanProof.lean needs to handle any good cycle
satisfying the hypotheses, not just sub-threshold ones.

The theorem is: 3 consecutive binary + zero winding + cw>0 + no safe → False.
This is used for sub-threshold systems, but the theorem itself is about
arbitrary systems satisfying the hypotheses.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import all_configs, privileged_set, apply_move

def get_good_cycle(ms, fs):
    """Extract the good cycle."""
    n = len(ms)
    configs = list(all_configs(ms))
    single_priv = {c for c in configs if len(privileged_set(c, fs, ms)) == 1}

    succ = {}
    mover_map = {}
    for c in single_priv:
        priv = privileged_set(c, fs, ms)
        if len(priv) == 1:
            s = apply_move(c, priv[0], fs, ms)
            if s in single_priv:
                succ[c] = s
                mover_map[c] = priv[0]

    visited = set()
    for start in succ:
        if start in visited:
            continue
        path = []
        vis = set()
        c = start
        while c not in vis and c in succ:
            vis.add(c)
            path.append(c)
            c = succ[c]
        if c in vis:
            idx = path.index(c)
            cycle_configs = path[idx:]
            cycle = [(cfg, mover_map[cfg]) for cfg in cycle_configs]
            return cycle
        visited.update(path)
    return None


def analyze(cycle, ms, n):
    L = len(cycle)
    movers = [cycle[i][1] for i in range(L)]
    dirs = []
    for i in range(L):
        m_now = movers[i]
        m_next = movers[(i+1) % L]
        if m_next == (m_now + 1) % n:
            dirs.append('CW')
        elif m_next == (m_now - 1) % n:
            dirs.append('CCW')
        else:
            dirs.append('STAY')

    # Zero winding check
    zw = True
    for p in range(n):
        rp = (p + 1) % n
        cw = sum(1 for i in range(L) if movers[i] == p and dirs[i] == 'CW')
        ccw = sum(1 for i in range(L) if movers[i] == rp and dirs[i] == 'CCW')
        if cw != ccw:
            zw = False
            break

    # Safe proc
    safe = False
    for q in range(n):
        lq = (q - 1) % n
        rq = (q + 1) % n
        if all(movers[i] != q and movers[i] != lq and movers[i] != rq for i in range(L)):
            safe = True
            break

    cw_count = sum(1 for d in dirs if d == 'CW')

    # Global min gap
    min_gap = float('inf')
    for p in range(n):
        rp = (p + 1) % n
        crossings = []
        for i in range(L):
            if movers[i] == p and dirs[i] == 'CW':
                crossings.append((i, 'CW'))
            elif movers[i] == rp and dirs[i] == 'CCW':
                crossings.append((i, 'CCW'))
        for i1 in range(len(crossings)):
            for i2 in range(i1+1, len(crossings)):
                s1, d1 = crossings[i1]
                s2, d2 = crossings[i2]
                if d1 != d2:
                    has_between = any(s1 < crossings[i3][0] < s2
                                     for i3 in range(len(crossings)))
                    if not has_between:
                        gap = s2 - s1
                        min_gap = min(min_gap, gap)

    return zw, safe, cw_count, min_gap, movers, dirs


def check_m5_96_witness():
    """Check the M_5=96 witness: ms=[2,2,2,3,4]."""
    print("=== M_5=96 witness ms=[2,2,2,3,4] ===")
    # Need to find the actual transition functions
    # From the verifier paper, there's a valid system with ms=[2,2,2,3,4]
    # Let me try to find it via search
    import random
    random.seed(42)
    ms = [2, 2, 2, 3, 4]
    n = 5

    for trial in range(100000):
        fs = []
        for i in range(n):
            m_L = ms[(i-1) % n]
            m_S = ms[i]
            m_R = ms[(i+1) % n]
            table = {}
            for L in range(m_L):
                for S in range(m_S):
                    for R in range(m_R):
                        table[(L, S, R)] = random.randint(0, m_S - 1)
            def f(L, S, R, t=table):
                return t[(L, S, R)]
            fs.append(f)

        cycle = get_good_cycle(ms, fs)
        if cycle is None:
            continue

        zw, safe, cw_count, min_gap, movers, dirs = analyze(cycle, ms, n)
        if zw and not safe and cw_count > 0:
            print(f"  trial={trial}: L={len(cycle)}, gap={min_gap}")
            print(f"  movers={movers}")
            print(f"  dirs={dirs}")
            if min_gap <= 2:
                print(f"  *** SMALL GAP ***")
            break

    if trial == 99999:
        print("  No zero-winding cycle found in 100K trials")


def check_n9_above_threshold():
    """Check at n=9 with ms=(2,2,2,3,...,3) at threshold product."""
    from cup2_theorem import build_system

    # CUP-2 system has ms=(2,3,...,3,2)
    # Not 3 consecutive binary. Let me check anyway.
    for n in [5, 6, 7, 8, 9]:
        ms, fs = build_system(n)
        binary_procs = [p for p in range(n) if ms[p] == 2]

        cycle = get_good_cycle(ms, fs)
        if cycle is None:
            print(f"n={n}: no cycle")
            continue

        zw, safe, cw_count, min_gap, movers, dirs = analyze(cycle, ms, n)
        print(f"n={n}: L={len(cycle)}, zw={zw}, safe={safe}, cw={cw_count}, "
              f"gap={min_gap}, binary={binary_procs}")


def check_arbitrary_cycles():
    """Generate arbitrary good cycles (not from valid systems) and check gap.

    A good cycle is just a sequence of configs where each step has exactly
    one privileged processor. We can CONSTRUCT such cycles directly.

    Actually, the easier approach: just check if gap=1 can occur by
    looking at the mover sequence constraints.

    For a zero-winding cycle with 3 consecutive binary,
    CW-CCW gap=1 at global min means:
    step a: mover=p, CW
    step a+1: mover=right(p), CCW
    step a+2: mover=p

    If right(p) is binary, right(p) fires 1 time in steps a..a+1.
    right(p) fires >= 2 total. So right(p) fires elsewhere.
    Each firing of right(p) is isolated (no consecutive right(p) firings)
    or part of a run.

    If right(p) has a run of >= 2 consecutive firings anywhere: EC.
    If all firings isolated: right(p) fires CW or CCW at each.
    CCW at right(p) = crossing edge (p, right(p)).
    CW at right(p) = crossing edge (right(p), right(right(p))).

    Zero winding at edge (p, right(p)):
    cwMoveCountAt(p) = ccwMoveCountAt(right(p))
    = (number of times right(p) fires CCW)

    So: number of CW crossings by p = number of CCW crossings by right(p).

    If right(p) fires k times: some CW, some CCW, k is even >= 2.
    Say right(p) fires c times CW and d times CCW, c+d = k, k even.
    ccwMoveCountAt(right(p)) = d.
    cwMoveCountAt(p) = d.

    Zero winding at edge (right(p), right(right(p))):
    cwMoveCountAt(right(p)) = c = ccwMoveCountAt(right(right(p))).

    So c CW crossings at edge (right(p), rr(p)), d CCW crossings at edge (p, right(p)).

    Now, for the global min gap to be 1, every paired crossing at every edge
    must have gap >= 1 (vacuous). But we can show gap >= 2 must hold
    at some edge, contradicting global min = 1? Not obvious.

    KEY: The gap=1 pair at (p, right(p)) has CW at a, CCW at a+1.
    The CCW crossing is by right(p). So right(p) fires CCW at step a+1.
    right(p) has another firing somewhere. If that other firing is also CCW
    at edge (p, right(p)), we get another CCW crossing.
    Together with the CW crossing at a, we might get a new paired crossing.
    Its gap could be larger or smaller than 1.

    But since global min = 1, no paired crossing can have gap < 1.
    Gap >= 1 is vacuous. So no constraint.

    CONCLUSION: I think gap=1 CAN occur in principle (as a mover pattern).
    The question is whether the entry conflict can still be derived.
    """
    pass


def check_consec_firing_from_bounce():
    """Check the bounce argument:
    If mover bounces p, rp, p, rp, ... and eventually stops,
    does the stopping always produce consecutive firings?

    At step a: p CW → rp
    At step a+1: rp ? → ?
    If rp CCW → p: bounce continues
    If rp STAY → rp: rp fires at a+1 and a+2 CONSECUTIVE → EC on rp
    If rp CW → rr(p): bounce exits CW

    If bounce continues (rp CCW):
    At step a+2: p ? → ?
    If p CW → rp: bounce continues
    If p STAY → p: p fires at a+2 and a+3 CONSECUTIVE → EC on p
    If p CCW → left(p): bounce exits CCW

    So: the only way to NOT get consecutive firings is:
    - p always CW, rp always CCW (alternating bounce)
    - or p/rp exits the bounce (CW to rr(p) or CCW to left(p))

    The alternating bounce: p CW, rp CCW, p CW, rp CCW, ...
    This is periodic. For zero winding at edge (p, rp):
    Each "p CW" adds 1 to cwMoveCountAt(p).
    Each "rp CCW" adds 1 to ccwMoveCountAt(rp).
    They're equal: cwMoveCountAt(p) = ccwMoveCountAt(rp). ✓

    For zero winding at edge (rp, rr(p)):
    cwMoveCountAt(rp) = ccwMoveCountAt(rr(p)).
    In the alternating bounce, rp only fires CCW (never CW).
    So cwMoveCountAt(rp) = 0. But other steps might have rp firing CW.
    If rp ONLY fires in this bounce: cwMoveCountAt(rp) = 0.
    Zero winding → ccwMoveCountAt(rr(p)) = 0 at this edge.

    Similarly, zero winding at edge (left(p), p):
    cwMoveCountAt(left(p)) = ccwMoveCountAt(p).
    In the bounce, p only fires CW (never CCW).
    If p ONLY fires in this bounce: ccwMoveCountAt(p) = 0.
    Zero winding → cwMoveCountAt(left(p)) = 0 at this edge.

    So: in the pure alternating bounce, we get:
    cwMoveCountAt(rp) = 0 → ccwMoveCountAt(rr(p)) = 0 at edge (rp, rr(p))
    ccwMoveCountAt(p) = 0 → cwMoveCountAt(left(p)) = 0 at edge (left(p), p)

    And both p and rp fire k times each (k = half the bounce length).
    p fires k CW, rp fires k CCW.
    p is binary → k is even → k >= 2.
    rp is binary → k is even → k >= 2.
    So k = 2, 4, 6, ...

    For n >= 9 and the mover only visiting p and rp:
    Processor q = rr(rp) = right^3(p) has:
    - mover ≠ q (mover only at p, rp)
    - mover ≠ left(q) = rr(p) (mover not at rr(p))
    - mover ≠ right(q) = right^4(p) (mover not there)
    Since n >= 5, right^3(p) ≠ p and right^3(p) ≠ right(p).
    Wait, for n=5: right^3(p) could equal left(p) = right^4(p) = right^{-1}(p)...
    right^3(p) = (p+3)%5. left(p) = (p+4)%5. Different for n=5.
    q = (p+3)%5: left(q) = (p+2)%5 = rr(p). If mover only at p and (p+1)%5:
    mover ≠ (p+3)%5 ✓, mover ≠ (p+2)%5 ✓, mover ≠ (p+4)%5 ✓.
    So q is safe → contradicts hno_safe. ✓ for n >= 5.

    So the pure alternating bounce → safe processor → contradiction with hno_safe.

    CONCLUSION: In the bounce at (p, rp), it must eventually exit.
    Exit via STAY → consecutive firings → EC.
    Exit via CW from rp or CCW from p → mover leaves the pair.

    After leaving: the mover is at rr(p) or left(p). From there, it might return
    to p, rp or go further. Eventually it returns (no safe processor).

    But does the bounce produce consecutive firings? Not necessarily if it
    exits via CW/CCW (not STAY).

    However: the mover EVENTUALLY returns to p or rp (no safe processor).
    When it returns, it might bounce again. Each bounce exit is CW from rp
    or CCW from p. These create additional crossings.

    OK I think the key insight is: for the gap=1 case, we should use
    the BINARY PROCESSOR's firing structure differently.

    ALTERNATIVE PROOF IDEA:
    Since right(p) is binary and fires >= 2 times, find two firing steps s1 < s2.
    Between s1 and s2, right(p) doesn't fire (if they're consecutive firings).
    If s2 = s1 + 1: right(p) fires at consecutive steps → EC.
    If s2 > s1 + 1: right(p) fires at s1, not at s1+1, ..., fires at s2.
       At step s1: right(p) fires CW or CCW (not stay, since mover(s1+1) ≠ right(p)).
       At step s1: context (L, S, R) = (config[s1][p], config[s1][right(p)], config[s1][rr(p)])
       At step s2: context (L', S', R') = (config[s2][p], config[s2][right(p)], config[s2][rr(p)])

       For EC at right(p): need a mover step and a non-mover step with same context.

       Actually, use binary_config_eq_of_prefix_parity: if right(p) fires an EVEN
       number of times between s1 and s2, then S at s1 = S at s2.
       right(p) fires 0 times between s1 and s2 (since they're consecutive firings,
       no firing between). So prefixFireCount(right(p), s2) = prefixFireCount(right(p), s1) + 1.
       Wait: prefixFireCount counts firings at steps < s. So:
       prefixFireCount(right(p), s2) = prefixFireCount(right(p), s1) + 1 (right(p) fires at s1)
       + (number of right(p) firings at steps s1+1, ..., s2-1, which is 0)
       = prefixFireCount(right(p), s1) + 1.
       Parity change: 1 (odd). So config[s1][right(p)] ≠ config[s2][right(p)].
       Different S → no EC from these two steps alone.

       What about s1 and a NON-MOVER step with same context?
       At step s1: right(p) fires. At step s1-1: mover ≠ right(p) (if right(p) is isolated).
       Context at step s1: (config[s1][p], config[s1][right(p)], config[s1][rr(p)])
       Non-mover at step s1-1: context at right(p) is
       (config[s1-1][p], config[s1-1][right(p)], config[s1-1][rr(p)])

       Wait, we don't know if step s1-1 has mover ≠ right(p) unless s1 is NOT the first
       step (wrap around) or we explicitly prove it.

    This is getting nowhere fast. Let me just count: in the CW-CCW gap=1 case,
    how many sorrys can be closed and how, and focus on the LEAN code.
    """
    # The bounce argument shows: if the mover bounces between p and rp,
    # it must eventually:
    # a) STAY at p or rp → consecutive firings → EC, or
    # b) exit the bounce → mover visits other procs → eventually returns

    # For (b): the mover creates additional crossings at other edges.
    # These crossings have gap >= 1 (global min). But the argument gets complex.

    # PRAGMATIC DECISION: Handle gap=1 by:
    # 1. Find consecutive firings of right(p_g) (binary, fires >= 2)
    # 2. If consecutive: contiguous_run → EC
    # 3. If not consecutive: p_g fires at a_g and a_g+2 (gap 2 for p_g).
    #    Need p_g binary? Not necessarily.
    #    But if p_g is also binary (from hkey: both p and right(p) binary,
    #    but p_g might not be p): we need a different approach.

    # WAIT: In the `hkey` proof, we're trying to prove False given:
    # p with both p and right(p) binary, cwMoveCountAt(p) > 0.
    # The global min triple (p_g, a_g, b_g) might be at a different edge.
    # We have sorry at gap=1 with right(p_g) binary.
    #
    # ALTERNATIVE: Don't use the global min. Instead, get the paired crossing
    # at edge (p, right(p)) directly. Both p and right(p) are binary.
    # Use exists_paired_edge_crossing to get (a, b) at this edge.
    # This gives minimal gap at THIS edge (with hno: no crossing between).
    # Then build the MinGapArc-LIKE structure using ONLY this edge's minimality.
    #
    # The problem: for the stay chain, we need hglobal (no smaller gap anywhere).
    # Without it, right(p) might fire CW in (a,b), creating a crossing at
    # the adjacent edge with gap < our gap. But that's fine! It just means
    # the stay chain might not hold.
    #
    # HOWEVER: if we use the minimum gap at THIS specific edge, the CW firing
    # of right(p) in (a,b) would create a crossing at the ADJACENT edge.
    # But at our edge (p, right(p)), it would NOT be a crossing (right(p) CW
    # doesn't cross edge (p, right(p))). So the no-crossing-between condition
    # (hno) is preserved. The issue is with CCW: right(p) CCW in (a,b) would
    # cross edge (p, right(p)), violating hno. CONTRADICTION!
    #
    # So: right(p) can NOT fire CCW in (a,b) (since that would cross our edge).
    # But right(p) CAN fire CW in (a,b) (crosses the adjacent edge, not ours).
    #
    # For the stay chain: right(p) can only fire CW (not CCW, not stay unless
    # we can block CW too). If right(p) fires CW at step k in (a,b):
    # next mover = rr(p) ≠ right(p). So right(p) doesn't fire at k+1.
    # But the mover could come back to right(p) later.
    #
    # Without hglobal, we can't block right(p) from firing CW in (a,b).
    # So the stay chain doesn't hold. right(p) might fire CW, leave, and return.
    #
    # BUT: we still know right(p) fires at a+1 (from CW crossing at a → next = right(p)).
    # And right(p) can't fire CCW in (a,b) (hno). So right(p) fires CW or STAY.
    # If STAY: consecutive firings → EC.
    # If CW: mover goes to rr(p). Mover might return or not.
    #
    # IDEA: block right(p) CW using a DIFFERENT argument.
    # From not_ccw_at_right_between_crossings: right(p) can't fire CCW between (a,b)
    # (this only uses hno, not hglobal). ✓
    # From no_cw_fire_at_right_in_minGap: right(p) can't fire CW between (a,b)
    # (this uses hglobal). ✗ without global min.
    #
    # So the problem is really: blocking right(p) CW in (a,b).
    #
    # BUT: if we use the GLOBAL min, the global min gap G satisfies:
    # G <= gap at edge (p, right(p)). If G = 1: every paired crossing has gap >= 1.
    # Including the one created by right(p) firing CW at k in (a,b): this creates
    # a CW crossing at edge (right(p), rr(p)) at step k. Combined with some
    # CCW crossing at that edge (from zero winding if applicable):
    # the paired crossing at (right(p), rr(p)) has gap >= 1.
    #
    # But: the paired crossing (CW at a, CW at k) at edge (p, right(p)) and edge
    # (right(p), rr(p)) doesn't directly give a contradiction. The gap at edge
    # (right(p), rr(p)) could be >= 1. No contradiction.
    #
    # HOWEVER: the hglobal argument shows that the gap created at edge (right(p), rr(p))
    # by CW at k and some paired crossing: gap d satisfies G <= d. But also
    # d < b-a (since k is strictly between a and b). So G <= d < b-a.
    # If b-a = G (our pair IS the global min): G <= d < G, contradiction!
    # If b-a > G (our pair is NOT the global min): G <= d < b-a, no contradiction.
    #
    # So the CW blocking only works if our pair IS the global min.
    #
    # CONCLUSION: We really do need to use the global min pair for the stay chain.
    # And the gap=1 case genuinely needs a different proof strategy.

    print("\n=== Bounce/stay analysis ===")
    print("Gap=1 CW-CCW: p CW at a, rp CCW at a+1, p at a+2")
    print("At a+2, p fires CW/CCW/STAY:")
    print("  STAY → p fires at a+2 and a+3 consecutive → IF P BINARY: EC")
    print("  CW → bounce continues: rp fires at a+3 (CW or CCW or STAY)")
    print("    STAY → rp fires at a+3 and a+4 consecutive → EC on rp (binary)")
    print("    CCW → bounce: p at a+4, pattern p,rp,p,rp,...")
    print("    CW → rp leaves CW to rr(p)")
    print("  CCW → p leaves to left(p)")
    print()
    print("For the GLOBAL MIN gap=1 pair (p_g, a_g, a_g+1) with right(p_g) binary:")
    print("  Step a_g: p_g CW, step a_g+1: right(p_g) CCW, step a_g+2: p_g")
    print("  right(p_g) fires at a_g+1. right(p_g) is binary, fires >= 2.")
    print()
    print("  At step a_g+2, p_g fires with some direction.")
    print("  If STAY: p_g fires at a_g+2 and a_g+3. Need p_g binary for EC.")
    print("  But we only have right(p_g) binary, not p_g!")
    print()
    print("  KEY: In the hkey proof, we have p with BOTH p and right(p) binary.")
    print("  The global min p_g might differ from p.")
    print()
    print("  SOLUTION: Instead of gap=1 sorry for the global min,")
    print("  RESTRUCTURE the proof to use the binary-right pair (p, right(p))")
    print("  from hkey's hypotheses directly.")


if __name__ == '__main__':
    check_consec_firing_from_bounce()
    check_n9_above_threshold()
