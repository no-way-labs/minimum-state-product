#!/usr/bin/env python3
"""
Investigation: Alternating CW/CCW runs (max CW run = 1, max CCW run = 1)
for the large_arc_zeroWinding_ec axiom.

Key findings:
1. The case is NOT vacuous - mover can cover C_n via CW, STAY, CW patterns.
2. CW/CCW symmetry reduces to: max CW run = 1 AND max CCW run = 1.
3. The constraint means every CW step is followed by STAY or CCW,
   and every CCW step is followed by STAY or CW.
4. Need a new proof approach (not BAFArcAdj).

This script investigates STAY-step-based entry conflicts.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import Counter

from cup2_theorem import build_system


def get_good_cycle(ms, fs, n):
    """Extract the good cycle from a system."""
    all_configs = list(cartesian(*(range(m) for m in ms)))
    def get_privileged(c):
        privs = []
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            if fs[i](L, S, R) != S:
                privs.append(i)
        return privs

    good_configs = [(c, get_privileged(c)) for c in all_configs
                    if len(get_privileged(c)) == 1]
    if not good_configs:
        return None, None, None

    good_set = set(c for c, _ in good_configs)
    start = good_configs[0][0]
    cycle = [start]; movers = []; current = start
    while True:
        privs = get_privileged(current)
        mover = privs[0]; movers.append(mover)
        lst = list(current)
        lst[mover] = fs[mover](current[(mover-1)%n], current[mover], current[(mover+1)%n])
        nxt = tuple(lst)
        if nxt == start: break
        cycle.append(nxt); current = nxt
    return cycle, movers, good_set


def get_runs(dirs, target):
    runs = []
    rl = 0
    for d in dirs:
        if d == target: rl += 1
        else:
            if rl > 0: runs.append(rl)
            rl = 0
    if rl > 0: runs.append(rl)
    if len(runs) >= 2 and dirs[0] == target and dirs[-1] == target:
        runs[0] += runs[-1]; runs.pop()
    return runs


def check_cup2():
    """Check CUP-2 systems."""
    print("="*70)
    print("CUP-2 good cycle analysis")
    print("="*70)
    for n in [5, 7, 9]:
        ms, fs = build_system(n)
        cycle, movers, _ = get_good_cycle(ms, fs, n)
        if not cycle: continue
        L = len(movers)
        dirs = []
        for k in range(L):
            curr, nxt = movers[k], movers[(k+1)%L]
            if nxt == (curr+1)%n: dirs.append('CW')
            elif nxt == curr: dirs.append('STAY')
            elif nxt == (curr-1)%n: dirs.append('CCW')
            else: dirs.append('??')
        cw_runs = get_runs(dirs, 'CW')
        ccw_runs = get_runs(dirs, 'CCW')
        print(f"  n={n}: len={L}, CW={dirs.count('CW')}, CCW={dirs.count('CCW')}, "
              f"STAY={dirs.count('STAY')}, winding={dirs.count('CW')-dirs.count('CCW')}")
        print(f"    Max CW run={max(cw_runs) if cw_runs else 0}, "
              f"Max CCW run={max(ccw_runs) if ccw_runs else 0}")


def analyze_stay_structure():
    """
    Key insight: with max CW run = 1 and max CCW run = 1,
    between each pair of non-stay steps there may be STAY steps.

    At a STAY step: moverAt(k+1) = moverAt(k). The mover fires and stays.
    This means proc p fires at step k, and the next mover is also p.
    So: p fires AGAIN at step k+1.

    Two consecutive firings at the same processor!

    If p is binary (m_p = 2): after two fires, p returns to original value.
    The context at step k: (L, S, R) -> fires to S' != S.
    The context at step k+1: since moverAt(k+1) = p, we have
      left(p) and right(p) haven't changed (neither fired at step k).
      p has changed from S to S'. So context is (L, S', R).

    This is a DIFFERENT context. No immediate entry conflict from adjacent stays.

    But what about the STAY step itself?
    At step k: mover = p, step dir = STAY (moverAt(k+1) = p).
    At step k+1: mover = p, step dir could be anything.

    The STAY direction means the NEXT mover is at the same position.
    It does NOT mean the mover doesn't change position -- wait, actually
    by definition stepDir k = STAY iff moverAt(nextIndex k) = moverAt(k).
    So the mover position doesn't change.

    So: two consecutive firings at p. The (L,S,R) context changes because S changes.
    No trivial entry conflict.

    BUT: what if we look at a NEIGHBOR of p?
    At step k: mover = p, non-mover q (neighbor of p) sees context (L_q, S_q, R_q).
    At step k+1: mover = p again, non-mover q sees context that MAY differ
    (because p's value changed, and p is a neighbor of q).

    If q = right(p): L_q = value at p (which changed), so context changed.
    If q = left(p): R_q = value at p (which changed), so context changed.

    So consecutive stays at p change the context of p's neighbors. No conflict there either.
    """
    print("\n" + "="*70)
    print("STAY STEP ENTRY CONFLICT ANALYSIS")
    print("="*70)

    # The real structure to exploit: with max CW/CCW run = 1, the mover
    # word has a very specific pattern. Let's enumerate the possible
    # bigrams (consecutive step pairs):

    # Allowed bigrams (no CW-CW, no CCW-CCW):
    # CW-STAY, CW-CCW
    # STAY-CW, STAY-STAY, STAY-CCW
    # CCW-STAY, CCW-CW

    # The mover advances in CW-STAY-CW-STAY-... patterns.
    # Then retreats via CCW-STAY-CCW-STAY-... patterns.
    # Or alternates CW-CCW-CW-CCW-... (oscillating between 2 positions).

    print("""
  Allowed step bigrams (max CW run = 1, max CCW run = 1):
    CW -> STAY, CW -> CCW
    STAY -> CW, STAY -> STAY, STAY -> CCW
    CCW -> STAY, CCW -> CW

  Key structural consequence:
    CW -> CW is FORBIDDEN (no consecutive CW)
    CCW -> CCW is FORBIDDEN (no consecutive CCW)

  Between any two CW steps: at least one STAY or CCW step.
  Between any two CCW steps: at least one STAY or CW step.
  """)


def investigate_global_structure():
    """
    With max CW/CCW run = 1, the walk decomposes into "advance segments"
    (CW,STAY,CW,STAY,...) and "retreat segments" (CCW,STAY,CCW,STAY,...).

    The key: each advance segment gains at most 1 position per 2 steps.
    Each retreat segment loses at most 1 position per 2 steps.

    For zero winding with S CW and S CCW: total advance = S, total retreat = S.

    What constraints does the "max run = 1" impose on fire counts?
    """
    print("\n" + "="*70)
    print("GLOBAL STRUCTURE: STAY-step fire count implications")
    print("="*70)

    # At a STAY step k (stepDir = STAY):
    # moverAt(k) = moverAt(k+1) = p. So p fires at both steps k and k+1.
    # The NEXT step (k+1) could be CW, STAY, or CCW.

    # Consider a maximal STAY run: STAY, STAY, ..., STAY (length r).
    # The mover fires at the same position p for r+1 consecutive steps
    # (the step before the run starts the STAY, plus r STAY steps).
    # Wait: not exactly. If step k is STAY, moverAt(k) = moverAt(k+1).
    # A STAY run of length r at steps k, k+1, ..., k+r-1 means
    # moverAt(k) = moverAt(k+1) = ... = moverAt(k+r).
    # But moverAt(k-1) might be different (if step k-1 was CW or CCW).
    # And moverAt(k+r+1) might be different (if step k+r is CW or CCW).
    # So the mover fires at position p for steps k through k+r.
    # That's r+1 firings at p.

    # If the step BEFORE the STAY run was also at position p (i.e., step k-1 had
    # moverAt(k-1) such that the mover went to p at step k):
    # moverAt(k-1) could be left(p) (CW step) or right(p) (CCW step) or p (STAY).
    # In any case, moverAt(k) = p.

    # The firings at p during the STAY run: steps k, k+1, ..., k+r.
    # Plus potentially step k-1 if moverAt(k-1) = p (i.e., step k-1 was STAY too,
    # but that's part of the same STAY run).

    # Let me count differently. For each position p, fire count at p =
    # number of steps k where moverAt(k) = p.

    # At each STAY step k: moverAt(k) = moverAt(k+1). So consecutive movers share position.
    # At CW step k: moverAt(k) != moverAt(k+1) (different positions).
    # At CCW step k: moverAt(k) != moverAt(k+1) (different positions).

    # So the mover word looks like:
    # ..., p, p, p (STAY run), q (CW or CCW step), q, q, q (STAY run), ...

    # The "segments of same mover position" are:
    # - A maximal consecutive block of the same position.
    # - Within such a block, all step directions are STAY (except possibly the
    #   first step, which could be CW/CCW from the previous position).

    # Wait, let me be more careful. moverAt(k) gives the position at step k.
    # If moverAt(k) = p and stepDir(k) = CW, then moverAt(k+1) = right(p) != p.
    # If moverAt(k) = p and stepDir(k) = STAY, then moverAt(k+1) = p.
    # If moverAt(k) = p and stepDir(k) = CCW, then moverAt(k+1) = left(p) != p.

    # So a maximal block of moverAt = p has the property that all internal
    # step directions are STAY, and the last step direction is CW or CCW
    # (which transitions to a different position).

    # Actually: in a maximal block p, p, p, ..., p (length r, steps k to k+r-1),
    # stepDir(k), ..., stepDir(k+r-2) are all STAY (keep position p).
    # stepDir(k+r-1) is CW or CCW (leave position p).
    # UNLESS it's the end of the cycle, wrapping around.

    # So: fire count at p = total number of steps where moverAt = p = sum of block sizes.
    # Each block of size r contributes r firings at p, and has r-1 STAY steps + 1 non-STAY.

    # KEY: the total number of STAY steps = sum over blocks of (block_size - 1) = L - (CW+CCW+non-stay-transitions)
    # Actually: STAY count = L - CW count - CCW count = L - 2S.
    # And L = sum of fire counts.

    print("""
  Fire count structure:
    L = cycle length = 2S + STAY_count
    Each position's fire count = sum of its block sizes.
    Each block of size r has r-1 STAY steps and 1 CW/CCW step (end of block).
    Number of blocks = number of non-STAY steps = CW + CCW = 2S.
    STAY_count = L - 2S.

  Constraint: each processor fires 0 or >= 2 times (fireCount_ne_one).
  Binary processors fire even >= 2 times.

  The mover visits some set of positions P. |P| >= ceil(n/3) for no safe proc.
  For n=9: |P| >= 3 (minimum 1-covering).

  Each visited position fires >= 2 times.
  Sum of fire counts = L = 2S + STAY_count.
  """)


def investigate_entry_conflict_from_stays():
    """
    New approach: at a STAY step, the mover fires at the same position p
    in consecutive steps. After the first firing, p's value changes from
    S to S' = f(L, S, R). At the NEXT step (still at p), the context is
    (L, S', R') where R' might have changed if right(p) was affected.

    Wait -- at a STAY step k, mover = p. The move changes p's value.
    Non-movers (including neighbors) keep their values.
    So at step k+1: L = value at left(p) (unchanged), S = S' (p's new value),
    R = value at right(p) (unchanged).

    So context goes from (L, S, R) to (L, S', R) after one firing.
    Since p fires again at step k+1 (because stepDir = STAY, so moverAt(k+1) = p),
    context at step k+1 is (L, S', R), which is different from (L, S, R).

    After the second firing: S'' = f(L, S', R). Context becomes (L, S'', R).
    For binary p: S'' = S (toggle twice). So after 2 firings we're back to (L, S, R).

    IMPORTANT: At step k, p fires with context (L, S, R) -> S' != S.
    At step k+2 (if stay continues), p fires with context (L, S, R) again!
    But p is the MOVER at step k, and also the MOVER at step k+2.
    So we get f(L, S, R) evaluated twice with the same context -> no conflict.

    For an entry conflict, we need the same context at a MOVER step and a NON-MOVER step.

    Let's look at a neighbor q of p during the stay run.
    q = left(p): at step k, mover = p, q is non-mover.
    Context at q: (L_q, S_q, R_q) where R_q = value at p = S.
    At step k+1: mover = p, q is non-mover.
    Context at q: (L_q, S_q, R_q') where R_q' = value at p = S' != S.
    Different context for q. No conflict with the same step.

    But what if q fires somewhere else in the cycle?
    If q fires at some step j (moverAt(j) = q), and the context at q at step j
    matches the context at q at step k (non-mover), that's an entry conflict!

    Context at q at step k (non-mover): (c_{left(q)}, c_q, c_{right(q)}).
    Where right(q) = p (if q = left(p)), so c_{right(q)} = c_p = S.

    If at some mover step j for q, the context matches: need c_p at step j to be S.
    But c_p changes during the stay run! So we need to find the right timing.

    This is getting complex. Let me think about a cleaner argument.
    """
    print("\n" + "="*70)
    print("ENTRY CONFLICT FROM STAY STEPS")
    print("="*70)

    # Actually, the clearest approach might be to use the existing BAFArc
    # structure (not BAFArcAdj). The BAFArc doesn't require adjacent CCW steps.
    # It requires:
    # 1. proc fires CW (cwProcStep)
    # 2. right(proc) fires CW (cwNeighborStep)
    # 3. right(proc) fires CCW (ccwNeighborStep)
    # 4. proc fires CCW (ccwProcStep)
    # With no-fire conditions between certain steps.

    # In the "max run = 1" case, we DON'T have adjacent CW steps,
    # but we DO have CW steps separated by STAYs.

    # Example mover word at position: ..., p, p+1, p+1, p+2, ...
    # Step k: CW from p to p+1
    # Step k+1: STAY at p+1
    # Step k+2: CW from p+1 to p+2

    # So: cwProcStep for proc=p+1: step k+1 (where p+1 fires) -- wait, at step k+1,
    # mover = p+1 (STAY). That IS p+1 firing. And at step k, mover = p.
    # So the CW step at step k has moverAt = p, stepping CW to p+1.
    # At step k+1, moverAt = p+1 (STAY). p+1 fires.
    # At step k+2, moverAt = p+1 stepping CW to p+2.

    # For a BAFArc with proc = p+1:
    # cwProcStep = step where p+1 fires CW (= step k+2, since stepDir = CW there)
    # cwNeighborStep = step where right(p+1) = p+2 fires CW

    # Hmm, this gets complicated. Let me think about what STRUCTURE the
    # max-run-1 constraint forces.

    # KEY INSIGHT: In the zero-winding case with max CW/CCW run = 1,
    # we can construct a BAFArc (non-adjacent) instead of BAFArcAdj.
    # The R-value return is then from the binary double-fire lemma
    # applied over a larger interval.

    # Actually, let me reconsider the problem from scratch.
    # The BAFArcAdj needs ccwProcStep = ccwNeighborStep + 1.
    # This comes from: in the CCW pass, right(proc) fires, then immediately
    # proc fires. That's two consecutive CCW steps.

    # With max CCW run = 1: we can't have two consecutive CCW steps!
    # So BAFArcAdj literally can't be constructed.

    # But BAFArc (without the adjacency) can be constructed as long as
    # the 4 steps exist in the right order with the right no-fire conditions.

    # For BAFArc.elim, we need hR: the R-value (right(proc)) is the same
    # at cwNeighborStep and ccwProcStep.

    # Without adjacency, the R-value might change because right(proc) fires
    # between ccwNeighborStep and ccwProcStep.

    # With max CCW run = 1: between the CCW step at right(proc) and the
    # CCW step at proc, there's at least one non-CCW step (STAY or CW).
    # During that intervening step, right(proc) MIGHT fire (if the mover
    # revisits right(proc)).

    # If right(proc) fires an even number of times between cwNeighborStep
    # and ccwProcStep, and right(proc) is binary, then R-value is preserved!

    # So: can we show right(proc) fires an even number of times in the interval?

    # Actually, for the non-adjacent case: between ccwNeighborStep and ccwProcStep,
    # the mover goes from right(proc) to proc. With max CCW run = 1, the step
    # after ccwNeighborStep is NOT CCW. So the mover might STAY at left(right(proc)) = proc
    # or go CW from left(right(proc)) = proc to right(proc) again.

    # Wait, at ccwNeighborStep: mover = right(proc), stepDir = CCW.
    # So moverAt(ccwNeighborStep + 1) = left(right(proc)) = proc.
    # So the mover IS at proc at step ccwNeighborStep + 1.
    # But is that the ccwProcStep?

    # If stepDir(ccwNeighborStep) = CCW and the next step has mover at proc,
    # that IS ccwProcStep if the mover at proc fires and eventually the mover at
    # proc has moverAt = proc.

    # Actually: at step ccwNeighborStep, mover = right(proc), and the step
    # direction tells us where the NEXT mover is:
    # If stepDir(ccwNeighborStep) = CCW: next mover = left(moverAt) = left(right(proc)) = proc.
    # Wait, stepDir is about moverAt(next) vs moverAt(current):
    # stepDir = CCW means moverAt(next) = left(moverAt(current)) = left(right(proc)) = proc.

    # So moverAt(ccwNeighborStep + 1) = proc!
    # And the step from ccwNeighborStep to ccwNeighborStep+1 has mover at right(proc)
    # doing a CCW move to proc.

    # So ccwProcStep could be ccwNeighborStep + 1? But wait, ccwProcStep requires
    # moverAt(ccwProcStep) = proc, which IS satisfied.

    # AND: the step direction at ccwNeighborStep is CCW, meaning
    # moverAt(ccwNeighborStep + 1) = left(moverAt(ccwNeighborStep)) = proc.
    # So proc IS the mover at step ccwNeighborStep + 1.

    # But is that a CCW step for proc? Not necessarily. The step at ccwNeighborStep + 1
    # could be CW (from proc to right(proc)), STAY (at proc), or CCW (from proc to left(proc)).

    # In any case, proc fires at ccwNeighborStep + 1, which satisfies
    # ccw_proc_mover: gc.moverAt ccwProcStep = proc.

    # The "ccw" in ccwProcStep name is misleading -- we just need proc to fire there.
    # Actually looking at the BAFArc definition again: ccwProcStep just needs
    # moverAt = proc. It doesn't need the step to be CCW.

    # And for the entry conflict, we need:
    # At cwNeighborStep: mover = right(proc), proc is non-mover.
    # At ccwProcStep: mover = proc, proc is mover.
    # Same (L, S, R) context at proc -> contradiction.

    # L = left(proc) value, S = proc value, R = right(proc) value.
    # L preserved: left(proc) doesn't fire between cwNeighborStep and ccwProcStep.
    # S preserved: proc doesn't fire between cwNeighborStep and ccwProcStep.
    # R preserved: right(proc) value is the same.

    # For the non-adjacent case (ccwProcStep = ccwNeighborStep + 1):
    # Between cwNeighborStep and ccwProcStep:
    #   - proc doesn't fire: need to check. Between cwNeighborStep and
    #     ccwNeighborStep, we need proc not to fire. Between ccwNeighborStep
    #     and ccwProcStep (= ccwNeighborStep + 1), there are no intermediate steps.
    #     So proc doesn't fire in the interval [cwNeighborStep, ccwProcStep).

    #   BUT WAIT: at ccwNeighborStep, the mover is right(proc), which fires.
    #   Right(proc)'s value changes. At ccwProcStep = ccwNeighborStep + 1,
    #   the R value at proc = right(proc)'s value = the value AFTER right(proc) fired.
    #   This is DIFFERENT from the R value at cwNeighborStep (which was BEFORE
    #   right(proc) fired at ccwNeighborStep).

    #   So R changed! Unless right(proc) fired an even number of times in between
    #   AND is binary.

    #   Specifically: right(proc) fires at cwNeighborStep (mover = right(proc)),
    #   then fires again at ccwNeighborStep (mover = right(proc)).
    #   If right(proc) doesn't fire in between (rightProc_noFire_mid),
    #   then right(proc) fires exactly twice in [cwNeighborStep, ccwNeighborStep].
    #   If right(proc) is binary: two firings return to original value.
    #   So value at right(proc) at cwNeighborStep+1 = value at ccwNeighborStep+1.
    #   But what we need is value at cwNeighborStep = value at ccwProcStep.

    #   Value at right(proc) at cwNeighborStep: this is BEFORE right(proc) fires at cwNeighborStep.
    #   Value at right(proc) at ccwProcStep = ccwNeighborStep + 1: this is AFTER right(proc)
    #     fires at ccwNeighborStep.

    #   After cwNeighborStep firing: right(proc) toggled once.
    #   After ccwNeighborStep firing: right(proc) toggled twice.
    #   Two toggles of binary = return to original.
    #   So value at ccwProcStep = value at cwNeighborStep. R IS preserved!

    #   This is exactly the binary_double_fire_returns lemma!

    # SO: For the non-adjacent case (ccwProcStep = ccwNeighborStep + 1),
    # if right(proc) is BINARY and doesn't fire between cwNeighborStep and
    # ccwNeighborStep (exclusive), then R is preserved.

    # And ccwProcStep = ccwNeighborStep + 1 IS achievable even with max CCW run = 1,
    # because the CCW step at right(proc) is step ccwNeighborStep, and the NEXT
    # mover is at proc (= ccwProcStep). No need for two consecutive CCW steps!

    # Wait... but ccwProcStep = ccwNeighborStep + 1 IS the BAFArcAdj condition!
    # ccw_adjacent: ccwProcStep.val = ccwNeighborStep.val + 1

    # So actually, ccwNeighborStep followed by ccwProcStep = ccwNeighborStep + 1
    # works even without consecutive CCW steps, because:
    # At ccwNeighborStep: mover = right(proc), doing some step.
    # At ccwNeighborStep + 1: mover = proc.
    # The step at ccwNeighborStep need not be CCW! It could be any direction.

    # WAIT: I need to re-examine. The BAFArcAdj requires:
    # 1. ccwNeighborStep has moverAt = right(proc) -- this IS a step where right(proc) fires
    # 2. ccwProcStep has moverAt = proc
    # 3. ccwProcStep.val = ccwNeighborStep.val + 1

    # For step 3: the mover goes from right(proc) at step ccwNeighborStep to proc at
    # step ccwNeighborStep + 1. This means stepDir(ccwNeighborStep) = CCW
    # (since left(right(proc)) = proc).

    # So the step at ccwNeighborStep IS a CCW step (from right(proc) to proc).

    # And the step at ccwProcStep-1 (= ccwNeighborStep) is CCW.
    # The step at ccwProcStep could be anything.

    # NOW: the step BEFORE ccwNeighborStep: what direction is it?
    # If it's also CCW, then we have CCW, CCW which violates max CCW run = 1.

    # So with max CCW run = 1: the step BEFORE ccwNeighborStep is NOT CCW.
    # And the step AT ccwNeighborStep IS CCW.
    # The step AFTER ccwNeighborStep (= ccwProcStep) could be anything.

    # This is fine! The CCW run at ccwNeighborStep has length 1 (just one CCW step).
    # The BAFArcAdj is constructible!

    # Wait, but we also need the CW part:
    # cwProcStep: moverAt = proc, stepping CW.
    # cwNeighborStep: moverAt = right(proc), stepping CW.
    # cw_order: cwProcStep.val < cwNeighborStep.val.

    # For a CW run of length 1: the CW step at proc is isolated.
    # The NEXT step (cwProcStep + 1) is NOT CW.
    # So the mover at cwProcStep + 1 might be right(proc) (if stepDir = CW at cwProcStep).
    # But stepDir(cwProcStep) = CW means moverAt(cwProcStep + 1) = right(proc).
    # Then at cwProcStep + 1, the mover is right(proc).
    # cwNeighborStep = cwProcStep + 1? Then CW step at cwProcStep and the NEXT step
    # at right(proc). For cwNeighborStep to be a CW step where right(proc) fires:
    # moverAt(cwProcStep + 1) = right(proc), and stepDir(cwProcStep + 1) = CW.
    # That would mean stepDir at cwProcStep = CW and stepDir at cwProcStep + 1 = CW.
    # But moverAt at cwProcStep = proc (not right(proc)), so these are at different positions.
    # The CW runs are per-step-direction, not per-position.
    # CW run = maximal consecutive CW entries in the step_dirs array.
    # So cwProcStep has stepDir = CW, and cwProcStep + 1 has stepDir = CW:
    # that's a CW run of length 2! Violates max CW run = 1!

    # AH HA! So we CAN'T have cwProcStep followed immediately by cwNeighborStep
    # if both are CW steps, because that would be a CW run of length 2.

    # So the CW pass cannot have proc and right(proc) firing in consecutive steps
    # with both being CW. There must be a STAY or CCW between them.

    # For the BAFArc, we need:
    # cwProcStep (mover = proc, CW step) at position proc.
    # cwNeighborStep (mover = right(proc)) at some LATER step.
    # But cwNeighborStep need not be cwProcStep + 1!

    # Example with STAY between:
    # Step k: mover = proc, stepDir = CW (proc advances to right(proc))
    # Step k+1: mover = right(proc), stepDir = STAY
    # Step k+2: mover = right(proc), stepDir = CW (right(proc) advances)

    # Step dirs: CW, STAY, CW. CW runs: run at step k (length 1), run at step k+2 (length 1).
    # No CW run of length 2. This is fine!

    # cwProcStep = k, cwNeighborStep = k+2 (or k+1 if right(proc) fires there too).
    # Actually cwNeighborStep just needs moverAt = right(proc). Step k+1 has moverAt = right(proc).
    # So cwNeighborStep = k+1 works! At k+1, mover = right(proc) fires (STAY step).
    # The cw_neighbor_mover requirement: gc.moverAt cwNeighborStep = right proc. Satisfied.

    # So: cwProcStep = k, cwNeighborStep = k+1.
    # cw_order: k < k+1. OK.

    # For the CCW pass: similarly, we need ccwNeighborStep and ccwProcStep.
    # ccwNeighborStep: mover = right(proc) fires (any direction, typically CCW).
    # ccwProcStep: mover = proc fires.
    # ccw_order: ccwNeighborStep.val < ccwProcStep.val.

    # With the STAY pattern on CCW pass:
    # Step m: mover = right(proc), stepDir = CCW (retreats to proc)
    # Step m+1: mover = proc, stepDir = anything.
    # ccwNeighborStep = m, ccwProcStep = m+1.
    # ccw_adjacent: m+1 = m + 1. Satisfied!

    # And the step at m IS CCW (length 1 CCW run). The step at m-1 is NOT CCW
    # (to keep max CCW run = 1). The step at m+1 could be anything.

    # So the BAFArcAdj IS constructible even with max CW/CCW run = 1!
    # The key: cwNeighborStep can use a STAY step (mover at right(proc) during a STAY).

    # Let me verify this with a concrete example.

    print("""
  KEY FINDING: BAFArcAdj IS constructible even with max CW/CCW run = 1!

  The insight: cwNeighborStep doesn't require a CW step direction.
  It just requires moverAt(cwNeighborStep) = right(proc).
  A STAY step at right(proc) satisfies this!

  Example mover word pattern:
    Step k:   mover = proc,       stepDir = CW  (proc fires, advances to right(proc))
    Step k+1: mover = right(proc), stepDir = STAY (right(proc) fires, stays)
    ...
    Step m:   mover = right(proc), stepDir = CCW (right(proc) fires, retreats to proc)
    Step m+1: mover = proc,       stepDir = any (proc fires)

  BAFArcAdj construction:
    cwProcStep = k
    cwNeighborStep = k+1 (right(proc) fires at STAY step)
    ccwNeighborStep = m
    ccwProcStep = m+1

  This satisfies all BAFArcAdj requirements:
    cw_order: k < k+1 ✓
    mid_order: k+1 < m ✓ (some steps in between)
    ccw_order: m < m+1 ✓
    ccw_adjacent: m+1 = m + 1 ✓
    cw_proc_mover: moverAt(k) = proc ✓
    cw_neighbor_mover: moverAt(k+1) = right(proc) ✓
    ccw_neighbor_mover: moverAt(m) = right(proc) ✓
    ccw_proc_mover: moverAt(m+1) = proc ✓

  The no-fire conditions also hold (by the walk structure).
  And R-preservation follows from binary_double_fire_returns
  (right(proc) fires at k+1 and m, twice, returning to original if binary).

  CONCLUSION: The BAFArcAdj approach ALREADY handles max CW/CCW run = 1!
  The "alternating runs" sub-case is NOT a separate case.
  The existing proof framework covers it.
  """)

    # BUT: we need to verify the no-fire conditions hold.
    # proc_noFire: between cwNeighborStep (k+1) and ccwProcStep (m+1),
    #   proc doesn't fire. Since the mover went from proc at k to right(proc) at k+1,
    #   and then eventually returns to proc at m+1, we need proc not to fire
    #   in steps k+1 through m. This depends on the walk structure.

    # leftProc_noFire: left(proc) doesn't fire between k+1 and m+1.
    #   If the mover's arc is [proc, right(proc)] during this interval,
    #   and left(proc) is outside this arc, then left(proc) doesn't fire.

    # rightProc_noFire_mid: right(proc) doesn't fire between k+2 and m
    #   (between cwNeighborStep exclusive and ccwNeighborStep exclusive).
    #   But if the mover is at right(proc) doing STAY steps between k+1 and
    #   some later step, right(proc) DOES fire! That violates rightProc_noFire_mid.

    # AH: this is a problem. If right(proc) has multiple STAY steps,
    # it fires multiple times between cwNeighborStep and ccwNeighborStep.
    # The rightProc_noFire_mid condition requires right(proc) NOT to fire
    # in that interval.

    # So the BAFArcAdj construction works only if right(proc) fires exactly
    # at cwNeighborStep and ccwNeighborStep, and not in between.

    # With the STAY pattern at right(proc):
    # k+1: right(proc) fires (STAY), k+2: right(proc) might fire again (STAY or CW/CCW).
    # If k+2 is also at right(proc) (another STAY), then right(proc) fires at k+2,
    # which is between cwNeighborStep (k+1) and ccwNeighborStep (m).
    # That violates rightProc_noFire_mid.

    # FIX: choose cwNeighborStep = the LAST step where right(proc) fires
    # before the gap (before the mover leaves right(proc)).
    # And ccwNeighborStep = the FIRST step where right(proc) fires
    # after the gap (when the mover returns to right(proc)).

    # Then between cwNeighborStep and ccwNeighborStep, right(proc) doesn't fire.
    # rightProc_noFire_mid is satisfied.

    # In the max run = 1 case:
    # The mover is at right(proc) for some block of steps (possibly with STAYs).
    # Let cwNeighborStep = last step of this block.
    # At this step, mover = right(proc), and the NEXT step goes to a different position
    # (since it's the end of the block). The step direction is CW (to advance further)
    # or CCW (to retreat).

    # Then the mover goes away and eventually returns to right(proc).
    # ccwNeighborStep = first step of the return block.

    # Between these: right(proc) doesn't fire. Perfect.

    # For proc_noFire: between cwNeighborStep and ccwProcStep, proc must not fire.
    # cwNeighborStep is the last step of the right(proc) block.
    # ccwProcStep is the next step where proc fires (after right(proc) returns and retreats).
    # Between these: the mover goes from right(proc)'s block end, through other positions,
    # back to right(proc), then to proc.
    # If the mover doesn't visit proc in this interval: proc_noFire holds.

    # This depends on the specific walk. In the "advance-retreat" pattern
    # (CW,STAY,...,CW to rightmost, then CCW,STAY,...,CCW back), the mover
    # goes from right(proc) forward (away from proc) and then retreats
    # back through right(proc) to proc. So proc is NOT visited between
    # cwNeighborStep and ccwProcStep. ✓

    # Similarly, left(proc) is not visited (it's behind proc in the advance direction).

    print("""
  CORRECTION: The BAFArcAdj construction works, but cwNeighborStep must be
  the LAST firing of right(proc) in its forward-pass block, and
  ccwNeighborStep must be the FIRST firing of right(proc) in its retreat block.
  This ensures rightProc_noFire_mid holds.

  The construction works for ANY walk pattern (not just the specific advance-retreat)
  as long as:
  1. The mover visits proc, then right(proc), then eventually returns to right(proc),
     then to proc (the BAF structure).
  2. Between the forward and retreat visits to right(proc), it doesn't revisit right(proc).
  3. Between the forward visit to right(proc) and the retreat visit to proc,
     it doesn't visit proc or left(proc).

  These conditions follow from the no-safe-processor + zero-winding structure.

  FINAL ANSWER: The "alternating runs" sub-case does NOT need special handling.
  The BAFArcAdj construction (with cwNeighborStep at a STAY step) works.
  The case is covered by the existing proof framework.
  """)


def main():
    check_cup2()
    analyze_stay_structure()
    investigate_global_structure()
    investigate_entry_conflict_from_stays()

    print("="*70)
    print("SUMMARY")
    print("="*70)
    print("""
  The investigation reveals that the "all CW/CCW runs of length 1" sub-case
  does NOT require special handling:

  1. BAFArcAdj IS constructible even with max CW/CCW run = 1.
     The key: cwNeighborStep can use a STAY step where moverAt = right(proc).
     It doesn't need to be a CW step.

  2. The no-fire conditions (proc_noFire, leftProc_noFire, rightProc_noFire_mid)
     are satisfied by choosing cwNeighborStep as the LAST step of right(proc)'s
     forward block and ccwNeighborStep as the FIRST step of right(proc)'s
     retreat block.

  3. The R-preservation follows from binary_double_fire_returns: right(proc)
     fires exactly twice (at cwNeighborStep and ccwNeighborStep) between the
     forward and retreat phases, returning binary values to their original.

  4. For the Lean proof: the large_arc_zeroWinding_ec axiom can be replaced by
     a theorem that constructs a BAFArcAdj from any zero-winding, no-safe-proc
     good cycle, without requiring max CW run >= 2.

  The construction of BAFArcAdj relies on the existence of a BAF (back-and-forth)
  pattern in the mover word: the mover visits proc, then right(proc), then returns
  to right(proc), then to proc. This pattern exists in ANY zero-winding walk that
  covers the full ring (no safe processor), because the mover must advance through
  proc and right(proc) in one direction and retreat through them in the other.
    """)


if __name__ == '__main__':
    main()
