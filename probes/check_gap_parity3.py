#!/usr/bin/env python3
"""
check_gap_parity3.py — Why BAFArcAdj fails at turnaround, and what works instead.

At proc=n-2, right(proc)=n-1 (binary), the BAF arc fails because:
- proc CW fires: [n-2, 2n-2+n-2] = [n-2, 3n-4]  (first and third pass)
- proc CCW fires: [n] (second pass)
- right CW fires: [3n-3] (wraps around — actually the LAST step, third CW pass end)
- right CCW fires: [n-1] (turnaround)

For BAFArcAdj we need: cwProcStep < cwNeighborStep < ccwNeighborStep < ccwProcStep
- cwProc = n-2, cwRight = ??, ccwRight = n-1, ccwProc = n

But cwRight must be > cwProc and have direction CW.
right(proc) = n-1 fires CW only at the very end of the cycle (step 3n-3)
which is AFTER the CCW pass. So cwRight > ccwRight = n-1 fails ordering.

The issue: at the turnaround edge, right(proc) does NOT fire CW in the
first pass — it goes CW then immediately CCW. There's no CW fire of
right(proc) between proc's CW fire and proc's CCW fire.

This is exactly the turnaround problem. The BAFArcAdj needs a BACK-AND-FORTH:
CW pass then CCW pass. At the turnaround, the CW pass ENDS at right(proc).

INSIGHT: The BAFArcAdj works at INTERIOR processors (away from the turnaround).
The turnaround edge is the WORST place to look.

For the min-gap at the turnaround edge (gap=1), we can't build a BAFArcAdj.
For interior edges with larger gaps, BAFArcAdj exists but right(proc) is ternary.

NEW QUESTION: What if we build a "reversed" BAF arc?
- CCW proc fires at step n (proc goes CCW)
- CCW right fires at step n-1 (right goes CCW = turnaround)
- CW right fires at step 3n-3 (right goes CW = end of cycle)
- CW proc fires at step 3n-4 (proc goes CW)

Wait, that's also not right for adjacency.

Let me think about this differently. In sub-threshold systems with >= 3 binary,
we need to find SOME processor pair where the entry conflict works.

The CUP-2 cycle is at the threshold (product = 4*3^{n-2}), so it's NOT a
sub-threshold system. For actual sub-threshold systems:
- product < 4*3^{n-2}
- at least 3 binary processors
- some procs have state count >= 4 OR all binary

The proof needs to work for ANY good cycle in ANY sub-threshold system,
not just for the CUP-2 bounce cycle.

Let me focus on what the Lean proof actually needs:
The min-gap argument gives us an edge where right(p) doesn't fire CW or CCW
in the interior. But we need to connect this to BAFArcAdj.

Actually, the min-gap lemma and BAFArcAdj are related but NOT the same thing.
The min-gap gives us constraints on a specific edge crossing pair.
BAFArcAdj gives us a processor-level entry conflict.

The REAL question: how do we USE the min-gap lemma to produce a contradiction?
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system


def find_good_cycle(ms, fs, n):
    start = tuple([0] * n)
    config = start
    cycle_configs = [config]
    cycle_movers = []
    while True:
        priv = []
        for i in range(n):
            L = config[(i-1) % n]; S = config[i]; R = config[(i+1) % n]
            if fs[i](L, S, R) != S:
                priv.append(i)
        assert len(priv) == 1
        mover = priv[0]
        cycle_movers.append(mover)
        lst = list(config)
        L = config[(mover-1) % n]; S = config[mover]; R = config[(mover+1) % n]
        lst[mover] = fs[mover](L, S, R)
        config = tuple(lst)
        if config == start:
            break
        cycle_configs.append(config)
    return cycle_configs, cycle_movers


def analyze_min_gap_structure(n):
    """At the min-gap edge, what structure do we have?

    The min-gap edge in the bounce cycle is the TURNAROUND: (n-2, n-1) with gap=1.

    MinGap.lean proves: at the min-gap crossing (a, b) at edge (p, right(p)):
    - No CW fire of right(p) in (a, b)
    - No CCW fire of right(p) in (a, b) (would be a crossing)
    - So right(p) only stays in (a, b)

    For gap=1: (a, b) = (a, a+1), so there are NO interior steps. right(p) fires
    at steps a+1 through b, which is just step a+1 = b. One fire.

    For gap=3: (a, b) = (a, a+3). Interior steps a+1, a+2. right(p) stays at
    both. At step b = a+3, right(p) fires. Fire count = 3 (one CW at a+1?
    wait no — right(p) stays at a+1 and a+2, fires at a+3 which is b).

    Hmm wait, let me reconsider. The mover at step a is p (CW crossing).
    At step a+1, the mover moves to right(p) (since CW). Now what does
    right(p) do? If it CWs, mover goes to right(right(p)) — but that would
    be a CW crossing of the adjacent edge, which is what MinGap.lean forbids.

    So right(p) can only STAY at a+1. Mover stays at right(p).
    At step a+2, same: right(p) stays. Mover stays at right(p).
    ...
    At step b-1, right(p) stays.
    At step b, right(p) fires CCW. Mover goes from right(p) to p.

    So the mover sequence around the crossing is:
    step a: p (CW) → right(p)
    step a+1: right(p) (stay) → right(p)
    step a+2: right(p) (stay) → right(p)
    ...
    step b-1: right(p) (stay) → right(p)
    step b: right(p) (CCW) → p

    Fire count of right(p) in [a+1, b]: gap = b - a fires.
    ALL are "stay" except the last one which is "CCW".

    But "stay" means mover doesn't move — but does the processor fire?
    YES! The mover fires at every step. The mover IS right(p), and it fires
    (changes its state) but stays at the same position.

    Wait no. "Stay" means stepDir = stay, which means moverAt(k) = moverAt(k+1).
    The mover at step k is right(p). It fires (applies transition function),
    but the result is that it stays at the same position (f(L,S,R) = S? No,
    that would mean it's not privileged).

    Actually, I need to be more careful. In the good cycle, at each step the
    unique privileged processor fires. The "step direction" is determined by
    where the mover moves to. If moverAt(k) = right(p) and stepDir = stay,
    it means moverAt(k+1) = right(p) too.

    But right(p) fires (changes its state) at step k. The privileged condition
    is f(L,S,R) ≠ S. So right(p) fires and changes state.

    The FIRE COUNT of right(p) in [a+1, b] = gap steps. Each step, right(p)
    is the mover and fires. So fire count = gap.

    For binary right(p): value after 'gap' fires.
    If gap is even: value returns to original (even number of toggles).
    If gap is odd: value is toggled.

    For the CUP-2 bounce cycle, all gaps are odd, so binary right(p) always toggles.
    """
    ms, fs = build_system(n)
    cycle_configs, cycle_movers = find_good_cycle(ms, fs, n)
    L = len(cycle_movers)

    print(f"\n{'='*70}")
    print(f"MIN-GAP STRUCTURE for n={n}")
    print(f"{'='*70}")
    print(f"Movers: {cycle_movers}")

    # For the min-gap turnaround crossing at edge (n-2, n-1):
    p = n - 2
    rp = n - 1
    # CW crossing: step where mover = p and next mover = rp (CW)
    cw_step = None
    ccw_step = None
    for k in range(L):
        if cycle_movers[k] == p and cycle_movers[(k+1) % L] == rp:
            if cw_step is None:
                cw_step = k
        if cycle_movers[k] == rp and cycle_movers[(k+1) % L] == p:
            if ccw_step is None and (cw_step is not None) and k > cw_step:
                ccw_step = k

    if cw_step is not None and ccw_step is not None:
        gap = ccw_step - cw_step
        print(f"\nTurnaround edge ({p}, {rp}):")
        print(f"  CW crossing at step {cw_step}, CCW at step {ccw_step}, gap={gap}")

        # Track right(p)'s value through the crossing
        print(f"\n  Value tracking of right(p)={rp} (binary={ms[rp]==2}):")
        for k in range(cw_step, ccw_step + 2):
            if k < L:
                val = cycle_configs[k][rp]
                is_mover = cycle_movers[k] == rp
                print(f"    step {k}: val[{rp}]={val}, mover={cycle_movers[k]}, "
                      f"{'FIRES' if is_mover else ''}")

    # Now think about what the min-gap tells us in general
    print(f"\n{'='*70}")
    print(f"GENERAL ANALYSIS: connecting min-gap to entry conflict")
    print(f"{'='*70}")

    # At the min-gap crossing, between a and b:
    # - right(p) fires 'gap' times (all stays except last CCW)
    # - p fires at step a (CW) and will fire again at some later step
    # - left(p) may or may not fire

    # The BAFArcAdj approach failed at the turnaround because right(p) has no
    # CW fire in the BAF window. But the min-gap approach gives something different:

    # At step a: mover=p, direction=CW. Config[a] has some (L,S,R) at p.
    # At step b+1: mover=p again (returns from right(p) CCW to p).

    # Between a and b+1, p fires exactly at a and b+1 (possibly more if there are
    # intermediate visits to p, but the min-gap structure says no).

    # Actually, between a and b, the mover is at right(p) (stays or CCW at end).
    # At step b, mover=right(p) goes CCW to p.
    # At step b+1... wait, is the mover at p at step b+1?
    # If mover goes from right(p) to p at step b, then at step b+1 the mover is at p.
    # What does p do at step b+1? It could go CW, CCW, or stay.

    # For the bounce cycle: at step n-1 (= turnaround), mover goes from n-1 to n-2 (CCW).
    # At step n, mover is at n-2 and goes CCW to n-3. So p=n-2 fires CCW at step n.

    # Context at p at step a (CW crossing):
    # Mover = p at step a. p is privileged: f(L_a, S_a, R_a) ≠ S_a.
    # p changes to f(L_a, S_a, R_a).

    # Context at p at step b+1 (p fires again):
    # Mover = p. Config[b+1] has some (L', S', R') at p.
    # L' = left(p)'s value at step b+1
    # S' = p's value at step b+1 (what p has BEFORE firing at b+1)
    # R' = right(p)'s value at step b+1

    # What is S' = p's value at step b+1?
    # p fires at step a: S changes. Then p doesn't fire again until b+1.
    # Wait, p fires at step a. Does p fire between a and b+1?
    # The mover at steps a+1 through b is right(p). At step b+1, mover is p.
    # So p doesn't fire at steps a+1 through b. It fires at a and b+1.
    # S' = value after firing at a = f(L_a, S_a, R_a). This is the POST-fire value at a.
    # But config[b+1] records the PRE-fire state at step b+1.
    # Since p doesn't fire between a and b+1, config[b+1][p] = config[a+1][p] = f(L_a, S_a, R_a).

    # So S' = f(L_a, S_a, R_a) ≠ S_a.
    # S' is DIFFERENT from S_a. So the self-value at p has CHANGED.

    # This means p sees DIFFERENT (L,S,R) at steps a and b+1.
    # Not an entry conflict at p.

    # But wait: what if we look at ANOTHER processor?
    # At step a+1: mover = right(p). Config[a+1] has:
    #   left = p's value = f(L_a, S_a, R_a) (post-fire at a)
    #   self = right(p)'s value = R_a (hasn't fired yet at right(p))
    #   right = right(right(p))'s value (unchanged)

    # At step a+1, right(p) fires. What's the context?
    # L = p's value at a+1 = f(L_a, S_a, R_a)
    # S = right(p)'s value at a+1 = R_a
    # R = right(right(p))'s value at a+1

    # Hmm, this is getting complicated. Let me just compute it.

    # For the turnaround gap=1:
    # step a: mover=p fires CW. Config[a].
    # step a+1 = b: mover=right(p) fires CCW. Config[b].
    # step b+1 = a+2: mover=p fires. Config[a+2].

    # Context of right(p) at step b = a+1:
    # L = config[a+1][p], S = config[a+1][rp], R = config[a+1][rp+1]
    # config[a+1] = config after p fires at step a.
    # So config[a+1][p] = f_p(config[a][p-1], config[a][p], config[a][p+1])
    # config[a+1][rp] = config[a][rp] (rp didn't fire at step a)
    # config[a+1][rp+1] = config[a][rp+1] (didn't fire at step a)

    # Let me just compute actual values
    a = cw_step
    b = ccw_step

    print(f"\n  Config details:")
    for k in range(max(0, a-1), min(L, b+3)):
        c = cycle_configs[k]
        m = cycle_movers[k]
        print(f"    step {k}: config={c}, mover={m}")
        if k <= b + 1:
            # Show context at p and right(p)
            ctx_p = (c[(p-1)%n], c[p], c[(p+1)%n])
            ctx_rp = (c[(rp-1)%n], c[rp], c[(rp+1)%n])
            print(f"      context at p={p}: {ctx_p}")
            print(f"      context at rp={rp}: {ctx_rp}")


def analyze_what_needs_proving(n):
    """What does the Lean proof actually need?

    We're trying to close the axiom `large_arc_zeroWinding_ec`.
    This is about zero-winding, no safe processor, CW step count > 0.

    The min-gap approach: find globally minimum gap paired crossing, then
    show right(p) doesn't fire CW in the interior (MinGap.lean done).

    Next step: use this to derive a contradiction.

    The question is: what KIND of contradiction?

    Option A: Entry conflict at some processor.
    Option B: Some other structural impossibility.

    For the entry conflict: we need two steps where the same processor sees
    the same (L, S, R) but is mover at one and non-mover at the other.

    The BAFArcAdj approach identifies such a pair and shows R is preserved
    when right(proc) is binary. This works for INTERIOR processors where
    right(proc) is binary AND the BAFArcAdj can be constructed.

    KEY INSIGHT: In sub-threshold systems with >= 3 binary, the min-gap edge
    might not be the right place to look. The min-gap gives us structural
    info (no CW fire at right(p)), but the entry conflict comes from the
    BAFArcAdj at a DIFFERENT location.

    PLAN: The min-gap lemma establishes that at the globally minimum gap,
    right(p) only stays. This combined with "no safe processor" means the
    mover visits at least n-2 processors (covers the ring within distance 1).
    For the BAFArcAdj, we need a processor j where:
    1. right(j) is binary
    2. The BAF structure exists: CW pass visits j then j+1, CCW pass visits j+1 then j
    3. left(j) doesn't fire between the CW-neighbor and CCW-proc steps

    In a zero-winding cycle with CW steps, there's a CW segment and a CCW segment.
    Any interior processor in the CW+CCW "bounce" automatically has a BAFArcAdj
    (the CW pass visits j, j+1 and the CCW pass visits j+1, j).

    The min-gap ensures the right(p) stays argument at one edge. But for
    BAFArcAdj, we just need the bounce structure at a processor with binary
    right neighbor.

    Actually... maybe the connection is:

    In any zero-winding cycle with CW steps:
    - There exists at least one CW->CCW turnaround at some edge (p, p+1)
    - At the turnaround, mover goes ..., p, p+1, p, ... (CW then CCW)
    - For processor p: this is the BAF arc with cwProcStep, then mover at p+1
      (but p+1 goes CCW immediately, so ccwNeighborStep = cwNeighborStep+1?)

    Hmm, this is getting tangled. Let me focus.
    """
    ms, fs = build_system(n)
    cycle_configs, cycle_movers = find_good_cycle(ms, fs, n)
    L = len(cycle_movers)

    print(f"\n{'='*70}")
    print(f"WHAT NEEDS PROVING for n={n}")
    print(f"{'='*70}")

    # For the zero-winding, no-safe-processor case with CW steps:
    # The mover arc covers the ring (every proc within distance 1 of some mover).
    # There must be CW and CCW segments.
    # At each CW-to-CCW turnaround, there's a paired crossing with gap=1.
    # At each CCW-to-CW turnaround, there's a paired crossing with gap=1.

    # The entry conflict should come from an INTERIOR processor of the bounce.
    # Let's check: for each interior proc j in the bounce, does the BAFArcAdj
    # exist, and is right(j) ever binary?

    # In sub-threshold with >= 3 binary:
    # There exist >= 3 binary processors on the ring.
    # The bounce covers all processors.
    # Among the n-2 interior processors of the bounce, at least one must have
    # a binary right neighbor (pigeonhole: >= 3 binary procs, n-1 edges).

    # Actually, even stronger: if there are k >= 3 binary procs, then there
    # are k edges (j, j+1) where j+1 is binary. Among these, at least k-1
    # have j as an interior processor of the bounce (only the last processor
    # in the CW direction is not interior).

    # Wait, in a bounce word [0, 1, ..., T, T-1, ..., 0, 1, ...], processor T
    # is the turnaround. Every processor 1 through T-1 is interior.
    # For a zero-winding cycle that covers the whole ring, T = n-1 or close.
    # So processors 1 through n-2 are interior. That's n-2 interior procs.
    # Among these, if right(j) is binary for some j in {1,...,n-2}, we're good.
    # right(j) = j+1. So we need j+1 binary for some j in {1,...,n-2},
    # i.e., some binary proc in {2,...,n-1}.
    # With >= 3 binary procs and only n procs total, there's at least one
    # binary in {2,...,n-1} (at most 1 binary could be at position 0, leaving
    # >= 2 binary in {1,...,n-1}, and at most 1 at n-1, so >= 1 in {1,...,n-2},
    # meaning right(j) = j+1 for j in {0,...,n-3} includes a binary).

    # Actually, this isn't quite right because the bounce could start at any
    # processor, not necessarily 0. In a zero-winding cycle, the CW->CCW
    # turnaround could be at any position.

    print(f"\nFor ANY zero-winding good cycle with CW steps in a sub-threshold system:")
    print(f"- There are >= 3 binary processors")
    print(f"- The mover arc covers all processors")
    print(f"- There exists a CW->CCW turnaround at some processor T")
    print(f"- All processors from the CCW->CW turnaround to T are 'interior'")
    print(f"- Among these interior procs, at least one j has right(j) binary")
    print(f"- At that j, a BAFArcAdj exists with right(j) binary")
    print(f"- BAFArcAdj.elim_of_binary_right gives the contradiction")

    # Let me verify: at the CUP-2 bounce, why does BAFArcAdj fail at proc=n-2?
    # Answer: because right(n-2) = n-1 only fires CW at the END of the cycle
    # (step 3n-3), not during the first CW pass. The issue is that n-1 is the
    # turnaround processor.

    # But what about proc=0 with right(0)=1?
    # right(0) = 1 is ternary in CUP-2. Not binary.

    # In a sub-threshold system with >= 3 binary:
    # - Binary procs could be at positions like {0, 1, 2} or {0, 3, 5} etc.
    # - For binary at position b, we need b-1 to be interior of the bounce.
    # - b-1 is interior if b-1 is between the start and turnaround (exclusive).
    # - With the turnaround at T and start at S, interior = {S+1, ..., T-1}.
    # - We need some binary at position in {S+2, ..., T}.

    # For the CUP-2 system, S=0, T=n-1, interior = {1,...,n-2}.
    # Binary procs are {0, n-1}. Neither is in {2,...,n-1} with right being binary
    # (right(0)=1 is ternary, right(n-2)=n-1 is at turnaround).

    # BUT CUP-2 is at the threshold, not sub-threshold! Sub-threshold systems
    # have DIFFERENT state vectors with more binary processors.

    # OK so the real question is: for sub-threshold systems, with >= 3 binary,
    # can we always find an interior proc with binary right neighbor?

    # With >= 3 binary procs on a ring of n procs:
    # - At least 3 procs have m_i = 2.
    # - The bounce covers all procs. Turnaround at some T.
    # - Interior = all procs except start and turnaround (and maybe one more).
    # - With n >= 9 and >= 3 binary, there are at most 2 "edge" procs
    #   (start, turnaround). So >= 1 binary in interior.
    # - If binary proc b is in interior, then right(b-1) = b is binary,
    #   and b-1 is also likely interior (unless b-1 = start or turnaround).
    # - Even if b-1 is the start or turnaround, b is in interior, so
    #   we can try proc = b with right(b) = b+1 (which may or may not be binary).

    # Hmm, the key is: we don't need right(proc) to be binary. We just need
    # the R component to be preserved. For ternary right(proc), if it fires
    # exactly twice (once CW, once CCW) and returns to original value, that works.

    # For ternary: fires twice means value goes v0 -> v1 -> v2. Does v2 = v0?
    # Not in general! The transition function is context-dependent.
    # But: in the BAFArcAdj, between cwNeighborStep and ccwNeighborStep,
    # the processor's neighbors might have changed, so the second fire could
    # give a different result.

    # The data shows: for CUP-2 interior procs (ternary right), R goes from 0 to 2.
    # That's a ternary proc firing twice with values 0 -> ? -> 2 ≠ 0. NOT preserved.

    # So for ternary right(proc), R is NOT preserved. Only binary works.

    # CONCLUSION: We need right(proc) to be BINARY. This requires a binary proc
    # that is right-adjacent to an interior proc of the bounce.

    # In sub-threshold systems with >= 3 binary procs on n >= 9 ring:
    # The bounce has >= 7 interior procs (n-2 >= 7).
    # There are >= 3 binary procs.
    # At most 2 are at the "edges" (start, turnaround).
    # So >= 1 binary in interior.
    # If binary proc b is interior, left(b) = b-1 is also interior (for n >= 9,
    # the interior has >= 7 procs, so a binary in interior has left/right also
    # in interior except possibly at the edge).

    # Wait, I need to be more careful. The binary proc b being interior means
    # b is not the start or turnaround of the bounce. Then proc = b-1 has
    # right(b-1) = b which is binary. Is b-1 interior? It could be the start.
    # But even if b-1 = start, proc = b-1 DOES fire CW (it's the first CW step).
    # The BAFArcAdj at b-1 needs cwProcStep < cwNeighborStep < ccwNeighborStep < ccwProcStep.
    # If b-1 = start = 0 in the bounce [0,1,...,n-1,...,1,0,...]:
    #   cwProcStep = 0 (CW fire of proc=b-1=0)
    #   cwNeighborStep = 1 (CW fire of right=1=b)
    #   ccwNeighborStep = 2n-3 (CCW fire of right=1=b)
    #   ccwProcStep = 2n-2 (CCW fire of proc=0)
    # This ordering 0 < 1 < 2n-3 < 2n-2 works!
    # And left(0) = n-1 doesn't fire between steps 1 and 2n-2.
    # (In the bounce, n-1 fires at steps n-1 and ... but in a zero-winding
    # bounce that starts at 0, n-1 fires at step n-1 (turnaround) which is
    # between 1 and 2n-2.)
    # Hmm, so left(0) = n-1 DOES fire between cwNeighborStep=1 and ccwProcStep=2n-2.
    # That violates leftProc_noFire!

    # But wait — in the CUP-2 data, for proc=1 (with right=2):
    # left=0 fires at steps [0, 8] (for n=5). cwNeighborStep=2, ccwProcStep=7.
    # left=0 fires at step 0 < 2 and step 8 > 7. So left doesn't fire in [2,7).
    # That's why it works for proc=1!

    # For proc=0 with right=1:
    # left=n-1 fires at... in the bounce [0,1,...,n-1,...,1,0,1,...,n-1]:
    # n-1 fires at step n-1 (turnaround) and step 3n-3 (end).
    # cwNeighborStep would be step 1, ccwProcStep would be... when does 0 fire CCW?
    # In the bounce, 0 fires CW at step 0 and CW again at step 2n-2.
    # 0 never fires CCW in the standard CUP-2 bounce!

    # So proc=0 can't form a BAFArcAdj because it never fires CCW.
    # That makes sense: proc 0 is at the other edge of the bounce, always going CW.

    print(f"\n  CUP-2 bounce movers for reference: {cycle_movers}")
    print(f"  P0 fires: {[k for k in range(L) if cycle_movers[k] == 0]}")
    print(f"  P(n-1)={n-1} fires: {[k for k in range(L) if cycle_movers[k] == n-1]}")

    # So the issue with CUP-2: binary procs are at 0 and n-1, both at the
    # "edges" of the bounce (0 never fires CCW, n-1 never fires CW).
    # No binary proc is in the interior.

    # For sub-threshold: we need >= 1 binary in the interior of the bounce.
    # With >= 3 binary and n >= 9, this is guaranteed by pigeonhole:
    # 2 edge positions + >= 3 binary => at least 1 binary in interior.
    # In fact, even if both edges are binary, the third binary must be interior.

    print(f"\n  KEY CONCLUSION:")
    print(f"  In sub-threshold (>= 3 binary, n >= 9), the bounce has 2 edge procs.")
    print(f"  With >= 3 binary procs, at least 1 binary is in the interior.")
    print(f"  For that binary proc b (interior), left(b) is also interior (n >= 9).")
    print(f"  BAFArcAdj at proc=left(b) with right(left(b))=b (binary) works.")
    print(f"  R preservation by binary_double_fire_returns.")
    print(f"  Entry conflict => False. Done!")

    # Wait — we need to verify that left(b) is interior (not at the edges).
    # In a bounce on positions S, S+1, ..., T, T-1, ..., S:
    # Interior = {S+1, ..., T-1}. If b is interior, b-1 could be S.
    # If b-1 = S, then proc = S has right(S) = S+1 = b (binary).
    # Can we build BAFArcAdj at proc = S?
    # S fires CW at step 0 (start of bounce). S fires CW again later.
    # Does S fire CCW? In a zero-winding bounce, S fires CW at the start
    # and CW at the third pass, never CCW. So no BAFArcAdj at S.

    # PROBLEM: if b = S+1 (first interior proc after start), then left(b) = S
    # which can't form BAFArcAdj. And right(S) = b is binary but proc=S
    # can't be used.

    # Can we use proc = b instead? right(b) = b+1 might not be binary.
    # But we could try left(b) = S and use a different construction.

    # Or: use the binary proc b itself as the "observation" processor.
    # At step when b fires CW: b is mover, sees (L, S_b, R).
    # At step when b fires CCW: b is mover, sees (L', S_b', R').
    # S_b' = value of b after CW fire (changed from S_b).
    # So same processor, different context. Not directly an entry conflict.

    # Hmm. Let me think about whether there's ALWAYS an interior binary
    # with an interior left neighbor.

    # In a bounce S, S+1, ..., T (modular), interior = {S+1, ..., T-1}.
    # These are T - S - 1 processors.
    # For zero-winding, T - S = arc length. With no safe processor,
    # arc >= n - 2 (covers all procs within distance 1).
    # Actually, for zero-winding with CW + CCW, the arc from S to T
    # covers T - S + 1 processors. The 1-neighborhood covers all n.
    # So T - S + 1 >= n - 2 (since neighbors add 2 more).
    # Interior = T - S - 1 >= n - 4.
    # For n >= 9: interior >= 5.
    # With >= 3 binary, at most 2 at edges (S and T).
    # So >= 1 binary in interior.
    # If this binary is b, left(b) = b-1 is in interior iff b-1 ≠ S and b-1 ≠ T.
    # b is interior means b ≠ S and b ≠ T.
    # b-1 = S iff b = S+1.
    # So left(b) is interior unless b = S+1.

    # If the only interior binary is at S+1, then:
    # - Binary at S, S+1, and T (or elsewhere on edges)
    # - Wait, we said >= 3 binary. If 2 are at edges (S, T), and 1 at S+1,
    #   that's 3 binary all near the start. left(S+1) = S is at edge.
    # - But right(S) = S+1 is binary, and we need BAFArcAdj at S.
    # - S can't fire CCW (it's the start of the bounce).

    # HOWEVER: we're looking at the wrong direction! We could also try the
    # REVERSED BAF: CCW pass first, then CW pass. Or equivalently, use
    # right(b-1) = b where b-1 is the right neighbor looking from the other side.

    # In fact, BAFArcAdj considers "right" in the ring topology, not in the
    # bounce direction. The "right" is a fixed ring direction.
    # If b is at S+1 and the bounce goes CW from S, then in the ring:
    #   right(S) = S+1 = b.
    #   But also: left(S+2) = S+1 = b.
    #   So proc = S+2 has left(proc) = b (binary), not right.

    # Hmm, BAFArcAdj needs right(proc) to be binary, not left(proc).

    # Alternative: consider the REVERSED problem.
    # If we swap CW and CCW (reverse the ring orientation), left and right swap.
    # A BAFArcAdj in the reversed orientation would need left(proc) to be binary.
    # Since the ring has no preferred orientation, this should be equally valid.

    # So: either right(proc) is binary (standard BAFArcAdj) or
    # left(proc) is binary (reversed BAFArcAdj).

    # With >= 3 binary in interior (for n >= 9, interior >= 5):
    # If there are >= 2 binary in interior, then at least one has both
    # left and right in interior, and at least one of its neighbors is in
    # a position where right(neighbor) or left(neighbor) = binary.

    # With only 1 binary in interior at position S+1:
    # left(S+1) = S (edge). right(S+1) = S+2 (interior).
    # proc = S+2 has left(S+2) = S+1 (binary). Reversed BAF at S+2 works!
    # Or: proc = S has right(S) = S+1 (binary). Can't form standard BAF.

    # So using the reversed BAF: proc = S+2, left(proc) = S+1 = b (binary).
    # A "reversed BAFArcAdj" would have:
    # - ccwProcStep: proc fires CCW
    # - ccwNeighborStep: left(proc) fires CCW (proc is non-mover)
    # - cwNeighborStep: left(proc) fires CW
    # - cwProcStep: proc fires CW
    # With adjacency: cwProcStep = cwNeighborStep + 1
    # And left(proc) fires exactly twice (binary double-fire returns)
    # giving L preservation at proc.

    # This is the "left version" of BAFArcAdj, and gives L preservation
    # instead of R preservation. Combined with S and R preservation
    # (from no-fire arguments), we get full (L,S,R) match.

    # Wait, in the standard BAFArcAdj:
    # L is preserved because left(proc) doesn't fire (leftProc_noFire).
    # S is preserved because proc doesn't fire (proc_noFire).
    # R is preserved because right(proc) fires twice (binary double-fire).

    # In the "left version":
    # R is preserved because right(proc) doesn't fire.
    # S is preserved because proc doesn't fire.
    # L is preserved because left(proc) fires twice (binary double-fire).

    # This is perfectly symmetric! We just need to define a "left BAFArcAdj"
    # where the roles of left and right are swapped.

    print(f"\n  SYMMETRIC APPROACH:")
    print(f"  Define BAFArcAdj_Left (reversed) where:")
    print(f"    - ccwProcStep: proc fires CCW")
    print(f"    - ccwNeighborStep: left(proc) fires CCW")
    print(f"    - cwNeighborStep: left(proc) fires CW")
    print(f"    - cwProcStep: proc fires CW (= cwNeighborStep + 1)")
    print(f"  Then left(proc) fires twice (binary) => L preserved.")
    print(f"  proc doesn't fire between observation steps => S preserved.")
    print(f"  right(proc) doesn't fire between observation steps => R preserved.")

    # OK but actually we should verify: in the reversed BAF, does right(proc)
    # not fire between the observation steps?

    # The observation steps are:
    # - ccwNeighborStep: left(proc) fires CCW (proc is non-mover at this step)
    # - cwProcStep: proc fires CW (proc is mover at this step)

    # Between these: we need right(proc) to not fire.
    # In the bounce, the CCW pass goes ..., proc, left(proc), ...
    # and the CW pass goes ..., left(proc), proc, right(proc), ...
    # Between left(proc)'s CCW fire and proc's CW fire:
    # the mover goes from left(proc) CCW to proc-2, proc-3, ..., S,
    # then S to S+1, ..., proc-1 = left(proc) CW, then proc CW.
    # In this stretch, right(proc) = proc+1 fires at some point during the
    # CW pass (when the mover reaches proc+1).

    # Hmm, that's a problem. right(proc) fires during the CW pass between
    # the observation steps. So R is NOT preserved!

    # Unless we restrict to a sub-arc. Let me reconsider.

    # Standard BAFArcAdj observation steps:
    # cwNeighborStep: right(proc) fires CW
    # ccwProcStep: proc fires CCW (= ccwNeighborStep + 1)
    # Between these: proc doesn't fire, left(proc) doesn't fire, right(proc) doesn't fire.
    # This works because the CCW pass goes right(proc) then proc: one step apart.

    # Reversed BAFArcAdj:
    # ccwNeighborStep: left(proc) fires CCW
    # cwProcStep: proc fires CW (= cwNeighborStep + 1)
    # Between ccwNeighborStep and cwProcStep: there's a LONG stretch
    # (the entire turnaround from CCW to CW). Right(proc) fires during this.

    # So the reversed version does NOT have the "adjacent" property.
    # The adjacency in BAFArcAdj is crucial: the observation steps are
    # just 1 apart, so no processor fires in between.

    # Wait, I'm confusing the adjacent steps. Let me re-read BAFArcAdj.
    # ccwProcStep = ccwNeighborStep + 1 means:
    # step ccwNeighborStep: right(proc) fires CCW (toward proc)
    # step ccwProcStep = ccwNeighborStep + 1: proc fires CCW (continuing CCW)
    # These are ADJACENT steps in the CCW pass.

    # For the left version:
    # cwProcStep = cwNeighborStep + 1 would mean:
    # step cwNeighborStep: left(proc) fires CW (toward proc)
    # step cwProcStep = cwNeighborStep + 1: proc fires CW (continuing CW)
    # These are ADJACENT steps in the CW pass.

    # But the observation steps for the entry conflict would be:
    # At cwNeighborStep: left(proc) fires CW. proc is non-mover.
    #   proc sees (L, S, R) where L = left(proc) pre-fire, S = proc, R = right(proc).
    # At cwProcStep: proc fires CW. proc is mover.
    #   proc sees (L', S', R') where L' = left(proc) post-fire, S' = proc, R' = right(proc).
    # L' ≠ L because left(proc) just fired! The left value CHANGED at the
    # immediately preceding step!

    # So the (L, S, R) at cwNeighborStep and cwProcStep DIFFER at L.
    # Not an entry conflict.

    # This is fundamentally different from the BAFArcAdj case where:
    # At cwNeighborStep: right(proc) fires CW. proc is non-mover.
    #   proc sees (L, S, R) where R is right(proc) PRE-fire.
    # At ccwProcStep: proc fires CCW. proc is mover.
    #   proc sees (L, S, R') where R' might equal R (binary double-fire).
    # L is preserved because left(proc) doesn't fire between these steps.
    # S is preserved because proc doesn't fire.
    # R is preserved if right(proc) is binary (fires twice).

    # For the left version to work, we'd need observation steps where:
    # At step X: left(proc) fires and proc is non-mover.
    # At step Y: proc fires and proc is mover.
    # Between X and Y: proc, right(proc), AND left(proc) don't fire.
    # But left(proc) fires at X, and we need it to also fire at some other step
    # for the binary return. This other fire must be OUTSIDE [X, Y].

    # If left(proc) fires at X and at Z (both CW or whatever), with Z < X:
    # Then binary_double_fire at left(proc) gives value at X = value at Z+1.
    # But this doesn't directly give L at X = L at Y.

    # I think the conclusion is: the "reversed BAF" doesn't work directly.
    # We really need right(proc) to be binary for the standard BAFArcAdj.

    print(f"\n  REVERSED BAF DOESN'T WORK DIRECTLY.")
    print(f"  The L value changes at cwNeighborStep because left(proc) fires.")
    print(f"  Standard BAFArcAdj requires right(proc) binary, period.")


def pigeonhole_analysis():
    """Final analysis: can we always find proc with binary right(proc) in interior?"""
    print(f"\n{'='*70}")
    print(f"PIGEONHOLE: finding proc with binary right(proc) in bounce interior")
    print(f"{'='*70}")

    print("""
In a zero-winding good cycle with CW steps and no safe processor:
- The mover visits a contiguous arc of processors [S, S+1, ..., T] (CW)
  then [T, T-1, ..., S] (CCW). (Could have multiple bounces.)
- "No safe processor" means every proc is within distance 1 of the arc.
  With a single bounce on n >= 9, the arc covers n-2 to n processors.
- Interior processors of the bounce: {S+1, ..., T-1} (at least n-4 >= 5 for n >= 9).

For the BAFArcAdj at interior proc j:
- right(j) = j+1 must be binary
- j must be interior: S < j < T (so j+1 <= T, j+1 is in the arc)
- left(j) = j-1 must NOT fire between cwNeighborStep and ccwProcStep

For the left(j) no-fire condition:
- cwNeighborStep: when j+1 fires CW (mover at j+1 going right)
- ccwProcStep: when j fires CCW (mover at j going left)
- Between: mover goes from j+1 CW to turnaround T, then CCW back to j.
  During this, left(j) = j-1 fires when the mover returns past j-1 on CCW.
  But the CCW pass visits ..., j+1, j. So j-1 fires AFTER j on CCW.
  That means j-1 fires at ccwProcStep + 1 or later, which is AFTER ccwProcStep.
  And j-1 fires on CW at step BEFORE cwNeighborStep (j-1 fires CW before j+1).
  So left(j) doesn't fire in [cwNeighborStep, ccwProcStep). GOOD!

Wait, let me check this more carefully for the CUP-2 data:
For n=5, proc=1, left=0:
  cwNeighborStep = 2, ccwProcStep = 7
  left=0 fires at steps 0 and 8. Neither in [2, 7). Correct!

For n=5, proc=2, left=1:
  cwNeighborStep = 3, ccwProcStep = 6
  left=1 fires at steps 1, 7, 9. None in [3, 6). Correct!

So the no-fire condition holds because:
- On the CW pass: left(j) fires BEFORE j+1 (since left(j) = j-1 < j < j+1).
- On the CCW pass: left(j) fires AFTER j (since the CCW pass goes ..., j, j-1, ...).

This is purely structural from the bounce topology!

CONCLUSION:
For any bounce-type zero-winding good cycle:
1. Any interior proc j has a valid BAFArcAdj structure.
2. If right(j) = j+1 is binary, BAFArcAdj.elim_of_binary_right applies.
3. With >= 3 binary procs and n >= 9, there exists an interior j with binary j+1.
   (At most 2 procs are non-interior: S and T. With >= 3 binary, >= 1 is interior.
    That binary proc b is at some interior position. Then proc = b-1 has right = b binary.
    Is b-1 interior? b-1 >= S (since b > S). b-1 = S only if b = S+1.
    If b = S+1, then left(b-1) = left(S) = S-1 which is outside the bounce.
    Hmm, but b-1 = S IS in the bounce (it's the start). Is S "interior"?
    The BAFArcAdj at S needs cwProcStep (S fires CW), cwNeighborStep (S+1 fires CW),
    ccwNeighborStep (S+1 fires CCW), ccwProcStep (S fires CCW).
    In the bounce [S, ..., T, ..., S, ..., T], S fires CW at the start and CCW at the end.
    So S can form a BAFArcAdj! Let me check:
    cwProcStep = first step (S fires CW)
    cwNeighborStep = second step (S+1 fires CW)
    ccwNeighborStep = last CCW visit to S+1
    ccwProcStep = last CCW visit to S = ccwNeighborStep + 1 (adjacent!)
    And left(S) = S-1 doesn't fire between cwNeighborStep and ccwProcStep?
    left(S) = S-1 is OUTSIDE the bounce (or at the other end of the ring).
    If S-1 is not in the bounce, it never fires. So leftProc_noFire holds trivially!

    So even at proc = S, the BAFArcAdj works (left(S) never fires in the bounce).

    Therefore: for ANY interior binary proc b, proc = b-1 has a valid BAFArcAdj
    with binary right(proc) = b. Even if b-1 = S (start of bounce).)

4. Entry conflict => False.

THE ARGUMENT IS COMPLETE (modulo showing the bounce structure exists for
zero-winding cycles, which comes from the CW+CCW structure).
""")


def main():
    for n in [5, 7, 9]:
        analyze_min_gap_structure(n)

    for n in [5, 9]:
        analyze_what_needs_proving(n)

    pigeonhole_analysis()


if __name__ == '__main__':
    main()
