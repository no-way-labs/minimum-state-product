#!/usr/bin/env python3
"""
check_gap_parity2.py — Deeper analysis of the min-gap structure.

KEY FINDING from check_gap_parity.py: ALL gaps in CUP-2 bounce cycle are ODD.
Pattern: gaps = {1, 1, 3, 3, ..., 2n-3, 2n-3}.

This means the "even gap => binary value preserved => entry conflict" approach
is DEAD for this cycle type.

NEW OBSERVATION: The min-gap claim "right(p) only stays between a and b" is
WRONG for the CUP-2 cycle! Look at edge (0,1) at n=5:
  Movers: 0,1,2,3,4,3,2,1,0,1,2,3,4
  Crossing at step 0 (mover=0, CW) and step 7 (mover=1, CCW).
  Between steps 1-6: movers are 1,2,3,4,3,2 — right(0)=1 fires at steps 1 and...
  wait, the mover at step 1 IS right(0)=1 going CW.

Hmm, but MinGap.lean says "no CW fire at right(p) in (a,b)". Let me check:
this is about the MINIMUM-GAP crossing. The min gap at n=5 is 1 (at turnaround
edges like (3,4)), not 7 (at edge (0,1)).

At the min-gap-1 turnaround edge, the "only stays" claim is vacuous since
there are no interior steps.

So for general sub-threshold cycles (not just CUP-2), the question is:
what is the structure of min-gap crossings?

NEW APPROACH: Instead of gap parity, use the LEFT neighbor.

At the paired crossing of edge (p, right(p)):
- Step a: mover = p, direction CW. Config at step a has some values.
- Step b: mover = right(p), direction CCW.

The BAFArcAdj.elim theorem needs (L, S, R) at proc to match between
cwNeighborStep and ccwProcStep.

CRITICAL REALIZATION: We need to think about this from the BAFArcAdj perspective,
not the raw gap perspective.

In a BAFArcAdj:
- proc is some interior processor j
- cwNeighborStep: right(j) fires CW past j (j is non-mover, sees (L,S,R))
- ccwProcStep: j fires CCW (j is mover, sees (L,S,R))
- We need (L,S,R) to match.

L = left(j): preserved if left(j) doesn't fire between the two steps
S = j: preserved if j doesn't fire between the two steps
R = right(j): preserved if right(j) fires an even number of times (binary) or
              returns to the same value.

In the bounce cycle [0,1,...,n-1,...,1,0,1,...,n-1]:
The BAF arc for interior proc j:
- CW pass: mover goes ..., j, j+1, ...  (j fires at some step, then j+1 fires)
- CCW pass: mover goes ..., j+1, j, ... (j+1 fires, then j fires)

Between "j+1 fires CW" and "j fires CCW":
- j doesn't fire (it's interior, mover goes past j to turnaround and back)
- left(j) = j-1: does j-1 fire? YES, j-1 fires on both the CW and CCW pass.
  But does j-1 fire between cwNeighborStep and ccwProcStep? Need to check.

Let me trace this carefully.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system

def find_good_cycle(ms, fs, n):
    from itertools import product as cartesian
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
        assert len(priv) == 1, f"Expected 1 privileged, got {len(priv)} at {config}"
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


def trace_baf_arc(cycle_configs, cycle_movers, n, ms, fs, proc):
    """Trace the BAF arc for a given interior processor proc.

    Find:
    1. cwProcStep: when proc fires CW
    2. cwNeighborStep: when right(proc) fires CW (proc is non-mover)
    3. ccwNeighborStep: when right(proc) fires CCW
    4. ccwProcStep: when proc fires CCW
    """
    L = len(cycle_movers)
    right_proc = (proc + 1) % n
    left_proc = (proc - 1) % n

    # Find step directions
    dirs = []
    for k in range(L):
        m_curr = cycle_movers[k]
        m_next = cycle_movers[(k+1) % L]
        if m_next == (m_curr + 1) % n:
            dirs.append('cw')
        elif m_next == (m_curr - 1) % n:
            dirs.append('ccw')
        elif m_next == m_curr:
            dirs.append('stay')
        else:
            dirs.append('jump')

    # Find all steps where proc fires, and their directions
    proc_fires = [(k, dirs[k]) for k in range(L) if cycle_movers[k] == proc]
    right_fires = [(k, dirs[k]) for k in range(L) if cycle_movers[k] == right_proc]
    left_fires = [(k, dirs[k]) for k in range(L) if cycle_movers[k] == left_proc]

    print(f"\n  proc={proc}, right={right_proc}, left={left_proc}")
    print(f"  proc fires at: {proc_fires}")
    print(f"  right(proc) fires at: {right_fires}")
    print(f"  left(proc) fires at: {left_fires}")

    # Find BAF arc: CW proc, CW right, CCW right, CCW proc
    # In the bounce cycle, the CW pass has mover going 0,1,...,n-1
    # and the CCW pass has mover going n-1,...,0
    # So for interior proc j:
    #   cwProcStep: first time proc fires with CW dir
    #   cwNeighborStep: first time right(proc) fires with CW dir AFTER cwProcStep
    #   ccwNeighborStep: first time right(proc) fires with CCW dir AFTER cwNeighborStep
    #   ccwProcStep: first time proc fires with CCW dir AFTER ccwNeighborStep

    cw_proc = [k for k, d in proc_fires if d == 'cw']
    ccw_proc = [k for k, d in proc_fires if d == 'ccw']
    cw_right = [k for k, d in right_fires if d == 'cw']
    ccw_right = [k for k, d in right_fires if d == 'ccw']

    if not (cw_proc and ccw_proc and cw_right and ccw_right):
        print(f"  Cannot form BAF arc: missing some direction")
        return

    # Try to find a valid BAF arc
    for cp in cw_proc:
        for cr in cw_right:
            if cr <= cp:
                continue
            for ccr in ccw_right:
                if ccr <= cr:
                    continue
                for ccp in ccw_proc:
                    if ccp <= ccr:
                        continue

                    # Check no-fire conditions
                    # proc doesn't fire between cr and ccp
                    proc_fires_mid = [k for k in range(cr, ccp) if cycle_movers[k] == proc]
                    # left(proc) doesn't fire between cr and ccp
                    left_fires_mid = [k for k in range(cr, ccp) if cycle_movers[k] == left_proc]
                    # right(proc) doesn't fire between cr+1 and ccr-1
                    right_fires_interior = [k for k in range(cr+1, ccr) if cycle_movers[k] == right_proc]

                    # Check adjacency: ccwProcStep = ccwNeighborStep + 1
                    is_adjacent = (ccp == ccr + 1)

                    # Count right(proc) fires between cr and ccp (inclusive)
                    right_fires_count = sum(1 for k in range(cr, ccp+1) if cycle_movers[k] == right_proc)

                    print(f"\n  BAF arc candidate:")
                    print(f"    cwProcStep={cp}, cwNeighborStep={cr}, ccwNeighborStep={ccr}, ccwProcStep={ccp}")
                    print(f"    Adjacent CCW? {is_adjacent} (ccp={ccp}, ccr+1={ccr+1})")
                    print(f"    proc fires in [cr,ccp): {proc_fires_mid}")
                    print(f"    left(proc) fires in [cr,ccp): {left_fires_mid}")
                    print(f"    right(proc) fires in (cr,ccr): {right_fires_interior}")
                    print(f"    right(proc) total fires in [cr,ccp]: {right_fires_count}")

                    if not proc_fires_mid and not right_fires_interior and is_adjacent:
                        print(f"    ==> VALID BAFArcAdj!")

                        # Now check: what happens with R value?
                        # right(proc) fires at cr (CW) and ccr (CCW)
                        # If binary: fires 2 times, value preserved!
                        # If ternary: fires 2 times, may or may not preserve value

                        # Check actual values
                        config_cr = cycle_configs[cr]
                        config_ccp = cycle_configs[ccp]

                        L_cr = config_cr[left_proc]
                        S_cr = config_cr[proc]
                        R_cr = config_cr[right_proc]

                        L_ccp = config_ccp[left_proc]
                        S_ccp = config_ccp[proc]
                        R_ccp = config_ccp[right_proc]

                        print(f"    Context at cwNeighborStep (cr={cr}): L={L_cr}, S={S_cr}, R={R_cr}")
                        print(f"    Context at ccwProcStep (ccp={ccp}): L={L_ccp}, S={S_ccp}, R={R_ccp}")
                        print(f"    L preserved? {L_cr == L_ccp}")
                        print(f"    S preserved? {S_cr == S_ccp}")
                        print(f"    R preserved? {R_cr == R_ccp}")
                        print(f"    right(proc) is binary? {ms[right_proc] == 2}")

                        if left_fires_mid:
                            print(f"    WARNING: left(proc) fires in mid! L may not be preserved.")
                        else:
                            print(f"    left(proc) doesn't fire in mid — L preserved.")

                        if L_cr == L_ccp and S_cr == S_ccp and R_cr == R_ccp:
                            print(f"    ==> FULL CONTEXT MATCH => ENTRY CONFLICT!")
                        elif L_cr == L_ccp and S_cr == S_ccp:
                            print(f"    ==> L,S match but R differs. Need R preservation argument.")

                    # Only show first valid arc
                    if not proc_fires_mid and not right_fires_interior and is_adjacent:
                        return


def analyze_entry_conflict_structure(n):
    """Analyze the entry conflict structure for the CUP-2 bounce cycle."""
    ms, fs = build_system(n)
    cycle_configs, cycle_movers = find_good_cycle(ms, fs, n)
    L = len(cycle_movers)

    print(f"\n{'='*70}")
    print(f"BAF ARC ANALYSIS for n={n}")
    print(f"{'='*70}")
    print(f"ms={ms}, cycle length={L}")
    print(f"Movers: {cycle_movers}")

    # For each interior processor, find BAF arcs
    for proc in range(1, n-1):  # Interior processors
        trace_baf_arc(cycle_configs, cycle_movers, n, ms, fs, proc)


def analyze_general_gap_structure(n):
    """For general sub-threshold cycles (not just CUP-2), what's the gap structure?

    The CUP-2 bounce cycle has a very specific structure:
    movers = [0, 1, ..., n-1, n-2, ..., 1, 0, 1, ..., n-1]

    But the lower bound proof applies to ALL good cycles in ALL sub-threshold systems.
    The question is: in ANY such cycle, does a min-gap edge always have even gap?

    The CUP-2 cycle has all odd gaps, but CUP-2 is AT the threshold (product = 4*3^{n-2}),
    not sub-threshold. Sub-threshold systems have product < 4*3^{n-2}.
    """
    print(f"\n{'='*70}")
    print(f"GENERAL STRUCTURE ANALYSIS for n={n}")
    print(f"{'='*70}")

    # The CUP-2 system has product = 4*3^{n-2} which is the THRESHOLD, not sub-threshold.
    # Sub-threshold means product < 4*3^{n-2}.
    # The lower bound proof shows NO sub-threshold system can have a valid good cycle.
    # The CUP-2 system is the witness for the UPPER bound.

    # So the question is moot for CUP-2 itself — we're analyzing the wrong system!
    # We need to think about what ANY good cycle in a sub-threshold system looks like.

    threshold = 4 * (3 ** (n - 2))
    print(f"Threshold = 4 * 3^{n-2} = {threshold}")
    print(f"CUP-2 product = {threshold} (AT threshold, not sub-threshold)")
    print(f"\nThe lower bound proof applies to systems with product < {threshold}.")
    print(f"The CUP-2 cycle analysis shows the BAF structure but doesn't directly")
    print(f"tell us about sub-threshold cycles.")
    print(f"\nHowever, the BAF arc entry conflict argument is STRUCTURAL:")
    print(f"it doesn't depend on the specific system, only on the mover word structure.")

    # Key structural fact about bounce cycles in sub-threshold:
    # The bounce cycle has length 3n-2 for CUP-2. Sub-threshold cycles
    # could have different structures.

    # The min-gap argument applies to ANY good cycle:
    # 1. Find the min-gap paired crossing
    # 2. At that crossing, right(p) can't fire CW (MinGap.lean)
    # 3. right(p) can't fire CCW (would be another crossing)
    # 4. So right(p) only stays (if there are any interior steps)
    # 5. Fire count of right(p) = gap

    # The parity question: is the gap always odd?
    # For a bounce word: 0,1,...,k,...,1,0,1,...
    # The CW crossing at edge (j, j+1) happens when mover goes from j to j+1
    # The CCW crossing happens when mover goes from j+1 to j
    # The gap between them = distance from CW to CCW in the mover word

    # For the standard bounce: CW cross of (j,j+1) at step j, CCW cross at step 2k-j-1
    # (where k is the turnaround point). Gap = 2k-j-1-j = 2(k-j)-1 = always odd!

    # This is a structural property of bounce cycles: ALL gaps are odd.
    # It comes from the symmetry of the bounce word.

    print(f"\nSTRUCTURAL FACT: In a bounce cycle [0,1,...,k,...,1], the gap at")
    print(f"edge (j, j+1) between CW crossing at step j and CCW crossing at")
    print(f"step (2k-j-1) is 2(k-j)-1, which is ALWAYS ODD.")
    print(f"\nThis means the 'even gap => binary preserved' approach CANNOT work")
    print(f"for bounce-type cycles.")


def explore_alternative_approaches():
    """Explore alternatives when gap is always odd."""
    print(f"\n{'='*70}")
    print("ALTERNATIVE APPROACHES WHEN GAP IS ALWAYS ODD")
    print(f"{'='*70}")

    print("""
Since all gaps in bounce cycles are odd, we need a different argument.

APPROACH 1: Use left(proc) instead of right(proc) in BAFArcAdj.
   The BAFArcAdj checks (L, S, R) at proc between:
   - cwNeighborStep (right(proc) fires CW, proc is non-mover)
   - ccwProcStep (proc fires CCW, proc is mover)

   L = left(proc): preserved if left(proc) doesn't fire between these steps.
   S = proc: preserved if proc doesn't fire between these steps.
   R = right(proc): the problematic one (fires odd times).

   Wait — the BAFArcAdj.elim_of_binary_right specifically handles when
   right(proc) is binary and fires exactly twice (at cwNeighborStep and
   ccwNeighborStep). That gives preservation.

   But if the gap is odd, right(proc) fires odd times, and for binary
   this toggles the value.

APPROACH 2: Value-tracking across the toggle.
   If right(proc) is binary and fires an odd number of times, its value
   TOGGLES. So R_new = 1 - R_old.

   The context at cwNeighborStep is (L, S, R).
   The context at ccwProcStep is (L, S, 1-R).

   These are DIFFERENT contexts. So proc sees (L, S, R) as non-mover
   and (L, S, 1-R) as mover. This is NOT an entry conflict.

   BUT: proc must have a consistent transition function.
   f(L, S, R) = S (non-mover, so unchanged)
   f(L, S, 1-R) ≠ S (mover, must change)

   This is consistent! The function CAN distinguish these contexts.

APPROACH 3: Use the OTHER paired crossing direction.
   Each edge has TWO paired crossings: CW->CCW and CCW->CW.
   If one has gap g, the other has gap L-g (complementary).
   Since L = 3n-2 is odd for the bounce cycle, complementary gap has
   opposite parity. But the roles of p and right(p) swap!

   Hmm, this doesn't immediately help.

APPROACH 4: The min-gap is at the turnaround, gap = 1.
   At the turnaround edge (n-2, n-1): CW at step n-2, CCW at step n-1.
   Gap = 1. right(n-2) = n-1 fires once (odd).

   But gap = 1 means right(p) fires ONCE between a+1 and b (inclusive).
   Actually gap = b - a = 1 means b = a + 1.
   So right(p) fires at step b = a+1. That's just ONE fire.

   For binary: one fire toggles. R changes.
   For ternary: one fire changes value (by some amount).

   In either case, R is NOT preserved.

APPROACH 5: Adjacent BAF — use ccw_adjacent to get R preservation differently.
   In BAFArcAdj, ccwProcStep = ccwNeighborStep + 1.
   So the config at ccwProcStep is obtained from ccwNeighborStep by
   right(proc) firing CCW.

   The R value at ccwProcStep = R value AFTER right(proc) fires at ccwNeighborStep.
   The R value at cwNeighborStep = R value AFTER right(proc) fires at cwNeighborStep.
   Wait, no. cwNeighborStep is when right(proc) fires. The config at cwNeighborStep
   is the config BEFORE right(proc) fires. So R at cwNeighborStep is the pre-fire value.

   After cwNeighborStep, right(proc) has fired once (value changed).
   After ccwNeighborStep, right(proc) has fired once more.

   Between cwNeighborStep and ccwNeighborStep, right(proc) doesn't fire (by rightProc_noFire_mid).
   So total fires of right(proc) from cwNeighborStep to ccwNeighborStep = 0 interior +
   1 at ccwNeighborStep = 1. But wait, the config at cwNeighborStep already includes
   right(proc) having fired? NO.

   Let me re-read the BAF structure more carefully.

   configs[k] is the config BEFORE step k fires.
   At step cwNeighborStep: mover = right(proc).
   Config at cwNeighborStep has right(proc) BEFORE it fires.
   At step ccwProcStep: mover = proc.
   Config at ccwProcStep has right(proc) at some value.

   Between cwNeighborStep and ccwNeighborStep (exclusive), right(proc) doesn't fire.
   So right(proc)'s value is the same from cwNeighborStep+1 to ccwNeighborStep.

   But from cwNeighborStep to cwNeighborStep+1, right(proc) fires once (it's the mover).
   From ccwNeighborStep to ccwNeighborStep+1 = ccwProcStep, right(proc) fires once.

   So right(proc) at ccwProcStep = right(proc) AFTER firing at ccwNeighborStep
   = right(proc) at cwNeighborStep+1 AFTER one more fire

   Hmm, let me think about this with concrete values.

   Config[cwNeighborStep]: right(proc) = v0 (pre-fire)
   Config[cwNeighborStep+1]: right(proc) = f(v0's context) ≠ v0 (post-fire)
   Config[ccwNeighborStep]: right(proc) = f(v0's context) (same, no fire in between)
   Config[ccwNeighborStep+1] = Config[ccwProcStep]: right(proc) = f(post-fire context)

   For binary: if right(proc) fires exactly twice (once at cwNeighborStep, once at
   ccwNeighborStep), and doesn't fire in between, then:
   Config[cwNeighborStep].right = v0
   Config[cwNeighborStep+1].right = 1-v0 (toggled)
   Config[ccwNeighborStep].right = 1-v0 (unchanged)
   Config[ccwProcStep].right = v0 (toggled back!)

   Wait, this IS the binary_double_fire_returns argument!
   It says: firing twice returns to original value.

   So Config[cwNeighborStep].right(proc) = Config[ccwProcStep].right(proc)
   because right(proc) fires exactly at cwNeighborStep and ccwNeighborStep,
   not in between, and binary double-fire returns.

   THIS IS EXACTLY WHAT BAFArcAdj.elim_of_binary_right proves!

   The gap (b-a at the edge crossing level) is IRRELEVANT here!
   What matters is: does right(proc) fire exactly twice between
   cwNeighborStep and ccwProcStep (inclusive of endpoints)?

   In the BAFArcAdj structure:
   - right(proc) fires at cwNeighborStep (by definition)
   - right(proc) fires at ccwNeighborStep (by definition)
   - right(proc) doesn't fire in between (rightProc_noFire_mid)
   - ccwProcStep = ccwNeighborStep + 1 (adjacency)

   So right(proc) fires exactly twice in [cwNeighborStep, ccwProcStep).
   Binary double-fire returns: Config[cwNeighborStep].right = Config[ccwProcStep].right.

   THIS WORKS REGARDLESS OF THE GAP AT THE EDGE CROSSING LEVEL!

   The "gap" at the edge crossing is NOT the same as the number of times
   right(proc) fires in the BAF arc. The BAF arc is about the PROCESSOR-LEVEL
   structure, not the EDGE-LEVEL structure.

OK SO THE KEY QUESTION IS: Can we always construct a BAFArcAdj where
right(proc) is binary?

In CUP-2: ms = (2, 3, ..., 3, 2).
Binary processors: P_0 and P_{n-1}.
For proc = 1: right(proc) = 2 (ternary). Not binary.
For proc = n-2: right(proc) = n-1 (binary!). Binary!

So we should look at proc = n-2 in CUP-2.
right(n-2) = n-1 which is binary.

But in the sub-threshold case, we have >= 3 binary processors.
So there are at least 3 binary procs. Can we always find an interior proc j
such that right(j) is binary?
right(j) is binary means j+1 is binary. So j is the LEFT neighbor of a binary proc.
If there are >= 3 binary procs, and they can't all be at the same position,
at least one binary proc b has a left neighbor j = b-1. If j is not binary,
then j is interior with right(j) = b binary.

But what if j IS binary? Then we need j to have a non-trivial BAF arc.
If both j and j+1 are binary, the BAF arc at j has right(proc)=j+1 binary.
This works!

The real question: can we always CONSTRUCT the BAFArcAdj?
""")


def check_baf_construction(n):
    """Check if BAFArcAdj can be constructed at proc=n-2 in CUP-2."""
    ms, fs = build_system(n)
    cycle_configs, cycle_movers = find_good_cycle(ms, fs, n)
    L = len(cycle_movers)

    proc = n - 2
    right_proc = n - 1
    left_proc = n - 3

    print(f"\n{'='*70}")
    print(f"BAF CONSTRUCTION CHECK at proc={proc}, n={n}")
    print(f"right(proc)={right_proc} (binary={ms[right_proc]==2})")
    print(f"{'='*70}")
    print(f"Movers: {cycle_movers}")

    # Find fires
    proc_fires = [k for k in range(L) if cycle_movers[k] == proc]
    right_fires = [k for k in range(L) if cycle_movers[k] == right_proc]
    left_fires = [k for k in range(L) if cycle_movers[k] == left_proc]

    print(f"proc={proc} fires at: {proc_fires}")
    print(f"right(proc)={right_proc} fires at: {right_fires}")
    print(f"left(proc)={left_proc} fires at: {left_fires}")

    # Step directions
    dirs = []
    for k in range(L):
        m_curr = cycle_movers[k]
        m_next = cycle_movers[(k+1) % L]
        if m_next == (m_curr + 1) % n:
            dirs.append('cw')
        elif m_next == (m_curr - 1) % n:
            dirs.append('ccw')
        elif m_next == m_curr:
            dirs.append('stay')
        else:
            dirs.append('jump')

    # Find CW and CCW fires
    cw_proc = [k for k in proc_fires if dirs[k] == 'cw']
    ccw_proc = [k for k in proc_fires if dirs[k] == 'ccw']
    cw_right = [k for k in right_fires if dirs[k] == 'cw']
    ccw_right = [k for k in right_fires if dirs[k] == 'ccw']

    print(f"\nproc CW fires: {cw_proc}")
    print(f"proc CCW fires: {ccw_proc}")
    print(f"right CW fires: {cw_right}")
    print(f"right CCW fires: {ccw_right}")

    # Try to find BAFArcAdj
    found = False
    for cp in cw_proc:
        for cr in cw_right:
            if cr <= cp:
                continue
            for ccr in ccw_right:
                if ccr <= cr:
                    continue
                # Check adjacency: ccwProcStep should be ccr + 1
                ccp = ccr + 1
                if ccp >= L:
                    ccp = ccp % L

                # Check ccp is a proc CCW fire
                if cycle_movers[ccp] != proc:
                    continue
                if dirs[ccp] != 'ccw':
                    continue

                # Check no-fire conditions
                proc_fires_mid = any(cycle_movers[k] == proc for k in range(cr, ccp))
                left_fires_mid = any(cycle_movers[k] == left_proc for k in range(cr, ccp))
                right_fires_interior = any(cycle_movers[k] == right_proc for k in range(cr+1, ccr))

                print(f"\nCandidate: cwProc={cp}, cwRight={cr}, ccwRight={ccr}, ccwProc={ccp}")
                print(f"  proc fires in [cr,ccp)? {proc_fires_mid}")
                print(f"  left fires in [cr,ccp)? {left_fires_mid}")
                print(f"  right fires in (cr,ccr)? {right_fires_interior}")

                if not proc_fires_mid and not right_fires_interior:
                    print(f"  ==> VALID BAFArcAdj (modulo left fires)!")

                    config_cr = cycle_configs[cr]
                    config_ccp = cycle_configs[ccp]

                    R_cr = config_cr[right_proc]
                    R_ccp = config_ccp[right_proc]
                    L_cr = config_cr[left_proc]
                    L_ccp = config_ccp[left_proc]
                    S_cr = config_cr[proc]
                    S_ccp = config_ccp[proc]

                    print(f"  Context at cr: L={L_cr}, S={S_cr}, R={R_cr}")
                    print(f"  Context at ccp: L={L_ccp}, S={S_ccp}, R={R_ccp}")
                    print(f"  L match: {L_cr == L_ccp}")
                    print(f"  S match: {S_cr == S_ccp}")
                    print(f"  R match: {R_cr == R_ccp}")

                    if left_fires_mid:
                        print(f"  WARNING: left fires in mid — BAFArcAdj.leftProc_noFire violated!")
                        print(f"  left fires in mid at steps: {[k for k in range(cr, ccp) if cycle_movers[k] == left_proc]}")

                    found = True
                    break
            if found:
                break
        if found:
            break

    if not found:
        print(f"\nNO valid BAFArcAdj found at proc={proc}")
        print("Need to investigate why.")


def main():
    # First, understand the BAF arc structure
    for n in [5, 6, 7, 8, 9]:
        analyze_entry_conflict_structure(n)

    # Check the key structural question
    analyze_general_gap_structure(5)

    # Explore alternatives
    explore_alternative_approaches()

    # Check BAF construction at the right place
    for n in [5, 6, 7, 8, 9]:
        check_baf_construction(n)


if __name__ == '__main__':
    main()
