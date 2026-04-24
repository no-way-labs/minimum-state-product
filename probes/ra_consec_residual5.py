#!/usr/bin/env python3
"""
Refine the cross-phase EC proof.

The prediction "T1 appears as non-mover in phase 1" failed in some cases.
The issue: we predicted WHERE the non-mover appears, but EC still holds —
just via a different triple. Let me trace what actually happens.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from collections import Counter, defaultdict
import random


def trace_failures():
    """Find cases where the predicted EC triple fails, and see what actually happens."""
    print("=" * 70)
    print("TRACE: When predicted EC triple fails")
    print("=" * 70)

    random.seed(42)
    ms = (2, 2, 2, 3, 3, 3, 3, 3, 3)
    n = 9

    from ra_consec_residual2 import analyze_phases_at_proc

    found = 0
    for trial in range(100000):
        fires = []
        for p in range(n):
            fires.extend([p] * ms[p])
        random.shuffle(fires)
        mw = fires
        fc = Counter(mw)
        ok = all(fc.get(p, 0) % ms[p] == 0 and fc.get(p, 0) >= ms[p] for p in range(n))
        if not ok: continue
        if fc[1] != 2: continue

        config = [0] * n
        cycle = [tuple(config)]
        for step in range(len(mw)):
            p = mw[step]
            config = list(cycle[-1])
            if ms[p] == 2:
                config[p] = 1 - config[p]
            else:
                config[p] = (config[p] + 1) % ms[p]
            cycle.append(tuple(config))
        if cycle[-1] != cycle[0]: continue
        cycle = cycle[:-1]
        if len(set(cycle)) != len(cycle): continue

        phases = analyze_phases_at_proc(mw, 1, 0, 2)
        residual = [p for p in phases if p['isolated'] and p['odd_parity'] and p['J+K'] == 1]
        if not residual: continue

        L = len(mw)
        rp = residual[0]
        s1 = rp['s1']
        s2 = rp['s2']
        J = rp['J']
        K = rp['K']

        T1 = (cycle[s1][0], cycle[s1][1], cycle[s1][2])
        T2 = (cycle[s2][0], cycle[s2][1], cycle[s2][2])

        if J % 2 == 1 and K % 2 == 0:
            predicted = T1
        elif J % 2 == 0 and K % 2 == 1:
            predicted = T2
        else:
            continue

        # Check if predicted triple appears as non-mover
        found_as_nonmover = False
        for k in range(L):
            if mw[k] != 1:
                c = cycle[k]
                if (c[0], c[1], c[2]) == predicted:
                    found_as_nonmover = True
                    break

        if found_as_nonmover:
            continue  # Prediction correct, skip

        found += 1
        if found > 5:
            break

        # Prediction failed! Trace what actually happens.
        print(f"\nTrial {trial}: prediction fails")
        print(f"  T1 = {T1} (mover at s1={s1})")
        print(f"  T2 = {T2} (mover at s2={s2})")
        print(f"  J={J}, K={K}")
        print(f"  Predicted EC triple: {predicted}")

        # Show all triples at proc 1
        mover_triples = set()
        nonmover_triples = set()
        for k in range(L):
            c = cycle[k]
            triple = (c[0], c[1], c[2])
            if mw[k] == 1:
                mover_triples.add(triple)
            else:
                nonmover_triples.add(triple)

        overlap = mover_triples & nonmover_triples
        print(f"  Mover triples: {sorted(mover_triples)}")
        print(f"  Non-mover triples: {sorted(nonmover_triples)}")
        print(f"  Actual EC overlap: {sorted(overlap)}")

        # The issue: ternary procs change the context at proc 1's neighbors.
        # The proof assumed that between left's fires, left stays constant.
        # But left IS a binary proc (proc 0), and it's also a neighbor of other procs.
        # Other procs' fires DON'T change left's value — only left's own fires do.
        # So left's value only changes when left fires.

        # Wait — that's correct. Left's value at proc 0 only changes when proc 0 fires.
        # Between proc 0's fires, its value is constant.
        # So during phase 1 (s2→s1), left fires J'=1 time, right fires K'=2 times.
        # The trajectory of (left, right) at proc 1 is:
        # Start: (1-L1, R1) [from T2 analysis: L2=1-L1, R2=R1]
        # After left fires: (L1, R1)
        # After right fires: (L1, 1-R1) then (L1, R1)
        # But the ORDER matters! Left and right fire at specific steps.

        # Let me trace exactly
        print(f"\n  Phase 1 (s2={s2} → s1={s1}):")
        k = (s2 + 1) % L
        left_val = cycle[s2][0]  # After s2 fires: left is unchanged
        # Wait: at step s2, proc 1 fires. This doesn't change proc 0's value.
        # After step s2: config has proc 1 toggled.
        # The triple at proc 1 at step s2+1 is:
        # (cycle[s2+1][0], cycle[s2+1][1], cycle[s2+1][2])
        # But cycle[s2+1] depends on what fires at step s2 (proc 1).
        # Actually cycle[k] is the config BEFORE step k.
        # After step k, the config is cycle[(k+1)%L].

        # Let me just print the triples
        cur = s2
        while True:
            cur = (cur + 1) % L
            if cur == s1:
                break
            c = cycle[cur]
            triple = (c[0], c[1], c[2])
            role = "MOVER" if mw[cur] == 1 else f"non-mover (m={mw[cur]})"
            match = " <-- MATCHES T1!" if triple == T1 else ""
            match2 = " <-- MATCHES T2!" if triple == T2 else ""
            print(f"    step {cur:2d}: {triple} {role}{match}{match2}")

        # The issue might be that the non-mover triple matching T1 occurs at a step
        # where the left and right values are not what we predicted because
        # the ternary procs' fires happen between left/right fires and change
        # the config at ternary positions — but that doesn't affect proc 0 or proc 2!

        # Actually: the triple at proc 1 is (c[0], c[1], c[2]).
        # c[0] = proc 0's value (binary, only changes when proc 0 fires)
        # c[1] = proc 1's value (only changes when proc 1 fires, which is at s1 and s2 only)
        # c[2] = proc 2's value (binary, only changes when proc 2 fires)

        # So the triple at proc 1 only changes when proc 0, 1, or 2 fires!
        # Ternary proc fires don't affect this triple at all!

        # Wait — proc 1's value does change when proc 1 fires. And in phase 1,
        # proc 1 doesn't fire (it's between s2 and s1). So c[1] is constant in phase 1.
        # After s2 fires: c[1] toggles from the s2 value (which was 1-v) to v.
        # So c[1] = v throughout phase 1.

        # c[0] changes only when proc 0 fires (J'=1 time in phase 1).
        # c[2] changes only when proc 2 fires (K'=2 times in phase 1).

        # Starting values at step s2+1:
        # c[0] at s2+1: same as c[0] at s2 (proc 1 fired, not proc 0)
        c0_start = cycle[(s2+1)%L][0]
        c1_val = cycle[(s2+1)%L][1]
        c2_start = cycle[(s2+1)%L][2]

        print(f"\n  Phase 1 starts with: c[0]={c0_start}, c[1]={c1_val}, c[2]={c2_start}")
        print(f"  T1 = ({T1[0]}, {T1[1]}, {T1[2]})")

        # For T1 to appear: need c[0]=T1[0], c[1]=T1[1]=v (should be true), c[2]=T1[2]
        # c[0] starts at c0_start = cycle[s2][0] (= 1-L1 if J=1,K=0 in residual)
        # After proc 0 fires: c[0] = 1-c0_start = L1
        # c[2] starts at c2_start = cycle[s2][2] (= R1 if K=0 in residual)
        # After proc 2 fires first time: c[2] = 1-c2_start = 1-R1
        # After proc 2 fires second time: c[2] = c2_start = R1

        # T1 = (L1, v, R1)
        # Need c[0]=L1: happens AFTER proc 0 fires
        # Need c[2]=R1: happens at start and after 2nd proc-2 fire
        # So T1 = (L1, v, R1) appears when c[0]=L1 AND c[2]=R1.
        # This happens if proc 0 fires BEFORE both proc-2 fires, OR after both.

        print(f"  Need c[0]={T1[0]} AND c[2]={T1[2]}")
        print(f"  c[0] starts at {c0_start}, becomes {1-c0_start} after proc 0 fires")
        print(f"  c[2] starts at {c2_start}, toggles with each proc 2 fire")

        if T1[0] == c0_start:
            print(f"  T1[0]=c0_start: need c[0] BEFORE proc 0 fires")
        else:
            print(f"  T1[0]!=c0_start: need c[0] AFTER proc 0 fires")

        if T1[2] == c2_start:
            print(f"  T1[2]=c2_start: need c[2] at start or after 2 fires")
        else:
            print(f"  T1[2]!=c2_start: need c[2] after 1 fire only")


def analyze_ordering_issue():
    """
    The cross-phase proof assumes T1 appears in phase 1 — but the timing matters.
    If proc 0 fires BETWEEN proc 2's two fires, the triple (L1, v, R1) might
    never appear simultaneously.

    Example: phase 1 has J'=1 (proc 0 fires once), K'=2 (proc 2 fires twice).
    Order of fires matters:
    Case A: 0, 2, 2 → (c0_start,c2_start) → (1-c0_start,c2_start) → (1-c0_start,1-c2_start) → (1-c0_start,c2_start)
    Case B: 2, 0, 2 → (c0_start,c2_start) → (c0_start,1-c2_start) → (1-c0_start,1-c2_start) → (1-c0_start,c2_start)
    Case C: 2, 2, 0 → (c0_start,c2_start) → (c0_start,1-c2_start) → (c0_start,c2_start) → (1-c0_start,c2_start)

    For T1 = (L1, v, R1):
    We need (c0, c2) = (L1, R1) at some non-mover step.
    c0_start = 1-L1 (from residual phase with J=1).
    c2_start = R1 (from residual phase with K=0).

    Case A: (1-L1, R1) → (L1, R1) ← HERE! → (L1, 1-R1) → (L1, R1) ← HERE!
    Case B: (1-L1, R1) → (1-L1, 1-R1) → (L1, 1-R1) → (L1, R1) ← HERE!
    Case C: (1-L1, R1) → (1-L1, 1-R1) → (1-L1, R1) → (L1, R1) ← HERE!

    In ALL cases, (L1, R1) appears at the end! Because:
    After all fires: c0 = 1-L1 ⊕ 1 = L1, c2 = R1 ⊕ 0 = R1 (K'=2, even).
    The LAST state before s1 always has (L1, R1).

    But wait — we need this at a NON-MOVER step. The step right before s1 is
    the last step of phase 1. If proc 1 fires at s1, then step s1-1 (or
    the step before s1 cyclically) is a non-mover step for proc 1.
    At that step, (c0, c2) may or may not be (L1, R1).
    Actually: at step s1, the config is cycle[s1]. This IS the mover triple T1.
    The step BEFORE s1 (step s1-1 mod L) has some config.

    Hmm, let me reconsider. The issue is that (L1, R1) appears at some point,
    but it might be at a step where proc 0 or proc 2 is firing — not at a
    non-mover step for proc 1.

    But proc 0 and proc 2 are NOT proc 1. So if (L1, v, R1) appears at a step
    where proc 0 fires, proc 1 is still a non-mover. The triple at proc 1
    is (c0, c1, c2) = (L1, v, R1), and proc 1 is non-mover. That's EC with
    the mover at s1!

    Wait — when proc 0 fires at some step k in phase 1: c0 changes AFTER step k.
    At step k, the config is cycle[k]. The triple at proc 1 at step k is
    (cycle[k][0], cycle[k][1], cycle[k][2]).
    After proc 0 fires: config becomes cycle[k+1] with c0 toggled.

    So at step k (proc 0 fires): the triple at proc 1 is the BEFORE-fire value.
    At step k+1: the triple has c0 toggled.

    The question is: at what step does (c0, c2) first hit (L1, R1)?

    Let me trace case by case:
    """
    print("\n" + "=" * 70)
    print("ORDERING ANALYSIS: When does T1 appear in phase 1?")
    print("=" * 70)

    # In all cases, we showed (L1, R1) appears at the end of phase 1.
    # The step right before s1 has config cycle[s1-1 mod L].
    # That config has c0 = L1 (after J'=1 fires of proc 0, starting from 1-L1)
    # and c2 = R1 (after K'=2 fires of proc 2, starting from R1).
    # And c1 = v (unchanged in phase 1).
    # So cycle[s1-1 mod L] or at least cycle[s1] has (L1, v, R1).

    # cycle[s1] IS T1 by definition! And T1 is a mover triple.
    # But what about the step just before s1?
    # If at step s1-1, no more neighbor fires happen between the last fire and s1,
    # then (c0, c2) has reached their final values.
    # In particular, the LAST step of phase 1 (step s1-1) always has (L1, v, R1)
    # if all neighbor fires have completed.

    # Actually: the step s1-1 has cycle[s1-1]. The config at step s1 is cycle[s1].
    # cycle[s1] is the config BEFORE proc 1 fires at s1.
    # Between steps s1-1 and s1: one step. At step s1-1, some proc fires (not proc 1,
    # since isolated). After firing, config becomes cycle[s1].
    # If the proc firing at s1-1 is not proc 0 or 2: c0, c2 unchanged.
    # So cycle[s1] has (c0, c1, c2) where c0 and c2 reflect all fires up to s1.

    # But cycle[s1] IS the config before the s1 mover. And we said this is T1 = (L1, v, R1).
    # So the config at step s1 already has (L1, v, R1).
    # At step s1-1: depends on what fires at s1-1.
    # If mw[s1-1] ∉ {0, 2}: cycle[s1-1] also has c0=L1, c2=R1, c1=v → same triple!
    # If mw[s1-1] = 0: cycle[s1-1] has c0=1-L1 (before proc 0 fires), then fires→c0=L1.
    #   So at step s1-1: triple is (1-L1, v, R1) ≠ T1.
    # If mw[s1-1] = 2: similar, triple is (L1, v, 1-R1) ≠ T1.

    # So if the LAST fire in phase 1 is proc 0 or 2, T1 doesn't appear at s1-1.
    # But T1 appears at s1 (mover). We need T1 as NON-mover somewhere.

    # The key insight I was missing: we need to find a step where the triple
    # AT proc 1 equals T1 AND proc 1 is not the mover.

    # In phase 1: at every step k in (s2, s1), proc 1 is not the mover.
    # So ANY step in phase 1 where the triple equals T1 gives EC.

    # From the (c0, c2) trajectory analysis:
    # Case A (fires: 0, 2, 2): (1-L1,R1)→(L1,R1)→(L1,1-R1)→(L1,R1)
    # At step after 0 fires: (L1, R1) → triple = (L1, v, R1) = T1. EC!

    # Case B (fires: 2, 0, 2): (1-L1,R1)→(1-L1,1-R1)→(L1,1-R1)→(L1,R1)
    # After all 3 fires: (L1, R1). But this is the last state, which corresponds
    # to step s1 (where proc 1 fires). The step right before s1 had the 3rd fire (proc 2).
    # At that step: (L1, 1-R1) before proc 2 fires. After: (L1, R1) at s1.
    # So at the step of proc 2's 2nd fire: triple is (L1, 1-R1, ...) at proc 1,
    # i.e., (L1, v, 1-R1) ≠ T1.
    # What about earlier steps?
    # After 0 fires (step 2): (L1, 1-R1) → triple (L1, v, 1-R1) ≠ T1.
    # Before any fires: (1-L1, R1) → triple (1-L1, v, R1) ≠ T1.

    # So in Case B: T1 NEVER appears as non-mover in phase 1!

    # But EC still holds 100%. Where does it come from?
    # T2 = (1-L1, 1-v, R1) [from mover at s2].
    # Non-mover triples in phase 1 include: (1-L1, v, R1) — this is NOT T2.
    # Hmm. Let me check what the actual EC is.

    print("""
Key finding: In Case B (proc 2 fires, then proc 0, then proc 2 again):
T1 = (L1, v, R1) does NOT appear as non-mover in phase 1.

But let's check: what non-mover triples DO appear?
Phase 1 non-mover triples at proc 1 (between s2 and s1, c1=v throughout):
  (1-L1, v, R1) — before any fire
  (1-L1, v, 1-R1) — after 1st proc-2 fire
  (L1, v, 1-R1) — after proc-0 fire
  (L1, v, R1) — after 2nd proc-2 fire = T1... but this is at step s1!

Wait: the state (L1, v, R1) after all fires IS the state at step s1.
Step s1 is the mover step. So (L1, v, R1) appears at s1 as mover.

But between the last fire and s1, there might be non-fire steps!
In a minimum-length cycle (24 for our ms), EVERY step has a fire.
So step s1-1 fires someone, step s1 fires proc 1.
If step s1-1 fires proc 2 (the 2nd fire): at step s1-1, the triple is
(L1, v, 1-R1) [before proc 2 fires]. After proc 2 fires → (L1, v, R1) at s1.

So the non-mover triple (L1, v, 1-R1) appears at step s1-1.
But T1 = (L1, v, R1) only appears at s1 (mover step).

HOWEVER: other steps in phase 0 (the residual phase, s1→s2) may have this triple.
Phase 0 non-mover triples include some triples too.

Let me think differently. The argument should consider ALL triples across
the ENTIRE cycle, not just one phase.
""")

    # The correct general argument:
    # With fc(mid) = 2, proc 1 fires at s1 (self=v) and s2 (self=1-v).
    # Mover triples: T1 = (L1, v, R1), T2 = (L2, 1-v, R2).
    # Forced non-mover: (L1, 1-v, R1) at step s1+1, (L2, v, R2) at step s2+1.

    # For non-EC: neither T1 nor T2 appears as non-mover.
    # T1 = (L1, v, R1) must not appear at any non-mover step.
    # At step s1: T1 appears (mover). At step s2+1: (L2, v, R2) appears (non-mover).
    # T1 ≠ (L2, v, R2) requires L1 ≠ L2 or R1 ≠ R2.

    # When J=1, K=0: L2=1-L1, R2=R1. So (L2,v,R2)=(1-L1,v,R1) ≠ T1 = (L1,v,R1). OK.
    # T2 = (1-L1, 1-v, R1). Non-mover at s1+1: (L1, 1-v, R1) — different from T2?
    # (L1, 1-v, R1) ≠ (1-L1, 1-v, R1) since L1 ≠ 1-L1. OK.

    # So the forced non-movers don't directly give EC. We need to look further.

    # ALL non-mover triples at proc 1:
    # At every step k where mw[k] ≠ 1: the triple (cycle[k][0], cycle[k][1], cycle[k][2]).
    # c[1] only changes at steps s1 and s2. Between s1 and s2: c[1] = 1-v.
    # Between s2 and s1: c[1] = v.
    # c[0] only changes when proc 0 fires (fc(0)=2 times).
    # c[2] only changes when proc 2 fires (fc(2)=2 times).

    # Let's track (c0, c2) through the FULL cycle:
    # Starting at step 0: (c0_0, c2_0) = (0, 0) [all start at 0]
    # Every time proc 0 fires: c0 toggles. Every time proc 2 fires: c2 toggles.
    # After all fires: (c0, c2) returns to (0, 0).

    # The (c0, c2) trajectory visits 4 values from {0,1}^2.
    # With fc(0)=2 and fc(2)=2: c0 toggles twice (returns), c2 toggles twice (returns).
    # Possible trajectories depend on relative ordering of fires.

    # Key: c0 is in state 0 for some steps and state 1 for others.
    # Similarly c2. The simultaneous (c0, c2) visits at most 4 states.
    # With 2 toggles each: the trajectory visits exactly 2 states each,
    # spending some time in each.

    # The mover triples use 2 of the 8 possible triples.
    # For non-EC: no other step has the same triple.
    # With only 4 possible (c0, c2) values and 2 c1 values,
    # 8 possible triples. We use 2 as mover. Need the remaining 6 to cover
    # all L-2 non-mover steps without hitting those 2.

    # Actually: with L=24 and 22 non-mover steps, we need at most 6 distinct triples.
    # 6 available non-mover triples, 22 steps. On average 3.67 per triple. Tight but OK.

    # BUT: the constraint is that the (c0, c2) trajectory must visit both values
    # seen in the mover triples at EXACTLY the mover steps and never at non-mover steps.

    # T1 at s1: (L1, v, R1). c1=v between s2 and s1. So during this half of the cycle,
    # the triple (L1, v, R1) can only appear if c0=L1 and c2=R1 at some non-mover step.

    # c0=L1 happens after proc 0 fires an odd number of times (if L1=1) or even (if L1=0).
    # Starting from 0: c0=0 initially, c0=1 after 1st fire, c0=0 after 2nd.
    # If L1=0: c0=L1 at start and after 2nd fire. If L1=1: c0=L1 after 1st fire.

    # Similarly for c2=R1.

    # The mover step s1 happens when c0=L1 and c2=R1 and c1=v.
    # For non-EC: NO other step has c0=L1, c2=R1, c1=v (except s1).

    # c1=v during the s2→s1 half. So we need: in the s2→s1 half, (c0,c2)=(L1,R1)
    # only at step s1 itself.

    # How long is the s2→s1 half? Depends on the mover word.
    # If half the steps: ~12 steps.
    # During these 12 steps, c0 and c2 each toggle at most once (since J'=1, K'=2
    # but some fires might be in the other half).

    # Actually: in phase 1 (s2→s1), left fires J' times and right fires K' times.
    # The remaining left fires (J total in phase 0) and right fires (K in phase 0).
    # But there are also OTHER procs (3-8) firing between s2 and s1 that don't affect
    # the triple at proc 1.

    # The fires of proc 0 and proc 2 are spread across both phases.
    # Phase 0 has J left fires and K right fires.
    # Phase 1 has J' left fires and K' right fires.
    # With J+J'=2, K+K'=2.

    # For the residual case J=1,K=0: J'=1, K'=2.
    # In phase 1 (c1=v): left fires 1 time, right fires 2 times.

    # (c0,c2) trajectory in phase 1:
    # Start: (1-L1, R1) [since at s2, after phase 0 with J=1 left fires: c0=1-L1;
    #   K=0 right fires: c2=R1... wait, c2 at s2 depends on fires of proc 2 in phase 0]

    # Let me be very precise about the full cycle.
    # Let c0_init = cycle[0][0] = 0. Similarly c2_init = 0.
    # At step s1: c0 = L1, c2 = R1. This depends on how many times proc 0 and 2
    # fired before step s1.

    # Proc 0 fires at 2 specific steps. Let them be a1, a2 (with a1 < a2 mod L).
    # At step s1: c0 = (number of proc-0 fires before s1) mod 2 = L1.
    # At step s2: c0 = (number of proc-0 fires before s2) mod 2.

    # In the residual phase (s1→s2): J=1 proc-0 fire. So between s1 and s2, 1 proc-0 fire.
    # c0 at s2 = L1 ⊕ 1 = 1-L1. ✓ matches T2.

    # In phase 1 (s2→s1): J'=1 proc-0 fire.
    # c0 trajectory in phase 1: starts 1-L1, after fire: L1. Ends at L1 (= c0 at s1). ✓

    # Similarly c2:
    # Phase 0 (s1→s2): K=0 proc-2 fires. c2 stays R1. At s2: c2 = R1. ✓ matches T2.
    # Phase 1 (s2→s1): K'=2 proc-2 fires. c2: R1 → 1-R1 → R1. Ends R1. ✓

    # So in phase 1 (c1=v):
    # (c0,c2) trajectory: (1-L1,R1) → ... → (L1,R1) [end]
    # The exact path depends on ordering of the 3 fires (1 left, 2 right).

    # The triple T1 = (L1, v, R1) needs c0=L1 and c2=R1.
    # c0=L1 happens AFTER the left fire. c2=R1 happens at start and after 2nd right fire.

    # Cases by ordering:
    # (0,2,2): c0 goes L1 early, c2 goes R1→1-R1→R1. (L1,R1) after 1st fire and at end.
    # (2,0,2): c2 goes 1-R1 first, then c0 goes L1, then c2 back to R1. (L1,R1) at end.
    # (2,2,0): c2 goes 1-R1→R1, then c0 goes L1. (L1,R1) at end.

    # In ALL cases: (L1, R1) appears at the end of phase 1.
    # The end of phase 1 = step s1. But s1 is a MOVER step.
    # What about the step JUST BEFORE s1?

    # If the LAST fire in phase 1 is not proc 0 or 2: (c0,c2) is already (L1,R1).
    # Then the step before s1 has (L1,R1) and c1=v → triple T1 as non-mover. EC!

    # If the LAST fire is proc 0 (case 2,2,0): just before proc 0 fires, c0=1-L1.
    # So triple is (1-L1, v, R1) ≠ T1. After fire: (L1, v, R1) at s1 (mover). No non-mover T1.

    # If the LAST fire is proc 2 (cases 0,2,2 and 2,0,2): just before proc 2 fires,
    # c2=1-R1. Triple is (L1, v, 1-R1) ≠ T1 [case 0,2,2] or (L1, v, 1-R1) [case 2,0,2].

    # So when the last fire in phase 1 is proc 0 or proc 2, T1 doesn't appear as
    # non-mover in phase 1. BUT: there are OTHER steps where (L1, R1) might appear.

    # Case (0,2,2): After proc 0 fires: (L1, R1). Steps between proc 0 fire and 1st proc 2 fire.
    # If there are non-proc-0/2 steps here: triple is (L1, v, R1) = T1 as non-mover. EC!
    # If proc 2 fires immediately after proc 0: no gap. No T1 non-mover.

    # So the question is: can proc 0 and proc 2 fire CONSECUTIVELY in the mover word?
    # In a cycle of length 24, with 24 movers including procs 3-8 (18 fires) and procs 0,1,2
    # (6 fires), the probability of consecutive proc-0 and proc-2 fires is low.
    # But it CAN happen.

    # When it does happen: no T1 non-mover in that window.
    # BUT: there might be T1 non-mover elsewhere (in phase 0, where c1=1-v ≠ v... no!
    # T1 has self=v. In phase 0, c1=1-v. So T1 cannot appear in phase 0.)

    # WAIT: T1 has self=v. In phase 0 (s1→s2), c1 = 1-v (after s1 fires v→1-v).
    # So NO step in phase 0 has c1=v. T1 can only appear in phase 1.

    # So if T1 doesn't appear as non-mover in phase 1, we need EC from another source.
    # Let's check T2 = (1-L1, 1-v, R1).
    # T2 has self=1-v, which matches phase 0 (c1=1-v).
    # Phase 0 (s1→s2): c0 starts L1, after proc 0 fires: 1-L1.
    # c2 stays R1 (K=0).
    # T2 = (1-L1, 1-v, R1): need c0=1-L1 and c2=R1.
    # c0=1-L1 after the single proc-0 fire. c2=R1 throughout (K=0).
    # So after proc 0 fires in phase 0: (1-L1, 1-v, R1) = T2 appears!
    # This is at a non-mover step (proc 0 fires, not proc 1).
    # Wait: at the step where proc 0 fires, the config BEFORE fire has c0=L1.
    # After fire: c0=1-L1. The triple at proc 1 at that step (before fire) is
    # (L1, 1-v, R1) ≠ T2.
    # At the NEXT step: (1-L1, 1-v, R1) = T2!

    # So T2 appears as non-mover in phase 0, one step after proc 0 fires!
    # (assuming proc 1 doesn't fire at that next step — but proc 1 only fires at s2,
    # and this is inside phase 0, not at s2 unless proc 0 fires at step s2-1.)

    # If proc 0 fires at step s2-1 (the step right before s2):
    # Then (1-L1, 1-v, R1) = T2 appears at step s2 — but s2 IS the mover step for T2!
    # So T2 at s2 is mover, and the non-mover would be at s2 (contradiction).

    # So if proc 0 fires at s2-1: T2 appears at s2 as mover, no non-mover version.
    # Otherwise: T2 appears one step after proc 0's fire in phase 0 as non-mover. EC!

    # BOTH conditions:
    # T1 as non-mover in phase 1: fails if proc 0 and proc 2 fire back-to-back
    #   and the last fire is proc 0 or 2.
    # T2 as non-mover in phase 0: fails if proc 0 fires at step s2-1.

    # Can BOTH fail simultaneously?
    # T2 fails: proc 0 fires at step s2-1.
    # Then in phase 0: proc 0's single fire is at s2-1.
    # In phase 1: proc 0's single fire is at some step in (s2, s1).
    # T1 fails: need all 3 fires in phase 1 (proc 0 once, proc 2 twice) to be
    #   packed such that no non-mover step has (L1, R1).

    # Let me check: with proc 0 firing at s2-1 in phase 0, and proc 0 firing at
    # some step a in phase 1:
    # After proc 0 fires at a: c0 becomes L1.
    # For T1 to never appear: need (L1, R1) to never be (c0, c2) at a non-mover step.
    # c2 is R1 before 1st proc-2 fire, 1-R1 between fires, R1 after 2nd.
    # (L1, R1) appears if c0=L1 and c2=R1 simultaneously at a non-mover step.

    # If proc 0 fires first in phase 1: c0=L1 after. Then:
    #   If next non-mover step before proc 2 fires: (L1, R1) → T1. EC!
    #   Unless proc 2 fires immediately after proc 0.

    # If proc 2 fires immediately after proc 0: c2 goes to 1-R1. Then:
    #   Later proc 2 fires again: c2 goes to R1. If non-mover step between: (L1, R1) → EC!
    #   Unless proc 1 fires (= step s1) immediately after 2nd proc-2 fire.

    # So the worst case: proc 0, proc 2, ..., proc 2, proc 1 fire consecutively.
    # That means steps ..., a, a+1, ..., s1-1, s1 have movers 0, 2, ..., 2, 1.
    # With 3 fires in sequence: a=s1-3, s1-2 fires proc 2, s1-1 fires proc 2.
    # After a: (L1, 1-R1) [proc 2 fired at a? No: proc 0 at a].
    # After a (proc 0): c0=L1, c2=R1 still.
    # After a+1 (proc 2): c0=L1, c2=1-R1.
    # After a+2 (proc 2): c0=L1, c2=R1 → step a+3 = s1 has T1 as mover.
    # Between a and a+1: at step a+1, before proc 2 fires: (L1, R1) → triple T1. Non-mover?
    # Only if mw[a+1] ≠ 1. Yes, mw[a+1] = 2 ≠ 1. So proc 1 is non-mover. EC!

    # Wait: at step a+1, BEFORE the fire at that step, the triple is (L1, v, R1).
    # But step a fires proc 0. After fire: c0=L1. Between step a's fire and step a+1:
    # there's no step — step a+1 immediately follows.
    # At step a+1: the config is AFTER step a's fire. So c0=L1, c2=R1 (unchanged).
    # At step a+1, proc 2 fires. So proc 1 is non-mover.
    # Triple at proc 1 at step a+1: (L1, v, R1) = T1.
    # This is a non-mover step for proc 1. EC!

    print("""
CORRECTED PROOF:

Case J=1, K=0 (residual phase): J'=1, K'=2 in other phase.

In phase 1 (c1=v, between s2 and s1):
  proc 0 fires once (c0: 1-L1 → L1)
  proc 2 fires twice (c2: R1 → 1-R1 → R1)

At the step AFTER proc 0 fires (call it step a+1):
  c0 = L1 (just toggled), c2 = R1 or 1-R1 (depends on proc 2 fire ordering)

Key: at step a+1, the mover is NOT proc 1 (isolated firing). So proc 1 is non-mover.

Sub-case: c2 = R1 at step a+1 (proc 2 hasn't fired yet, or has fired twice):
  Triple at proc 1 = (L1, v, R1) = T1. NON-MOVER. EC!

Sub-case: c2 = 1-R1 at step a+1 (proc 2 has fired once):
  Triple at proc 1 = (L1, v, 1-R1) ≠ T1. No EC here.
  But proc 2 fires again later. At that step (or the next):
  c2 returns to R1. If there's a non-mover step with c0=L1, c2=R1, c1=v → EC.

  After proc 0's fire (step a): c0 = L1 permanently for the rest of phase 1.
  After proc 2's 2nd fire (step b): c2 = R1 permanently until s1.
  At step b+1 (or b if there's a gap): if mw[b+1] ≠ 1 (true, isolated):
    Triple = (L1, v, R1) = T1. Non-mover. EC!

  The only escape: b+1 = s1 (proc 2's 2nd fire immediately precedes proc 1's fire).
  But even then: at step b, mw[b] = 2 (proc 2 fires).
  BEFORE proc 2 fires at step b: c2 = 1-R1. After: c2 = R1.
  At step b: proc 1 is non-mover. Triple = (L1, v, 1-R1). Not T1.
  At step b+1 = s1: Triple = (L1, v, R1) = T1. MOVER. Not EC.

  But: there must be steps BETWEEN a+1 and b where other procs fire.
  At all such steps: c0 = L1, c1 = v.
  c2 = 1-R1 (between proc 2's 1st and 2nd fires).
  Triple = (L1, v, 1-R1) at all these steps. Not T1.

  NOW: look at PHASE 0 for T2.
  T2 = (1-L1, 1-v, R1). In phase 0 (c1 = 1-v), proc 0 fires J=1 time.
  After proc 0 fires: c0 = 1-L1. c2 = R1 (K=0).
  At step after proc 0 fires: Triple = (1-L1, 1-v, R1) = T2. Non-mover. EC!

  UNLESS: proc 0 fires at step s2-1 (immediately before proc 1's 2nd firing).
  Then T2 appears at step s2 as MOVER.
  But step s2 IS the mover for T2. So no non-mover T2.

  Can both fail? Need:
  1. T1 non-mover in phase 1 fails: proc 2's 2nd fire is at step s1-1.
  2. T2 non-mover in phase 0 fails: proc 0's fire in phase 0 is at step s2-1.

  Is this possible? Yes! Both are independent constraints.

  In this case: proc 0 fires at s2-1 (phase 0) and at step a (phase 1).
  proc 2 fires at steps b1 and s1-1 (phase 1, since K=0 in phase 0).
  All 4 neighbor fires accounted for (proc 0: s2-1, a; proc 2: b1, s1-1).

  Now what? Let's look at the SECOND remaining non-mover triple option.

  Consider proc 0's fire at step a in phase 1.
  Before fire at a: c0 = 1-L1.
  At step a: proc 0 fires, proc 1 non-mover. Triple at proc 1: (1-L1, v, c2_a).
  After fire: c0 = L1.
  At step a+1: triple at proc 1 = (L1, v, c2_{a+1}).

  If c2_a = R1: triple at step a is (1-L1, v, R1). Not T1.
  If c2_{a+1} = R1: triple at step a+1 is T1 = (L1, v, R1). EC!
  c2_{a+1} = R1 iff proc 2 hasn't fired yet (c2 still R1) or has fired twice.

  With proc 2 fires at b1 and s1-1:
  If a < b1: c2 at a+1 = R1. EC!
  If b1 < a < s1-1: c2 at a+1 = 1-R1. No EC from T1.
  If a > s1-1: impossible (a is in phase 1, before s1).

  Sub-case b1 < a < s1-1:
  Step a+1 has (L1, v, 1-R1). Steps after a until s1-1 have c0=L1, c2=1-R1.
  At step s1-1: proc 2 fires. Before: (L1, v, 1-R1). Not T1. After: (L1, v, R1) = T1 at s1.

  And in phase 0: proc 0 fires at s2-1. Steps before s2-1 have c0=L1, c2=R1.
  Triple = (L1, 1-v, R1). T2 = (1-L1, 1-v, R1). Not the same (L1 ≠ 1-L1).

  At step s2: T2 = (1-L1, 1-v, R1) is mover.
  After s2 fires (step s2+1): (1-L1, v, R1) — different self from T2.

  Hmm, we're running out of easy options. Let me look at T1 in a DIFFERENT WAY.

  Actually: in phase 0, c1 = 1-v. So triples with self=v (like T1) CANNOT appear
  in phase 0 at all. T1 can only appear in phase 1.

  Similarly, T2 has self=1-v, so T2 can only appear in phase 0.

  For non-EC: T1 never as non-mover in phase 1, T2 never as non-mover in phase 0.

  Phase 0 (s1→s2): J=1 left fire, K=0 right fires. c0: L1→1-L1. c2: R1 constant.
  Steps in phase 0: some number of steps where other procs (3-8) fire.
  Before proc 0 fires: c0=L1. Triple = (L1, 1-v, R1).
  After proc 0 fires: c0=1-L1. Triple = (1-L1, 1-v, R1) = T2.
  T2 as non-mover: any step after proc 0 fires (before s2).
  Unless proc 0 fires at s2-1: then T2 only at s2 (mover).

  Phase 1 (s2→s1): J'=1 left fire, K'=2 right fires. c0: 1-L1→L1. c2: R1→1-R1→R1.
  Steps in phase 1: s2+1, s2+2, ..., s1-1.
  For T1=(L1,v,R1): need c0=L1 and c2=R1 simultaneously at some step.
  c0=L1 after proc 0 fires. c2=R1 before 1st proc-2 fire and after 2nd.
  T1 as non-mover: any step with c0=L1, c2=R1, mw[k]≠1.

  For BOTH to fail simultaneously:
  - proc 0 fires at s2-1 (kills T2 in phase 0)
  - In phase 1: whenever c0=L1 (after proc 0's fire), c2≠R1
    This means: proc 0 fires BETWEEN proc 2's 1st and 2nd fires.
    i.e., b1 < a < s1-1 where b1 is proc 2's 1st fire, a is proc 0's fire.

  In this worst case: no T1 or T2 as non-mover.
  But there are OTHER triples in the cycle!

  Actually wait — we need to consider ALL 8 possible triples, not just T1 and T2.
  There might be EC from a different triple appearing both as mover and non-mover.

  But with only 2 mover triples (T1 and T2), EC means T1∈N or T2∈N.
  If neither T1 nor T2 appears as non-mover, there's no EC at proc 1.

  Does EC always occur at ANOTHER proc instead? From the survey:
  97.7% of the time EC is at proc 1 itself. But 2.3% it's only elsewhere.
  Wait no: the breakdown showed EC at mid 97.7%, EC at other 100%.
  These overlap (multiple procs can have EC).

  Let me check: is there ever NO EC at proc 1 specifically?
""")


def check_ec_at_proc1_specifically():
    """Check if EC always holds at proc 1 specifically."""
    random.seed(42)
    ms = (2, 2, 2, 3, 3, 3, 3, 3, 3)
    n = 9

    from ra_consec_residual2 import analyze_phases_at_proc

    no_ec_at_1 = 0
    total = 0

    for trial in range(500000):
        fires = []
        for p in range(n):
            fires.extend([p] * ms[p])
        if random.random() < 0.3:
            extra = random.randint(1, 3)
            for _ in range(extra):
                p = random.randint(0, n-1)
                fires.extend([p] * ms[p])
        random.shuffle(fires)
        mw = fires
        fc = Counter(mw)
        ok = all(fc.get(p, 0) % ms[p] == 0 and fc.get(p, 0) >= ms[p] for p in range(n))
        if not ok: continue

        config = [0] * n
        cycle = [tuple(config)]
        for step in range(len(mw)):
            p = mw[step]
            config = list(cycle[-1])
            if ms[p] == 2:
                config[p] = 1 - config[p]
            else:
                config[p] = (config[p] + 1) % ms[p]
            cycle.append(tuple(config))
        if cycle[-1] != cycle[0]: continue
        cycle = cycle[:-1]
        if len(set(cycle)) != len(cycle): continue

        total += 1
        L = len(mw)

        # Check EC at proc 1 specifically
        mover_triples = set()
        nonmover_triples = set()
        for k in range(L):
            c = cycle[k]
            triple = (c[0], c[1], c[2])
            if mw[k] == 1:
                mover_triples.add(triple)
            else:
                nonmover_triples.add(triple)

        ec_at_1 = bool(mover_triples & nonmover_triples)
        if not ec_at_1:
            no_ec_at_1 += 1
            if no_ec_at_1 <= 5:
                print(f"  No EC at proc 1! trial {trial}")
                print(f"  M={sorted(mover_triples)}, N={sorted(nonmover_triples)}")
                phases = analyze_phases_at_proc(mw, 1, 0, 2)
                for p in phases:
                    print(f"    Phase: J={p['J']}, K={p['K']}, iso={p['isolated']}, odd={p['odd_parity']}")
                # Check EC at proc 0
                m0 = set()
                n0 = set()
                for k in range(L):
                    c = cycle[k]
                    triple = (c[n-1], c[0], c[1])
                    if mw[k] == 0: m0.add(triple)
                    else: n0.add(triple)
                print(f"  EC at proc 0: {bool(m0 & n0)}")

        if total >= 200000:
            break

    print(f"\nTotal cycles: {total}")
    print(f"No EC at proc 1: {no_ec_at_1}")
    print(f"EC at proc 1: {total - no_ec_at_1} ({(total-no_ec_at_1)/total*100:.4f}%)")


if __name__ == "__main__":
    check_ec_at_proc1_specifically()
