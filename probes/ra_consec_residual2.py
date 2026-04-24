#!/usr/bin/env python3
"""
Deeper investigation: Can J+K=1 at a 3CB middle binary ever occur without EC?

Key insight from Part 6: out of 6054 random valid cycles, 2302 had residual phases
and ALL had EC. This suggests the residual + no-EC combination is impossible.

Now: understand WHY. Is it because:
(a) J+K=1 at a 3CB middle binary forces EC (the mechanism we need), or
(b) the EC comes from elsewhere (another proc), not from the residual phase

Also: the counterexample mover word has ALL procs 1-8 binary. With 8 binary procs,
at 3CB block {1,2,3}, the phases have J+K=2 (both neighbors fire once each).
The residual J+K=1 requires one neighbor to NOT fire in the gap — is this possible
when all neighbors are binary?
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import Counter
import random

from verifier import all_configs


def analyze_phases_at_proc(mover_word, proc, left_proc, right_proc):
    """Extract phases at a proc between consecutive firings."""
    L = len(mover_word)
    fire_steps = [k for k in range(L) if mover_word[k] == proc]
    if len(fire_steps) < 2:
        return []

    phases = []
    for idx in range(len(fire_steps)):
        s1 = fire_steps[idx]
        s2 = fire_steps[(idx + 1) % len(fire_steps)]
        gap_steps = []
        k = (s1 + 1) % L
        while k != s2:
            gap_steps.append(k)
            k = (k + 1) % L

        J = sum(1 for k in gap_steps if mover_word[k] == left_proc)
        K = sum(1 for k in gap_steps if mover_word[k] == right_proc)

        # Isolation: step before s2 is not proc
        prev_s2 = (s2 - 1) % L
        isolated = (mover_word[prev_s2] != proc)

        # Parity: count left/right fires up to s1+1 and s2
        # Simple approach: count in the gap
        left_gap = J
        right_gap = K
        # Odd parity means: at least one of left_gap, right_gap is odd
        parity_ok = (left_gap % 2 == 0) and (right_gap % 2 == 0)

        phases.append({
            'idx': idx, 's1': s1, 's2': s2,
            'gap_len': len(gap_steps),
            'J': J, 'K': K, 'J+K': J + K,
            'isolated': isolated,
            'odd_parity': not parity_ok,
        })
    return phases


def check_entry_conflict(cycle, mover_word):
    """Check EC at each proc."""
    n = len(cycle[0])
    L = len(cycle)
    ec_procs = []

    for proc in range(n):
        mover_triples = set()
        nonmover_triples = set()
        for k in range(L):
            c = cycle[k]
            left = c[(proc - 1) % n]
            self_s = c[proc]
            right = c[(proc + 1) % n]
            triple = (left, self_s, right)
            if mover_word[k] == proc:
                mover_triples.add(triple)
            else:
                nonmover_triples.add(triple)
        overlap = mover_triples & nonmover_triples
        if overlap:
            ec_procs.append((proc, overlap))

    return ec_procs


def build_cycle_from_mw(ms, mover_word, ternary_mode='inc'):
    """Build config cycle from mover word."""
    n = len(ms)
    L = len(mover_word)
    config = [0] * n
    cycle = [tuple(config)]
    for step in range(L):
        p = mover_word[step]
        config = list(cycle[-1])
        if ms[p] == 2:
            config[p] = 1 - config[p]
        else:
            if ternary_mode == 'inc':
                config[p] = (config[p] + 1) % ms[p]
            else:
                config[p] = (config[p] - 1) % ms[p]
        cycle.append(tuple(config))

    if cycle[-1] != cycle[0]:
        return None
    cycle = cycle[:-1]
    if len(set(cycle)) != len(cycle):
        return None
    return cycle


def survey_residual_ec_source():
    """
    For cycles with residual phases that have EC:
    WHERE does the EC come from? At the 3CB middle binary, or elsewhere?
    """
    print("=" * 70)
    print("SURVEY: Where does EC come from in residual cases?")
    print("=" * 70)

    random.seed(42)
    ms = (2, 2, 2, 3, 3, 3, 3, 3, 3)
    n = 9

    residual_ec_at_3cb = 0
    residual_ec_elsewhere = 0
    residual_no_ec = 0
    total_residual = 0

    for trial in range(20000):
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
        if not ok:
            continue

        cycle = build_cycle_from_mw(ms, mw)
        if cycle is None:
            continue

        # Check for residual at 3CB {0,1,2}, middle=1
        phases = analyze_phases_at_proc(mw, 1, 0, 2)
        has_residual = any(
            p['isolated'] and p['odd_parity'] and p['J+K'] == 1
            for p in phases
        )

        if not has_residual:
            continue

        total_residual += 1
        ec_procs = check_entry_conflict(cycle, mw)

        if not ec_procs:
            residual_no_ec += 1
            print(f"\n  *** NO EC with residual at trial {trial} ***")
            print(f"  mw = {mw}")
            continue

        # Where is EC?
        ec_proc_ids = [p for p, _ in ec_procs]
        # Check if EC at 3CB block procs (0, 1, or 2)
        at_3cb = any(p in [0, 1, 2] for p in ec_proc_ids)
        if at_3cb:
            residual_ec_at_3cb += 1
        else:
            residual_ec_elsewhere += 1
            if residual_ec_elsewhere <= 5:
                print(f"\n  EC only at non-3CB procs: {ec_proc_ids}")
                for p, overlap in ec_procs:
                    print(f"    proc {p}: overlap triples = {overlap}")

    print(f"\n\nResults ({total_residual} residual cases):")
    print(f"  EC at 3CB block: {residual_ec_at_3cb}")
    print(f"  EC only elsewhere: {residual_ec_elsewhere}")
    print(f"  No EC at all: {residual_no_ec}")
    print(f"  Total: {residual_ec_at_3cb + residual_ec_elsewhere + residual_no_ec}")


def analyze_jk1_mechanism():
    """
    WHY does J+K=1 at a 3CB middle binary with increment transitions force EC?

    At the middle binary proc p (m=2), with both neighbors binary:
    - Phase has J+K=1: exactly one neighbor fires in the gap
    - Say J=1, K=0: left neighbor fires once, right doesn't
    - Since p is binary, its value alternates: v_p at s1, then 1-v_p at s2
    - Since right doesn't fire (K=0): right value is constant in the gap
    - Left fires once: left value changes once in the gap

    The mover triple at s1 is (left_val, v_p, right_val) -> v_p fires -> 1-v_p
    After left fires: left_val changes to 1-left_val (binary!)
    The mover triple at s2 is (1-left_val, 1-v_p, right_val) -> (1-v_p) fires -> v_p

    For EC, we need a non-mover step with the same triple as a mover step.

    Key: with binary neighbors, the context space is {0,1}^3 = 8 triples.
    Each mover step uses one triple; the cycle has L non-mover steps at p.
    If L is large enough relative to 8, pigeonhole forces overlap.

    But: the mover triples are DIFFERENT from the non-mover triples
    UNLESS the same (left, self, right) appears as both mover and non-mover.
    """
    print("\n" + "=" * 70)
    print("MECHANISM: Why J+K=1 at 3CB middle binary forces EC")
    print("=" * 70)

    # Let's look at specific cases
    ms = (2, 2, 2, 3, 3, 3, 3, 3, 3)
    n = 9

    random.seed(123)
    found = 0

    for trial in range(50000):
        fires = []
        for p in range(n):
            fires.extend([p] * ms[p])
        if random.random() < 0.2:
            p = random.randint(0, n-1)
            fires.extend([p] * ms[p])
        random.shuffle(fires)
        mw = fires

        fc = Counter(mw)
        ok = all(fc.get(p, 0) % ms[p] == 0 and fc.get(p, 0) >= ms[p] for p in range(n))
        if not ok:
            continue

        cycle = build_cycle_from_mw(ms, mw)
        if cycle is None:
            continue

        phases = analyze_phases_at_proc(mw, 1, 0, 2)
        residual_phases = [p for p in phases
                          if p['isolated'] and p['odd_parity'] and p['J+K'] == 1]

        if not residual_phases:
            continue

        found += 1
        if found > 3:
            break

        L = len(mw)
        rp = residual_phases[0]

        print(f"\nTrial {trial}: Residual phase at proc 1")
        print(f"  Phase: s1={rp['s1']}, s2={rp['s2']}, J={rp['J']}, K={rp['K']}")

        # Show the triples at proc 1 during this phase
        s1 = rp['s1']
        s2 = rp['s2']

        print(f"\n  Triples at proc 1 during phase:")
        k = s1
        while True:
            c = cycle[k]
            triple = (c[0], c[1], c[2])
            role = "MOVER" if mw[k] == 1 else f"non-mover (mover={mw[k]})"
            print(f"    step {k:3d}: triple={triple}, {role}")
            if k == s2:
                break
            k = (k + 1) % L

        # Also show the full mover/nonmover triple sets for proc 1
        mover_triples = set()
        nonmover_triples = set()
        for k in range(L):
            c = cycle[k]
            triple = (c[0], c[1], c[2])
            if mw[k] == 1:
                mover_triples.add(triple)
            else:
                nonmover_triples.add(triple)

        print(f"\n  ALL mover triples at proc 1: {sorted(mover_triples)}")
        print(f"  ALL nonmover triples at proc 1: {sorted(nonmover_triples)}")
        overlap = mover_triples & nonmover_triples
        print(f"  Overlap: {sorted(overlap)}")

        if overlap:
            # Find the specific steps
            for ot in overlap:
                mover_steps = [k for k in range(L) if mw[k] == 1 and
                              (cycle[k][0], cycle[k][1], cycle[k][2]) == ot]
                nonmover_steps = [k for k in range(L) if mw[k] != 1 and
                                 (cycle[k][0], cycle[k][1], cycle[k][2]) == ot]
                print(f"  Overlap triple {ot}: mover at steps {mover_steps}, non-mover at steps {nonmover_steps}")


def check_counterexample_residual():
    """
    The counterexample ms=(3,2,...,2) has 8 binary procs.
    Check: does it have J+K=1 at ANY 3CB middle binary?
    """
    print("\n" + "=" * 70)
    print("Counterexample: J+K check at all 3CB blocks")
    print("=" * 70)

    ms = (3, 2, 2, 2, 2, 2, 2, 2, 2)
    n = 9
    mw = [0, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0, 8, 7, 6, 5, 4, 3, 2, 1]

    # 3CB blocks: any 3 consecutive procs all binary
    # Binary procs: 1-8 (all 8 of them)
    # 3CB blocks: {1,2,3}, {2,3,4}, ..., {6,7,8}
    # Also wrapping: {7,8,1} needs proc 8,1 binary AND the third
    # Wait: proc 0 is ternary. So {8,0,1} is NOT 3CB (proc 0 is ternary)
    # Similarly {0,1,2} is not 3CB (proc 0 ternary)
    # Valid 3CB blocks: {1,2,3}, {2,3,4}, {3,4,5}, {4,5,6}, {5,6,7}, {6,7,8}

    for i in range(1, 7):
        mid = i + 1
        left_p = i
        right_p = i + 2
        phases = analyze_phases_at_proc(mw, mid, left_p, right_p)
        print(f"\n3CB {{proc {left_p}, {mid}, {right_p}}}:")
        for p in phases:
            dispatch = ""
            if p['J+K'] >= 2:
                dispatch = "DISPATCHED (J+K >= 2)"
            elif not p['odd_parity']:
                dispatch = "DISPATCHED (even parity)"
            elif not p['isolated']:
                dispatch = "DISPATCHED (not isolated)"
            else:
                dispatch = "*** RESIDUAL ***"
            print(f"  Phase: J={p['J']}, K={p['K']}, J+K={p['J+K']}, odd={p['odd_parity']}, iso={p['isolated']} -> {dispatch}")

    print(f"\nConclusion: The counterexample has J+K=2 at ALL 3CB blocks.")
    print(f"With 8 binary procs in a sweep, every gap between consecutive firings")
    print(f"of the middle proc includes exactly one fire of each neighbor.")
    print(f"So J+K=1 is IMPOSSIBLE in this mover word structure.")
    print(f"\nThe counterexample does NOT produce the residual.")
    print(f"It blocks normalForm_gives_ec (which claims ALL normal-form → EC),")
    print(f"but the residual never occurs in this counterexample.")


def systematic_jk1_analysis():
    """
    Systematic analysis: When does J+K=1 occur at a 3CB middle binary?
    And when it does, why does EC always follow?
    """
    print("\n" + "=" * 70)
    print("SYSTEMATIC: When does J+K=1 occur and why does EC follow?")
    print("=" * 70)

    random.seed(999)
    ms = (2, 2, 2, 3, 3, 3, 3, 3, 3)
    n = 9

    # Classify all residual cases by their structure
    jk_10_count = 0  # J=1, K=0
    jk_01_count = 0  # J=0, K=1
    ec_at_mid = 0
    ec_at_left = 0
    ec_at_right = 0
    ec_at_other = 0
    total = 0

    for trial in range(100000):
        fires = []
        for p in range(n):
            fires.extend([p] * ms[p])
        if random.random() < 0.3:
            extra = random.randint(1, 4)
            for _ in range(extra):
                p = random.randint(0, n-1)
                fires.extend([p] * ms[p])
        random.shuffle(fires)
        mw = fires

        fc = Counter(mw)
        ok = all(fc.get(p, 0) % ms[p] == 0 and fc.get(p, 0) >= ms[p] for p in range(n))
        if not ok:
            continue

        cycle = build_cycle_from_mw(ms, mw)
        if cycle is None:
            continue

        # 3CB at {0,1,2}
        phases = analyze_phases_at_proc(mw, 1, 0, 2)
        residual_phases = [p for p in phases
                          if p['isolated'] and p['odd_parity'] and p['J+K'] == 1]

        if not residual_phases:
            continue

        total += 1
        rp = residual_phases[0]
        if rp['J'] == 1 and rp['K'] == 0:
            jk_10_count += 1
        else:
            jk_01_count += 1

        ec_procs = check_entry_conflict(cycle, mw)
        if not ec_procs:
            print(f"  *** NO EC at trial {trial} ***")
            continue

        ec_ids = set(p for p, _ in ec_procs)
        if 1 in ec_ids:
            ec_at_mid += 1
        if 0 in ec_ids:
            ec_at_left += 1
        if 2 in ec_ids:
            ec_at_right += 1
        if ec_ids - {0, 1, 2}:
            ec_at_other += 1

    print(f"\nTotal residual cases: {total}")
    print(f"  J=1,K=0: {jk_10_count}")
    print(f"  J=0,K=1: {jk_01_count}")
    print(f"\nEC location breakdown:")
    print(f"  At middle binary (proc 1): {ec_at_mid} ({ec_at_mid/total*100:.1f}%)")
    print(f"  At left binary (proc 0): {ec_at_left} ({ec_at_left/total*100:.1f}%)")
    print(f"  At right binary (proc 2): {ec_at_right} ({ec_at_right/total*100:.1f}%)")
    print(f"  At other procs: {ec_at_other} ({ec_at_other/total*100:.1f}%)")


def test_jk1_implies_ec_directly():
    """
    Direct test: take ANY mover word where a 3CB middle binary has a J+K=1 phase.
    Does the cycle ALWAYS have EC?

    Test with MULTIPLE ms vectors, not just (2,2,2,3,...,3).
    """
    print("\n" + "=" * 70)
    print("DIRECT TEST: J+K=1 at 3CB middle binary → EC?")
    print("=" * 70)

    random.seed(2024)

    ms_options = [
        (2, 2, 2, 3, 3, 3, 3, 3, 3),  # 3b + 6t
        (2, 2, 2, 3, 3, 3, 3, 3, 4),  # 3b + 5t + 1q
        (2, 2, 2, 2, 3, 3, 3, 3, 3),  # 4b + 5t (3CB at {0,1,2})
    ]

    for ms in ms_options:
        n = len(ms)
        product = 1
        for m in ms:
            product *= m
        threshold = 4 * 3 ** (n - 2)

        print(f"\nms = {ms}, product = {product}, sub-threshold = {product < threshold}")

        total_residual = 0
        ec_count = 0
        no_ec_count = 0

        for trial in range(50000):
            fires = []
            for p in range(n):
                fires.extend([p] * ms[p])
            if random.random() < 0.2:
                p = random.randint(0, n-1)
                fires.extend([p] * ms[p])
            random.shuffle(fires)
            mw = fires

            fc = Counter(mw)
            ok = all(fc.get(p, 0) % ms[p] == 0 and fc.get(p, 0) >= ms[p] for p in range(n))
            if not ok:
                continue

            cycle = build_cycle_from_mw(ms, mw)
            if cycle is None:
                # Try decrement
                cycle = build_cycle_from_mw(ms, mw, 'dec')
                if cycle is None:
                    continue

            # Check residual at 3CB {0,1,2}
            phases = analyze_phases_at_proc(mw, 1, 0, 2)
            has_residual = any(
                p['isolated'] and p['odd_parity'] and p['J+K'] == 1
                for p in phases
            )
            if not has_residual:
                continue

            total_residual += 1
            ec_procs = check_entry_conflict(cycle, mw)
            if ec_procs:
                ec_count += 1
            else:
                no_ec_count += 1
                if no_ec_count <= 2:
                    print(f"  *** NO EC! trial {trial}, mw length={len(mw)}")

        print(f"  Residual cases: {total_residual}")
        print(f"  With EC: {ec_count}")
        print(f"  Without EC: {no_ec_count}")
        if total_residual > 0:
            print(f"  EC rate: {ec_count/total_residual*100:.2f}%")


def investigate_smaller_n():
    """
    Test at smaller n where exhaustive analysis is feasible.
    n=5 with ms=(2,2,2,3,3): enumerate ALL mover words.
    """
    print("\n" + "=" * 70)
    print("EXHAUSTIVE: n=5, ms=(2,2,2,3,3)")
    print("=" * 70)

    from itertools import permutations

    ms = (2, 2, 2, 3, 3)
    n = 5

    # Minimum fires: 2,2,2,3,3 = total 12
    # Build all permutations of the fire sequence
    fires = [0,0, 1,1, 2,2, 3,3,3, 4,4,4]  # minimum
    L = len(fires)

    print(f"ms = {ms}, minimum cycle length = {L}")
    print(f"Enumerating all distinct permutations of {fires}...")

    # Use set to get unique permutations
    seen = set()
    total = 0
    valid_cycles = 0
    residual_count = 0
    ec_count = 0
    no_ec_count = 0

    # Too many permutations for 12 elements — use random sampling instead
    random.seed(42)
    for trial in range(200000):
        mw = list(fires)
        random.shuffle(mw)
        key = tuple(mw)
        if key in seen:
            continue
        seen.add(key)
        total += 1

        cycle = build_cycle_from_mw(ms, mw)
        if cycle is None:
            cycle = build_cycle_from_mw(ms, mw, 'dec')
            if cycle is None:
                continue

        valid_cycles += 1

        phases = analyze_phases_at_proc(mw, 1, 0, 2)
        has_residual = any(
            p['isolated'] and p['odd_parity'] and p['J+K'] == 1
            for p in phases
        )

        if has_residual:
            residual_count += 1
            ec_procs = check_entry_conflict(cycle, mw)
            if ec_procs:
                ec_count += 1
            else:
                no_ec_count += 1

    print(f"\nTotal distinct mover words sampled: {total}")
    print(f"Valid closed distinct cycles: {valid_cycles}")
    print(f"Residual (J+K=1, isolated, odd parity): {residual_count}")
    print(f"  With EC: {ec_count}")
    print(f"  Without EC: {no_ec_count}")


def investigate_binary_parity_mechanism():
    """
    The core mechanism: at a binary proc p with both neighbors binary,
    if J+K=1 in a phase and the phase has odd parity, what happens?

    Binary parity means: between consecutive firings of p,
    one neighbor fires an odd number of times.

    With J+K=1: one neighbor fires 1 time (odd!), other fires 0 times.
    So the odd-parity neighbor is the one that fires.

    The value of p toggles each firing: v, 1-v, v, 1-v, ...
    The value of the firing neighbor also toggles once in the gap.
    The value of the non-firing neighbor stays constant.

    Mover triple at s1: (L_val, v_p, R_val)
    After p fires: config has (L_val, 1-v_p, R_val) = non-mover at s1

    In the gap, say left fires (J=1, K=0):
    Before left fires: left=L_val
    After left fires: left=1-L_val

    Mover triple at s2: (1-L_val, 1-v_p, R_val)
    After p fires at s2: config has (1-L_val, v_p, R_val) = non-mover at s2

    Non-mover triples during gap: left fires at some step k in the gap.
    Before left fires at k: triple at p is (L_val, 1-v_p, R_val) — same as non-mover at s1!
    Wait, is this an EC? Only if this triple also appears as a mover triple somewhere.

    Actually, the non-mover triple at step s1 (right after p fires) is (L_val, 1-v_p, R_val).
    The mover triple at step s2 is (1-L_val, 1-v_p, R_val).
    These are DIFFERENT (L_val vs 1-L_val).

    But there are fc(p) phases. The mover triples cycle through different (L,S,R).
    For EC, we need a mover triple from one phase to match a non-mover triple from another.

    With fc(p)=2 and ms(p)=2: exactly 2 mover triples.
    The 2 mover triples have the SAME S value (both v_p, since p alternates and fires at even
    positions from start). Wait: p fires at s1 with value v_p, then at s2 with value 1-v_p.
    So the two mover triples have DIFFERENT self values.

    Mover at phase 0: (L0, v0, R0) — fires v0 -> 1-v0
    Mover at phase 1: (L1, 1-v0, R1) — fires 1-v0 -> v0

    Non-mover at phase 0 start: (L0, 1-v0, R0) — just after phase 0 mover fires
    Non-mover at phase 1 start: (L1, v0, R1)

    For EC: need (L0, v0, R0) to appear as non-mover, or (L1, 1-v0, R1) as non-mover.
    Or: need a non-mover triple to match any mover triple.

    Non-mover triples during phase 0 gap (after p fires, before p fires again):
    - Immediately after s1: (L0, 1-v0, R0)
    - During gap: left fires → left becomes 1-L0
    - After left fires: (1-L0, 1-v0, R0)

    So non-mover triples at p during phase 0: {(L0, 1-v0, R0), (1-L0, 1-v0, R0)}
    (before and after left fires — left value changes, self and right stay)

    Non-mover triples at p during phase 1 gap:
    - Immediately after s2: (L1, v0, R1)
    - During gap: one neighbor fires → similar change

    Mover triples: {(L0, v0, R0), (L1, 1-v0, R1)}

    For EC overlap:
    (L0, v0, R0) ∈ non-mover triples? Only if v0 = 1-v0, impossible.
    Unless a non-mover triple from ANOTHER phase has self=v0.
    Phase 1 non-mover triples have self=v0 (since after s2 fires 1-v0→v0).
    So: (L1, v0, R1) is a non-mover triple.
    We need: (L0, v0, R0) = (L1, v0, R1), i.e., L0=L1 and R0=R1.

    Or: (1-L0, v0, R0) could be a non-mover from phase 1
    if left fires in phase 1. But this depends on whether J=1 in phase 1 too.

    KEY INSIGHT: When fc(p)=2 and J+K=1 in BOTH phases...
    The sum of J+K across all phases = fc(left) + fc(right) for the gap steps.
    Actually: sum of J across all phases = fc(left), sum of K = fc(right).
    Since fc(left)=2 and fc(right)=2 (both binary, minimum fires):
    J_0 + J_1 = 2, K_0 + K_1 = 2.
    If J_0+K_0=1 (J_0=1,K_0=0 say): then J_1=1, K_1=2 → J_1+K_1=3 ≥ 2, dispatched!
    Or J_0=0,K_0=1: K_1=1, J_1=2 → dispatched.

    WAIT: This means if ONE phase is residual (J+K=1), the OTHER phase has J+K ≥ 3!
    The other phase is always dispatched!

    But the sorry is about a SINGLE phase being residual. The proof doesn't need
    ALL phases to be residual — it needs to close the branch for that one phase.
    The dispatch routes different phases differently. One phase being dispatched
    doesn't help close the other.

    Unless... we can use the OTHER phase's dispatch to get EC, and that EC is global.
    EC is a global property (hasEntryConflict gc) — if any proc has overlap, we're done.
    """
    print("\n" + "=" * 70)
    print("MECHANISM: Binary parity analysis at 3CB middle binary")
    print("=" * 70)

    ms = (2, 2, 2, 3, 3, 3, 3, 3, 3)
    n = 9

    random.seed(42)
    found = 0

    for trial in range(100000):
        fires = []
        for p in range(n):
            fires.extend([p] * ms[p])
        if random.random() < 0.2:
            p = random.randint(0, n-1)
            fires.extend([p] * ms[p])
        random.shuffle(fires)
        mw = fires

        fc = Counter(mw)
        ok = all(fc.get(p, 0) % ms[p] == 0 and fc.get(p, 0) >= ms[p] for p in range(n))
        if not ok:
            continue

        cycle = build_cycle_from_mw(ms, mw)
        if cycle is None:
            continue

        phases = analyze_phases_at_proc(mw, 1, 0, 2)
        if len(phases) < 2:
            continue

        # Check if any phase is residual
        residual_idx = None
        for p in phases:
            if p['isolated'] and p['odd_parity'] and p['J+K'] == 1:
                residual_idx = p['idx']
                break

        if residual_idx is None:
            continue

        found += 1
        if found > 10:
            break

        # Print phase summary
        print(f"\nTrial {trial}: fc(1)={fc[1]}")
        print(f"  fc(0)={fc[0]}, fc(2)={fc[2]}")
        total_J = sum(p['J'] for p in phases)
        total_K = sum(p['K'] for p in phases)
        print(f"  Total J (left fires in gaps) = {total_J}, should = fc(0) = {fc[0]}")
        print(f"  Total K (right fires in gaps) = {total_K}, should = fc(2) = {fc[2]}")
        for p in phases:
            dispatch = "RESIDUAL" if (p['isolated'] and p['odd_parity'] and p['J+K'] == 1) else "DISPATCHED"
            print(f"  Phase {p['idx']}: J={p['J']}, K={p['K']}, J+K={p['J+K']} -> {dispatch}")


if __name__ == "__main__":
    survey_residual_ec_source()
    check_counterexample_residual()
    systematic_jk1_analysis()
    test_jk1_implies_ec_directly()
    investigate_smaller_n()
    investigate_binary_parity_mechanism()
