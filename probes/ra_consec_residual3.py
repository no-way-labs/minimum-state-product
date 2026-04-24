#!/usr/bin/env python3
"""
Prove the mechanism: J+K=1 at 3CB middle binary → EC.

From Part 6-8, we know:
1. EC rate is 100% among 200k+ samples
2. EC is at the 3CB block procs themselves (97.7% at middle binary)
3. When fc(mid)=2: residual phase has J+K=1, complementary phase has J+K >= 3

The mechanism must be cross-phase: the OTHER phase provides EC.
With J+K >= 2 in the other phase, the standard dispatch handles it.
But wait — the standard dispatch gives EC for J+K >= 2. And EC is GLOBAL.
So if the OTHER phase has J+K >= 2 and the dispatch gives EC, we're done.

Let me verify: when the other phase is dispatched (J+K >= 2), does it always give EC?
And: is J+K >= 2 in the other phase ALWAYS the case?

The key insight from the parity analysis:
- sum of J across phases = fc(left_neighbor)
- sum of K across phases = fc(right_neighbor)
- Both neighbors are binary, so fc(left) >= 2, fc(right) >= 2
- fc(left) % 2 = 0, fc(right) % 2 = 0

If fc(mid) = 2 (minimum for binary):
  Phase 0: J_0 + K_0 = 1 (residual)
  Phase 1: J_1 + K_1 = (fc(left) - J_0) + (fc(right) - K_0) = fc(left) + fc(right) - 1
  Since fc(left) >= 2, fc(right) >= 2: J_1 + K_1 >= 3
  The other phase has J+K >= 3, which is dispatched by the BothEven/one-sided mechanisms.

If fc(mid) = 2k (k >= 2), there are 2k phases. One is residual with J+K=1.
Sum of (J+K) across all phases = fc(left) + fc(right) >= 4.
With 2k phases and one having J+K=1, the remaining 2k-1 phases sum to >= 3.
At least one of them has J+K >= 2 (by pigeonhole if 2k-1 >= 1, which is true for k >= 1).

BUT: does having J+K >= 2 in some OTHER phase guarantee EC?
The dispatch mechanisms work PER PHASE. Having J+K >= 2 in a phase gives EC
at the PIVOT proc (the phase extraction target). And EC is global — once any
proc has EC, the whole cycle has EC.

So the proof strategy is:
1. Extract phases at the 3CB middle binary
2. If ANY phase has J+K >= 2, dispatch gives EC → done
3. If ALL phases have J+K <= 1, but sum of J+K = fc(left)+fc(right) >= 4
   with 2k phases... can ALL have J+K <= 1? Only if 2k >= 4. Each <= 1.
   Sum <= 2k. Need sum >= 4. So 2k >= 4, i.e., k >= 2, fc >= 4.
   And ALL must have J+K = 1 (since sum >= 4 with each <= 1 means need enough).
   Actually: if all 2k phases have J+K <= 1, then sum <= 2k.
   We need sum = fc(left)+fc(right) >= 2+2 = 4.
   So need 2k >= 4, k >= 2.
   With fc(mid) = 2k >= 4: all 4+ phases have J+K <= 1? Sum <= 2k = fc(mid).
   Need fc(left)+fc(right) <= fc(mid).
   But fc(left) >= 2, fc(right) >= 2, so fc(left)+fc(right) >= 4.
   If fc(mid) >= 4: fc(mid) >= 4, and sum of J+K across phases = fc(left)+fc(right).
   For ALL phases to have J+K <= 1: need fc(left)+fc(right) <= 2k = fc(mid).
   This IS possible if fc(mid) >= fc(left)+fc(right).

   But with binary procs: fc(mid) % 2 = 0.
   And: in the sorry hypothesis, fc(mid) >= 2. Actually the sorry says fc >= 2.
   The real question: can all phases have J+K <= 1?

Let me check this computationally for fc(mid) >= 4.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import Counter
import random

from ra_consec_residual2 import (
    analyze_phases_at_proc, check_entry_conflict, build_cycle_from_mw
)


def verify_complementary_phase():
    """
    When fc(mid)=2 and one phase is residual (J+K=1),
    verify the other phase always has J+K >= 2 AND gives EC.
    """
    print("=" * 70)
    print("VERIFY: Complementary phase mechanism")
    print("=" * 70)

    random.seed(42)
    ms = (2, 2, 2, 3, 3, 3, 3, 3, 3)
    n = 9

    fc2_residual = 0
    fc2_other_jk_ge2 = 0
    fc_gt2_all_jk_le1 = 0
    total_residual = 0

    for trial in range(200000):
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

        phases = analyze_phases_at_proc(mw, 1, 0, 2)
        residual_phases = [p for p in phases if p['isolated'] and p['odd_parity'] and p['J+K'] == 1]
        if not residual_phases:
            continue

        total_residual += 1
        fc_mid = fc[1]

        if fc_mid == 2:
            fc2_residual += 1
            # Check the OTHER phase
            other_phases = [p for p in phases if p['idx'] != residual_phases[0]['idx']]
            other_jk_ge2 = any(p['J+K'] >= 2 for p in other_phases)
            if other_jk_ge2:
                fc2_other_jk_ge2 += 1
            else:
                print(f"  fc=2 but other phase has J+K < 2!")
                for p in phases:
                    print(f"    Phase {p['idx']}: J={p['J']}, K={p['K']}")
        else:
            # fc_mid >= 4
            all_le1 = all(p['J+K'] <= 1 for p in phases)
            if all_le1:
                fc_gt2_all_jk_le1 += 1
                print(f"\n  fc(mid)={fc_mid}, ALL phases J+K<=1!")
                for p in phases:
                    print(f"    Phase {p['idx']}: J={p['J']}, K={p['K']}")

    print(f"\nTotal residual cases: {total_residual}")
    print(f"  fc(mid)=2: {fc2_residual}")
    print(f"    Other phase has J+K>=2: {fc2_other_jk_ge2} ({fc2_other_jk_ge2}/{fc2_residual})")
    print(f"  fc(mid)>=4 with ALL J+K<=1: {fc_gt2_all_jk_le1}")


def prove_complementary_phase_analytically():
    """
    Prove: when fc(mid)=2 and one phase is residual (J+K=1),
    the other phase has J+K = fc(left)+fc(right)-1 >= 3.

    Proof:
    - fc(mid) = 2, so there are exactly 2 phases.
    - Phase 0: J_0 + K_0 = 1 (residual)
    - J_0 + J_1 = fc(left), K_0 + K_1 = fc(right)
    - So J_1 + K_1 = fc(left) - J_0 + fc(right) - K_0 = fc(left) + fc(right) - 1
    - fc(left) >= 2 (binary, minimum fires), fc(right) >= 2
    - J_1 + K_1 >= 3

    Now prove: a phase with J+K >= 2 at a binary proc with both neighbors binary
    always gives EC via the existing dispatch.

    Existing dispatch mechanisms for phases:
    1. BothEven: J even, K even, both >= 2 → EC
    2. One-sided: J >= 2, K = 0 or K >= 2, J = 0 → EC (long one-sided phase)
    3. Toggle-FR: >= 3 one-sided → EC

    With J_1 + K_1 >= 3:
    - If J_1 >= 2 and K_1 >= 1: dispatch depends on parities
    - If J_1 = 3, K_1 = 0: one-sided with J=3 → EC
    - If J_1 = 0, K_1 = 3: one-sided with K=3 → EC
    - If J_1 = 2, K_1 = 1 or J_1 = 1, K_1 = 2: mixed phase

    Wait — the dispatch might not handle ALL J+K >= 2 cases. Let me check
    the actual Lean mechanisms more carefully.

    Actually, the Lean proof says:
    - BothEven: both J even and K even → EC
    - One-sided >= 2: one side has >= 2 fires, other has 0 → EC
    - The "dispatch" is: BothEven, then one-sided >= 2, then... more

    For the complementary phase with J_1 + K_1 >= 3:
    Cases:
    (3,0) or (0,3): one-sided with 3 fires → dispatched
    (2,1) or (1,2): mixed, J+K=3
      - (2,1): J even, K odd → BothEven fails. One-sided fails (K=1≠0).
        This is the "mixed" case.
      - Actually: J=2 means left fires twice in the gap.
        For a binary proc: left value toggles twice → returns to original!
        So left parity is EVEN. K=1: right fires once → odd parity.

    Hmm, need to check what happens for (2,1) mixed phase at a binary proc.
    Does the dispatch handle this?

    Let me check computationally: when the other phase has (J,K) with J+K >= 3,
    which specific dispatch mechanism fires?
    """
    print("\n" + "=" * 70)
    print("ANALYTICAL: Complementary phase mechanism")
    print("=" * 70)

    print("""
THEOREM: For a 3CB block {i, mid, r} (all binary, m=2),
if fc(mid) = 2 and one phase is residual (J+K=1):
  - The other phase has J+K = fc(left)+fc(right)-1 >= 3
  - Since fc(left) >= 2 (binary min) and fc(right) >= 2 (binary min)

PROOF:
  fc(mid) = 2 → exactly 2 phases at mid.
  Phase 0: J_0 + K_0 = 1 (residual)
  Total fires across gaps: J_0+J_1 = fc(left), K_0+K_1 = fc(right)
  Phase 1: J_1+K_1 = fc(left)+fc(right) - (J_0+K_0) = fc(left)+fc(right)-1
  Binary constraint: fc(left) % 2 = 0, fc(left) >= 2
  Similarly fc(right) >= 2
  So J_1+K_1 >= 2+2-1 = 3. QED.

REMAINING QUESTION: Does J+K >= 3 always give EC?
  If J >= 2 and K = 0 (or K >= 2 and J = 0): long one-sided → dispatched
  If J >= 1 and K >= 1 and J+K >= 3: mixed phase with both sides active
    → Need to check if this is dispatched
""")


def check_jk_ge3_gives_ec():
    """
    When J+K >= 3 at a binary proc with both neighbors binary, does EC always hold?
    """
    print("=" * 70)
    print("CHECK: J+K >= 3 at binary proc with binary neighbors → EC?")
    print("=" * 70)

    random.seed(2024)
    ms = (2, 2, 2, 3, 3, 3, 3, 3, 3)
    n = 9

    jk3_total = 0
    jk3_ec = 0
    jk3_no_ec = 0
    jk_breakdown = Counter()

    for trial in range(200000):
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

        phases = analyze_phases_at_proc(mw, 1, 0, 2)
        for p in phases:
            if p['J+K'] >= 3:
                jk3_total += 1
                jk_breakdown[(p['J'], p['K'])] += 1

                ec_procs = check_entry_conflict(cycle, mw)
                if ec_procs:
                    jk3_ec += 1
                else:
                    jk3_no_ec += 1
                    if jk3_no_ec <= 3:
                        print(f"  NO EC with J+K={p['J+K']}!")
                break

    print(f"\nTotal phases with J+K >= 3: {jk3_total}")
    print(f"  With EC: {jk3_ec}")
    print(f"  Without EC: {jk3_no_ec}")
    print(f"\n(J,K) breakdown:")
    for (j, k), count in sorted(jk_breakdown.items()):
        print(f"  ({j},{k}): {count}")


def check_jk_ge2_gives_ec():
    """
    More generally: does J+K >= 2 at a binary proc with binary neighbors → EC?
    """
    print("\n" + "=" * 70)
    print("CHECK: J+K >= 2 → EC? (at binary proc, binary neighbors)")
    print("=" * 70)

    random.seed(2024)
    ms = (2, 2, 2, 3, 3, 3, 3, 3, 3)
    n = 9

    jk2_total = 0
    jk2_ec = 0
    jk2_no_ec = 0

    for trial in range(200000):
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

        phases = analyze_phases_at_proc(mw, 1, 0, 2)
        for p in phases:
            if p['J+K'] >= 2:
                jk2_total += 1
                ec_procs = check_entry_conflict(cycle, mw)
                if ec_procs:
                    jk2_ec += 1
                else:
                    jk2_no_ec += 1
                    if jk2_no_ec <= 3:
                        print(f"  NO EC with J={p['J']}, K={p['K']}!")
                break

    print(f"\nTotal phases with J+K >= 2: {jk2_total}")
    print(f"  With EC: {jk2_ec}")
    print(f"  Without EC: {jk2_no_ec}")
    print(f"  EC rate: {jk2_ec/jk2_total*100:.4f}%")


def investigate_direct_mechanism():
    """
    Look at a specific residual case and trace the EC mechanism step by step.
    """
    print("\n" + "=" * 70)
    print("TRACE: Detailed EC mechanism in residual case")
    print("=" * 70)

    random.seed(42)
    ms = (2, 2, 2, 3, 3, 3, 3, 3, 3)
    n = 9

    for trial in range(100000):
        fires = []
        for p in range(n):
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

        if fc[1] != 2:
            continue

        phases = analyze_phases_at_proc(mw, 1, 0, 2)
        residual = [p for p in phases if p['isolated'] and p['odd_parity'] and p['J+K'] == 1]
        if not residual:
            continue

        ec_procs = check_entry_conflict(cycle, mw)
        if not ec_procs:
            continue

        # Found a case! Trace it in detail.
        rp = residual[0]
        other = [p for p in phases if p['idx'] != rp['idx']][0]

        print(f"\nMover word: {mw}")
        print(f"Length: {len(mw)}")
        print(f"\nfc: {dict(fc)}")
        print(f"\nPhases at proc 1 (middle binary of 3CB {{0,1,2}}):")
        print(f"  Residual phase {rp['idx']}: s1={rp['s1']}, s2={rp['s2']}, J={rp['J']}, K={rp['K']}")
        print(f"  Other phase {other['idx']}: s1={other['s1']}, s2={other['s2']}, J={other['J']}, K={other['K']}")

        # Show EC details
        for proc, overlap in ec_procs:
            if proc in [0, 1, 2]:
                print(f"\nEC at proc {proc}:")
                for ot in overlap:
                    # Find mover and non-mover steps
                    mover_steps = []
                    nonmover_steps = []
                    L = len(mw)
                    for k in range(L):
                        c = cycle[k]
                        left = c[(proc - 1) % n]
                        self_s = c[proc]
                        right = c[(proc + 1) % n]
                        if (left, self_s, right) == ot:
                            if mw[k] == proc:
                                mover_steps.append(k)
                            else:
                                nonmover_steps.append(k)
                    print(f"  Triple {ot}: mover at {mover_steps}, nonmover at {nonmover_steps}")

                    # Is the EC within the other phase (J+K>=3)?
                    for ms_step in mover_steps:
                        in_residual = is_in_phase(ms_step, rp, L)
                        in_other = is_in_phase(ms_step, other, L)
                        print(f"    Mover step {ms_step}: in_residual={in_residual}, in_other={in_other}")
                    for ns_step in nonmover_steps[:3]:
                        in_residual = is_in_phase(ns_step, rp, L)
                        in_other = is_in_phase(ns_step, other, L)
                        print(f"    Nonmover step {ns_step}: in_residual={in_residual}, in_other={in_other}")

        break


def is_in_phase(step, phase, L):
    """Check if step is within a phase (between s1 and s2, inclusive)."""
    s1 = phase['s1']
    s2 = phase['s2']
    if s1 <= s2:
        return s1 <= step <= s2
    else:
        return step >= s1 or step <= s2


def prove_ec_via_complementary():
    """
    The proof strategy:

    Given: 3CB at {i, mid, r}, all binary (m=2)
    Given: fc(mid) >= 2, isolated firing, odd parity → residual phase

    CASE 1: fc(mid) = 2
      Two phases. Residual has J+K=1.
      Other phase has J+K = fc(left)+fc(right)-1 >= 3.
      OTHER phase is dispatched → EC at proc mid → done.

    CASE 2: fc(mid) >= 4
      Multiple phases. At least one is residual (J+K=1).
      Sum of J+K across all phases = fc(left)+fc(right) >= 4.
      With fc(mid)/2 phases (since binary, fire count is even):
        If ANY other phase has J+K >= 2 → dispatched → EC → done.
        If ALL phases have J+K <= 1:
          Sum <= fc(mid)/2 (since there are fc(mid)/2 phases)
          Need sum >= 4
          So fc(mid)/2 >= 4 → fc(mid) >= 8

      But wait: the sorry hypothesis says fc(mid) >= 2, not fc(mid) = 2.
      Let me check if fc(mid) >= 4 with all phases having J+K <= 1 ever occurs.
    """
    print("\n" + "=" * 70)
    print("PROOF STRATEGY: Complementary phase EC")
    print("=" * 70)

    random.seed(2024)
    ms = (2, 2, 2, 3, 3, 3, 3, 3, 3)
    n = 9

    # Count cases by fc(mid)
    fc_dist = Counter()
    all_jk_le1_cases = 0
    total_checked = 0

    for trial in range(500000):
        fires = []
        for p in range(n):
            fires.extend([p] * ms[p])
        if random.random() < 0.5:
            extra = random.randint(1, 6)
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

        fc_mid = fc[1]
        phases = analyze_phases_at_proc(mw, 1, 0, 2)
        residual = [p for p in phases if p['isolated'] and p['odd_parity'] and p['J+K'] == 1]
        if not residual:
            continue

        total_checked += 1
        fc_dist[fc_mid] += 1

        all_le1 = all(p['J+K'] <= 1 for p in phases)
        if all_le1:
            all_jk_le1_cases += 1
            print(f"  ALL J+K<=1: fc(mid)={fc_mid}, fc(left)={fc[0]}, fc(right)={fc[2]}")
            for p in phases:
                print(f"    Phase {p['idx']}: J={p['J']}, K={p['K']}")

    print(f"\nTotal residual cases: {total_checked}")
    print(f"  ALL phases J+K<=1: {all_jk_le1_cases}")
    print(f"\nfc(mid) distribution among residual cases:")
    for fc_val, count in sorted(fc_dist.items()):
        print(f"  fc={fc_val}: {count} ({count/total_checked*100:.1f}%)")

    if all_jk_le1_cases == 0:
        print(f"\n>>> NEVER all J+K<=1! The complementary phase ALWAYS has J+K >= 2.")
        print(f">>> This is the proof mechanism.")


def formal_proof_sketch():
    """Print the formal proof sketch."""
    print("\n" + "=" * 70)
    print("FORMAL PROOF SKETCH")
    print("=" * 70)
    print("""
THEOREM (Complementary Phase EC for 3CB Residual):

Given:
- Ring of n >= 9 processors
- 3CB at {i, mid, r} (all binary, m_i = m_mid = m_r = 2)
- Good cycle gc with sub-threshold product
- fc(mid) >= 2
- Isolated firing at mid
- Odd parity at one or both neighbors in the minimum firing gap
- Phase extraction gives a TernaryPhase where dispatch fails

Then: hasEntryConflict gc.

PROOF:

Step 1: Phase structure.
  fc(mid) >= 2 and m_mid = 2 → fc(mid) is even (binary proc returns to start).
  There are exactly fc(mid) phases at mid (gaps between consecutive firings).
  In each phase j: J_j = fires of left neighbor, K_j = fires of right neighbor.

  sum_j J_j = fc(left), sum_j K_j = fc(right).

  Both neighbors binary → fc(left) >= 2, fc(left) even. Same for fc(right).
  So sum_j (J_j + K_j) = fc(left) + fc(right) >= 4.

Step 2: Complementary phase.
  The residual phase has J + K = 1 (by hypothesis of non-dispatch).

  CASE fc(mid) = 2: exactly 2 phases. The other has:
    J' + K' = fc(left) + fc(right) - 1 >= 4 - 1 = 3 >= 2. ✓

  CASE fc(mid) >= 4: at least 2 phases besides the residual.
    Sum of J+K across all other phases = fc(left)+fc(right)-1 >= 3.
    Number of other phases = fc(mid) - 1 >= 3.
    By pigeonhole: some phase has (J+K) >= ceil(3 / (fc(mid)-1)).
    Since fc(mid)-1 >= 3: this gives >= 1. Not enough for >= 2.

    BUT: actually we need a stronger argument for fc(mid) >= 4.

    Key: NOT all phases can have J+K <= 1.
    If all fc(mid) phases have J+K <= 1:
      sum <= fc(mid).
      Need sum = fc(left)+fc(right) >= 4.
      So need fc(mid) >= 4, which is consistent.

    BUT: fc(left)+fc(right) >= 4 and sum = fc(left)+fc(right).
    Each of fc(mid) phases has J+K in {0, 1}.
    Phases with J+K=0: no neighbor fires. Possible if mid fires consecutively.
    But hypothesis says ISOLATED firing → no consecutive firings of mid.
    So between each pair of consecutive mid-firings, there's at least 1 other
    proc firing. That proc could be a neighbor (J+K >= 1) or not (J+K = 0).

    Actually: in the worst case, all non-neighbor procs fire between mid's firings.
    J+K=0 is possible for some phases.

    With fc(mid) phases each having J+K in {0,1}:
    Number of phases with J+K=1 = fc(left)+fc(right) (since each neighbor fire
    contributes to exactly one phase).
    Wait: sum of J_j = fc(left), so number of phases with J_j >= 1 <= fc(left).
    Similarly for K.

    Actually the strongest version:
    Phases with J+K >= 1: at most fc(left)+fc(right) (each neighbor fire in at most 1 phase).
    No wait: each neighbor fire is in EXACTLY one phase (the phase that contains that step).
    So number of phases with J >= 1 = (number of distinct phases containing a left-fire).
    Each left-fire is in exactly one phase, so fc(left) fires in at most fc(left) phases.
    But if multiple left-fires are in the same phase, fewer phases have J >= 1.

    For ALL phases to have J+K <= 1: at most fc(mid) phases have J+K = 1.
    Total J+K = fc(left)+fc(right) >= 4.
    Each contributing phase has J+K = 1, so we need >= 4 phases with J+K=1.
    Need fc(mid) >= 4.

    With fc(mid) = 4: 4 phases, each J+K in {0,1}, sum >= 4.
    All 4 must have J+K = 1. Possible? Only if fc(left)+fc(right) = 4.
    With fc(left) = 2, fc(right) = 2: possible in principle.

    COMPUTATION SAYS: this never happens (0 out of 500k trials).

    WHY? Because isolation means mid fires in separated positions.
    Each phase has at least 1 step. With fc(left)=2 and 4 phases:
    left fires 2 times, spread across 4 gaps. At most 2 gaps have J >= 1.
    Similarly right: at most 2 gaps have K >= 1.
    With 4 gaps, at most 2+2=4 gaps have J+K >= 1. Could reach sum = 4.

    But J+K = 1 in a gap means exactly ONE neighbor fires. The other doesn't.
    If in 2 gaps left fires but not right, and 2 gaps right fires but not left,
    we'd have sum = 4 with all J+K in {0,1}.

    This would require: the 4 gaps are perfectly separated, with left and right
    fires in different gaps. Is this kinematically possible?

    Let me check harder with fc(mid)=4 specifically...
""")


def force_fc4_test():
    """Force fc(mid)=4 and check if all-J+K<=1 is possible."""
    print("=" * 70)
    print("FORCED fc(mid)=4 test")
    print("=" * 70)

    random.seed(42)
    ms = (2, 2, 2, 3, 3, 3, 3, 3, 3)
    n = 9

    found_all_le1 = 0
    total = 0
    total_residual = 0

    for trial in range(1000000):
        # Force fc(1) = 4
        fires = [1, 1, 1, 1]  # 4 fires for proc 1
        for p in range(n):
            if p != 1:
                fires.extend([p] * ms[p])
        random.shuffle(fires)
        mw = fires

        fc = Counter(mw)
        assert fc[1] == 4
        ok = all(fc.get(p, 0) % ms[p] == 0 and fc.get(p, 0) >= ms[p] for p in range(n))
        if not ok:
            continue

        cycle = build_cycle_from_mw(ms, mw)
        if cycle is None:
            continue

        total += 1

        phases = analyze_phases_at_proc(mw, 1, 0, 2)
        residual = [p for p in phases if p['isolated'] and p['odd_parity'] and p['J+K'] == 1]
        if not residual:
            continue

        total_residual += 1
        all_le1 = all(p['J+K'] <= 1 for p in phases)
        if all_le1:
            found_all_le1 += 1
            # Check EC anyway
            ec = check_entry_conflict(cycle, mw)
            print(f"  ALL J+K<=1 at fc=4! EC={bool(ec)}")
            for p in phases:
                print(f"    Phase {p['idx']}: J={p['J']}, K={p['K']}")

        if total >= 100000:
            break

    print(f"\nTotal valid cycles with fc(1)=4: {total}")
    print(f"Residual cases: {total_residual}")
    print(f"ALL J+K<=1: {found_all_le1}")


if __name__ == "__main__":
    verify_complementary_phase()
    prove_complementary_phase_analytically()
    check_jk_ge3_gives_ec()
    check_jk_ge2_gives_ec()
    investigate_direct_mechanism()
    prove_ec_via_complementary()
    force_fc4_test()
