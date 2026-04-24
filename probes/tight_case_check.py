#!/usr/bin/env python3
"""
Check whether the "tight case" in within-phase entry conflict survives
binary recovery.

Key insight for speed: instead of enumerating all permutations, we use
the combinatorial structure. For a phase with events L (left_t), G (left²t),
R (right_t), H (right²t), we need to check if there EXISTS an ordering
where NEITHER left_t NOR right_t gets entry conflict.

Entry conflict at left_t: the (config[left²t], config[left_t]) pair at a
left_t mover step matches that pair at some non-left_t step. Since both
are binary, there are only 4 possible pairs. We track which pairs appear
at L-firing steps vs non-L steps.

For the adversary to AVOID EC at left_t: the set of (a,b) pairs at L-firings
must be disjoint from the set at non-{L,G} steps AND the set at G steps.
Wait -- G steps also change config[left²t], so the pair AT the G step (pre-step)
is different from after.

Let me think carefully:
- At each step, the boundary triple at left_t is (config[left²t], config[left_t], config[t]).
- config[t] is constant, so we only track (a, b) = (config[left²t], config[left_t]).
- Before any event: (a, b) = initial values, WLOG (0, 0).
- L event: left_t fires. Pre-step pair is (a, b). Post: b flips.
- G event: left²t fires. Pre-step pair is (a, b). Post: a flips.
- R or H event: neither changes. Pre-step pair is (a, b).

EC at left_t: some L step has pre-pair (a, b), AND some non-L step also
has pre-pair (a, b).

The adversary controls the ordering of {L^Ji, G^gi, R^Ki, H^hi}.
Starting from (0,0), each ordering determines a sequence of (a,b) pairs.
EC at left_t iff L-pairs intersect non-L-pairs.

Similarly for right_t with (d, e) = (config[right²t], config[right_t]):
- R event: e flips.
- H event: d flips.
- L or G event: neither changes.
EC at right_t iff R-pairs intersect non-R-pairs.

For the adversary to WIN (avoid all EC): need an ordering where
L-pairs are disjoint from non-L-pairs AND R-pairs are disjoint from non-R-pairs.

We can enumerate this efficiently by tracking the joint state (a, b, d, e)
and doing DFS over all possible next-event choices.
"""

from itertools import product as iterproduct
from functools import lru_cache

def is_normal_form(J, K):
    """(J,K) not in forbidden set."""
    if J % 2 == 0 and K % 2 == 0:
        return False
    if J >= 2 and K == 0:
        return False
    if J == 0 and K >= 2:
        return False
    return True

def phase_avoids_ec(Ji, Ki, gi, hi):
    """
    Check if the adversary can order Ji L's, gi G's, Ki R's, hi H's
    such that:
    - No (a,b) pair appears at both an L step and a non-L step
    - No (d,e) pair appears at both an R step and a non-R step

    Returns True if adversary CAN avoid EC (i.e., phase survives).

    Uses DFS with memoization on (state, remaining counts, L-pair-set, R-pair-set,
    non-L-pair-set, non-R-pair-set).
    """
    # State: (a, b, d, e, remaining_L, remaining_G, remaining_R, remaining_H,
    #         L_pairs_mask, nonL_pairs_mask, R_pairs_mask, nonR_pairs_mask)
    # pairs encoded as 2-bit: (x,y) -> 2*x + y, mask is 4-bit

    # DFS with memoization
    # State space: 2^4 * (Ji+1) * (gi+1) * (Ki+1) * (hi+1) * 4^4
    # = 16 * counts * 256 which can be large but manageable for small counts.

    # For large counts, we need a smarter approach. But let's try.

    if Ji + Ki + gi + hi == 0:
        return True  # no events, no EC

    # Optimization: if Ji == 0 and Ki == 0, no mover steps, no EC possible
    if Ji == 0 and Ki == 0:
        return True

    from functools import lru_cache

    @lru_cache(maxsize=None)
    def dfs(a, b, d, e, rL, rG, rR, rH, Lmask, nLmask, Rmask, nRmask):
        """Returns True if adversary can avoid EC from this state."""
        if rL + rG + rR + rH == 0:
            return True  # done, no conflict found

        pair_ab = 2 * a + b
        pair_de = 2 * d + e

        # Try each possible next event
        # L event: left_t fires
        if rL > 0:
            # L step sees pair (a,b). Check if this conflicts with existing non-L pairs.
            new_Lmask = Lmask | (1 << pair_ab)
            if not (new_Lmask & nLmask):  # no conflict at left_t
                # For right_t: L is a non-R step, sees pair (d,e)
                new_nRmask = nRmask | (1 << pair_de)
                if not (Rmask & new_nRmask):  # no conflict at right_t
                    if dfs(a, 1-b, d, e, rL-1, rG, rR, rH,
                           new_Lmask, nLmask, Rmask, new_nRmask):
                        return True

        # G event: left²t fires
        if rG > 0:
            # G is non-L step, sees (a,b)
            new_nLmask = nLmask | (1 << pair_ab)
            if not (Lmask & new_nLmask):
                # G is non-R step, sees (d,e)
                new_nRmask = nRmask | (1 << pair_de)
                if not (Rmask & new_nRmask):
                    if dfs(1-a, b, d, e, rL, rG-1, rR, rH,
                           Lmask, new_nLmask, Rmask, new_nRmask):
                        return True

        # R event: right_t fires
        if rR > 0:
            # R is non-L step, sees (a,b)
            new_nLmask = nLmask | (1 << pair_ab)
            if not (Lmask & new_nLmask):
                # R step sees (d,e)
                new_Rmask = Rmask | (1 << pair_de)
                if not (new_Rmask & nRmask):
                    if dfs(a, b, d, 1-e, rL, rG, rR-1, rH,
                           Lmask, new_nLmask, new_Rmask, nRmask):
                        return True

        # H event: right²t fires
        if rH > 0:
            # H is non-L step, sees (a,b)
            new_nLmask = nLmask | (1 << pair_ab)
            if not (Lmask & new_nLmask):
                # H is non-R step, sees (d,e)
                new_nRmask = nRmask | (1 << pair_de)
                if not (Rmask & new_nRmask):
                    if dfs(a, b, 1-d, e, rL, rG, rR, rH-1,
                           Lmask, new_nLmask, Rmask, new_nRmask):
                        return True

        return False

    result = dfs(0, 0, 0, 0, Ji, gi, Ki, hi, 0, 0, 0, 0)
    dfs.cache_clear()
    return result

def main():
    MAX_J = 8
    MAX_K = 8

    valid_assignments = []

    for J1 in range(MAX_J + 1):
        for J2 in range(MAX_J + 1):
            J_total = J1 + J2
            if J_total < 2 or J_total % 2 != 0:
                continue
            for K1 in range(MAX_K + 1):
                for K2 in range(MAX_K + 1):
                    K_total = K1 + K2
                    if K_total < 2 or K_total % 2 != 0:
                        continue
                    if not is_normal_form(J1, K1):
                        continue
                    if not is_normal_form(J2, K2):
                        continue
                    for g1 in range(3):
                        g2 = 2 - g1
                        for h1 in range(3):
                            h2 = 2 - h1
                            valid_assignments.append((J1, K1, g1, h1, J2, K2, g2, h2))

    print(f"Total valid assignments: {len(valid_assignments)}")

    # For each assignment, check BOTH phases.
    # An assignment is CLOSED if at least one phase has EC (adversary cannot avoid).
    # An assignment SURVIVES if BOTH phases can avoid EC.

    survivors = []
    closed = 0
    phase_results = {}

    # Cache phase results to avoid recomputation
    phase_cache = {}

    for idx, asgn in enumerate(valid_assignments):
        J1, K1, g1, h1, J2, K2, g2, h2 = asgn

        key1 = (J1, K1, g1, h1)
        key2 = (J2, K2, g2, h2)

        if key1 not in phase_cache:
            phase_cache[key1] = phase_avoids_ec(*key1)
        if key2 not in phase_cache:
            phase_cache[key2] = phase_avoids_ec(*key2)

        p1_survives = phase_cache[key1]
        p2_survives = phase_cache[key2]

        if p1_survives and p2_survives:
            survivors.append(asgn)
        else:
            closed += 1

    print(f"Closed: {closed}")
    print(f"Survivors: {len(survivors)}")

    # Analyze survivors
    # Group by (J_total, K_total)
    from collections import Counter
    jk_counts = Counter()
    for asgn in survivors:
        J1, K1, g1, h1, J2, K2, g2, h2 = asgn
        jk_counts[(J1+J2, K1+K2)] += 1

    print(f"\nSurvivor (J_total, K_total) distribution:")
    for (jt, kt), cnt in sorted(jk_counts.items()):
        print(f"  J_total={jt}, K_total={kt}: {cnt}")

    # Show all survivors with small J_total + K_total
    print(f"\nAll survivors with J_total + K_total <= 6:")
    for asgn in survivors:
        J1, K1, g1, h1, J2, K2, g2, h2 = asgn
        if J1+J2 + K1+K2 <= 6:
            print(f"  (J1={J1},K1={K1},g1={g1},h1={h1}) (J2={J2},K2={K2},g2={g2},h2={h2})")

    # The critical question: do ALL survivors have J1=1 in some phase?
    print(f"\nChecking structural patterns in survivors:")
    all_have_Ji1 = True
    all_have_Ki1 = True
    for asgn in survivors:
        J1, K1, g1, h1, J2, K2, g2, h2 = asgn
        if not (J1 == 1 or J2 == 1):
            all_have_Ji1 = False
        if not (K1 == 1 or K2 == 1):
            all_have_Ki1 = False

    print(f"  Every survivor has Ji=1 in some phase (left): {all_have_Ji1}")
    print(f"  Every survivor has Ki=1 in some phase (right): {all_have_Ki1}")

    # Check the minimal survivor
    print(f"\nMinimal survivors (J_total=2, K_total=2):")
    for asgn in survivors:
        J1, K1, g1, h1, J2, K2, g2, h2 = asgn
        if J1+J2 == 2 and K1+K2 == 2:
            print(f"  (J1={J1},K1={K1},g1={g1},h1={h1}) (J2={J2},K2={K2},g2={g2},h2={h2})")

    # For the key survivor (1,1,1,1,1,1,1,1), show the witness ordering
    print(f"\nDetailed witness for (1,1,1,1,1,1,1,1):")
    print(f"  Phase avoids EC: {phase_avoids_ec(1,1,1,1)}")

    # Show ALL orderings for (1,1,1,1) and their EC status
    from itertools import permutations
    events = ['L', 'G', 'R', 'H']
    print(f"  All 24 orderings of (L,G,R,H):")
    for perm in permutations(events):
        a, b, d, e = 0, 0, 0, 0
        L_pairs = set()
        nonL_pairs = set()
        R_pairs = set()
        nonR_pairs = set()

        for ev in perm:
            pair_ab = (a, b)
            pair_de = (d, e)

            if ev == 'L':
                L_pairs.add(pair_ab)
                nonR_pairs.add(pair_de)
                b = 1 - b
            elif ev == 'G':
                nonL_pairs.add(pair_ab)
                nonR_pairs.add(pair_de)
                a = 1 - a
            elif ev == 'R':
                nonL_pairs.add(pair_ab)
                R_pairs.add(pair_de)
                e = 1 - e
            elif ev == 'H':
                nonL_pairs.add(pair_ab)
                nonR_pairs.add(pair_de)
                d = 1 - d

        left_ec = bool(L_pairs & nonL_pairs)
        right_ec = bool(R_pairs & nonR_pairs)
        status = []
        if left_ec:
            status.append("LEFT-EC")
        if right_ec:
            status.append("RIGHT-EC")
        if not status:
            status.append("CLEAN")

        print(f"    {perm}: L={L_pairs} nL={nonL_pairs} R={R_pairs} nR={nonR_pairs} -> {', '.join(status)}")

    # === ACCOUNTING FOR OTHER PROCESSORS ===
    print()
    print("=" * 70)
    print("ACCOUNTING FOR OTHER PROCESSORS")
    print("In a real good cycle with n >= 5, there are ≥ 1 other processors")
    print("firing in each phase. These are non-{L,G,R,H} steps that contribute")
    print("to BOTH nonL and nonR pairs without changing a,b,d,e.")
    print("=" * 70)

    def phase_avoids_ec_with_others(Ji, Ki, gi, hi, num_others):
        """
        Same as phase_avoids_ec but with num_others additional 'O' events
        that don't change any of (a,b,d,e) but appear as nonL and nonR steps.
        """
        if Ji + Ki + gi + hi + num_others == 0:
            return True

        @lru_cache(maxsize=None)
        def dfs(a, b, d, e, rL, rG, rR, rH, rO, Lmask, nLmask, Rmask, nRmask):
            if rL + rG + rR + rH + rO == 0:
                return True

            pair_ab = 2 * a + b
            pair_de = 2 * d + e

            # O event: other processor fires
            if rO > 0:
                new_nLmask = nLmask | (1 << pair_ab)
                if not (Lmask & new_nLmask):
                    new_nRmask = nRmask | (1 << pair_de)
                    if not (Rmask & new_nRmask):
                        if dfs(a, b, d, e, rL, rG, rR, rH, rO-1,
                               Lmask, new_nLmask, Rmask, new_nRmask):
                            return True

            if rL > 0:
                new_Lmask = Lmask | (1 << pair_ab)
                if not (new_Lmask & nLmask):
                    new_nRmask = nRmask | (1 << pair_de)
                    if not (Rmask & new_nRmask):
                        if dfs(a, 1-b, d, e, rL-1, rG, rR, rH, rO,
                               new_Lmask, nLmask, Rmask, new_nRmask):
                            return True

            if rG > 0:
                new_nLmask = nLmask | (1 << pair_ab)
                if not (Lmask & new_nLmask):
                    new_nRmask = nRmask | (1 << pair_de)
                    if not (Rmask & new_nRmask):
                        if dfs(1-a, b, d, e, rL, rG-1, rR, rH, rO,
                               Lmask, new_nLmask, Rmask, new_nRmask):
                            return True

            if rR > 0:
                new_nLmask = nLmask | (1 << pair_ab)
                if not (Lmask & new_nLmask):
                    new_Rmask = Rmask | (1 << pair_de)
                    if not (new_Rmask & nRmask):
                        if dfs(a, b, d, 1-e, rL, rG, rR-1, rH, rO,
                               Lmask, new_nLmask, new_Rmask, nRmask):
                            return True

            if rH > 0:
                new_nLmask = nLmask | (1 << pair_ab)
                if not (Lmask & new_nLmask):
                    new_nRmask = nRmask | (1 << pair_de)
                    if not (Rmask & new_nRmask):
                        if dfs(a, b, 1-d, e, rL, rG, rR, rH-1, rO,
                               Lmask, new_nLmask, Rmask, new_nRmask):
                            return True

            return False

        result = dfs(0, 0, 0, 0, Ji, gi, Ki, hi, num_others, 0, 0, 0, 0)
        dfs.cache_clear()
        return result

    # Check the key survivor (1,1,1,1) with 1, 2, 3 other processors
    print(f"\nPhase (J=1,K=1,g=1,h=1) with extra 'other' steps:")
    for num_o in range(6):
        result = phase_avoids_ec_with_others(1, 1, 1, 1, num_o)
        print(f"  +{num_o} others: adversary can avoid = {result}")

    # Check all survivors with 1 other processor
    print(f"\nRe-checking survivors with 1 'other' processor per phase:")
    survivors_with_1 = []
    for asgn in survivors:
        J1, K1, g1, h1, J2, K2, g2, h2 = asgn
        if J1+J2+K1+K2 > 10:
            continue  # skip large for speed
        p1 = phase_avoids_ec_with_others(J1, K1, g1, h1, 1)
        p2 = phase_avoids_ec_with_others(J2, K2, g2, h2, 1)
        if p1 and p2:
            survivors_with_1.append(asgn)

    print(f"  Survivors with 1 other: {len(survivors_with_1)} (out of checked)")

    if survivors_with_1:
        print(f"  Examples:")
        for asgn in survivors_with_1[:20]:
            J1, K1, g1, h1, J2, K2, g2, h2 = asgn
            print(f"    (J1={J1},K1={K1},g1={g1},h1={h1}) (J2={J2},K2={K2},g2={g2},h2={h2})")

    # Check with 2 others
    print(f"\nRe-checking (1,1,1,1,1,1,1,1) with 2 others per phase:")
    p1 = phase_avoids_ec_with_others(1, 1, 1, 1, 2)
    p2 = phase_avoids_ec_with_others(1, 1, 1, 1, 2)
    print(f"  Phase (1,1,1,1) + 2 others: {p1}")

    # === SUMMARY ===
    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"Total valid (J,K,g,h) assignments: {len(valid_assignments)}")
    print(f"Closed by within-phase EC (no others): {closed}")
    print(f"Survivors (no others): {len(survivors)}")

    # Count unique phase types that survive
    surviving_phases = set()
    for asgn in survivors:
        J1, K1, g1, h1, J2, K2, g2, h2 = asgn
        surviving_phases.add((J1, K1, g1, h1))
        surviving_phases.add((J2, K2, g2, h2))

    print(f"\nUnique surviving phase types: {len(surviving_phases)}")
    for ph in sorted(surviving_phases):
        print(f"  J={ph[0]}, K={ph[1]}, g={ph[2]}, h={ph[3]}")

if __name__ == '__main__':
    main()
