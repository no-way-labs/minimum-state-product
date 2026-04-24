#!/usr/bin/env python3
"""n8_n9_nonincrement.py — Check whether M_8=2592 witness uses non-incrementing transitions.

KEY INSIGHT from previous analysis:
- With incrementing transitions, EC seems unavoidable at n>=7 for 3-binary+quat.
- But M_8=2592 exists! So either:
  (a) Non-incrementing transitions at some procs avoid the EC, or
  (b) The valid system has a different ms arrangement (rotation matters), or
  (c) EC at some procs can be tolerated if convergence still works.

Wait -- EC means the SAME context appears as both mover and nonmover.
If so, the transition function must output BOTH "change state" (mover) and
"keep state" (nonmover) for the same input. Contradiction! EC means NO
transition function can work.

So if M_8=2592 is achievable with ms=(2,2,2,3,4,3,3,3), either:
- There's a cycle that avoids EC at ALL procs, possibly with non-incrementing transitions
- Or the ms arrangement matters (where we put the binary/quat procs)

Let's check all rotations/reflections of (2,2,2,3,4,3,3,3).
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian, permutations
from collections import defaultdict
from math import prod, factorial

def build_cycle_from_mover_word(n, ms, movers, start=None):
    """Build cycle with incrementing transitions."""
    if start is None:
        start = tuple([0] * n)
    config = list(start)
    cycle = [tuple(config)]
    for mv in movers:
        config = list(cycle[-1])
        config[mv] = (config[mv] + 1) % ms[mv]
        nc = tuple(config)
        cycle.append(nc)
    if cycle[-1] != cycle[0]:
        return None
    return cycle[:-1]


def check_entry_conflicts(n, ms, cycle, movers):
    """Check entry conflicts."""
    CL = len(cycle)
    mover_ctx = defaultdict(set)
    nonmover_ctx = defaultdict(set)
    for idx in range(CL):
        c = cycle[idx]
        mv = movers[idx]
        for p in range(n):
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            ctx = (L, S, R)
            if p == mv:
                mover_ctx[p].add(ctx)
            else:
                nonmover_ctx[p].add(ctx)
    conflicts = {}
    total = 0
    for p in range(n):
        overlap = mover_ctx[p] & nonmover_ctx[p]
        conflicts[p] = overlap
        total += len(overlap)
    return conflicts, total


def check_all_arrangements(n, base_multiset):
    """Check all distinct ring arrangements of the multiset.

    A ring arrangement is an equivalence class under rotation and reflection.
    For now, just check all distinct tuples (overcounting but correct).
    """
    from itertools import permutations as perms

    seen = set()
    arrangements = []

    for perm in perms(base_multiset):
        # Normalize: smallest rotation
        rotations = []
        for r in range(n):
            rotated = perm[r:] + perm[:r]
            rotations.append(rotated)
            # Also reflection
            reflected = tuple(reversed(perm))
            rotated_ref = reflected[r:] + reflected[:r]
            rotations.append(rotated_ref)
        canonical = min(rotations)
        if canonical not in seen:
            seen.add(canonical)
            arrangements.append(perm)

    return arrangements


def sweep_cycle(n, ms, direction='CW'):
    """Build sweep cycle."""
    CL = sum(ms)
    movers = []
    counts = [0] * n
    if direction == 'CW':
        seq = list(range(n))
    else:
        seq = list(range(n-1, -1, -1))
    idx = 0
    while len(movers) < CL:
        p = seq[idx % n]
        if counts[p] < ms[p]:
            movers.append(p)
            counts[p] += 1
        idx += 1
        if idx > CL * n:
            break
    return movers


def large_sample_ec_check(n, ms, num_samples=5000):
    """Sample many random mover words and check EC."""
    import random
    random.seed(42)

    CL = sum(ms)
    base = []
    for p in range(n):
        base.extend([p] * ms[p])

    ec_free = 0
    total = 0
    min_conflicts = float('inf')
    best_word = None

    for _ in range(num_samples):
        perm = list(base)
        random.shuffle(perm)
        cycle = build_cycle_from_mover_word(n, ms, perm)
        if cycle is None:
            continue
        _, conf = check_entry_conflicts(n, ms, cycle, perm)
        total += 1
        if conf == 0:
            ec_free += 1
        if conf < min_conflicts:
            min_conflicts = conf
            best_word = list(perm)

    return total, ec_free, min_conflicts, best_word


def check_decrementing_transitions(n, ms, movers):
    """Build cycle where some procs use decrementing transitions.

    For a proc with m_p states and decrementing: state goes (0 -> m_p-1 -> m_p-2 -> ... -> 1 -> 0).
    Each proc can independently be incrementing or decrementing.
    Total modes = 2^n.
    """
    CL = sum(ms)
    results = []

    for mode_mask in range(1 << n):
        # mode_mask bit p = 0: incrementing, 1: decrementing
        config = [0] * n
        cycle = [tuple(config)]
        valid = True
        for mv in movers:
            config = list(cycle[-1])
            if (mode_mask >> mv) & 1:
                # Decrementing
                config[mv] = (config[mv] - 1) % ms[mv]
            else:
                # Incrementing
                config[mv] = (config[mv] + 1) % ms[mv]
            nc = tuple(config)
            cycle.append(nc)

        if cycle[-1] != cycle[0]:
            continue

        cycle = cycle[:-1]
        if len(set(cycle)) != len(cycle):
            continue  # Not a simple cycle

        _, total_ec = check_entry_conflicts(n, ms, cycle, movers)
        mode_str = ''.join('D' if (mode_mask >> p) & 1 else 'I' for p in range(n))
        results.append((mode_str, total_ec))

    return results


if __name__ == "__main__":
    import random
    random.seed(42)

    # ================================================================
    # PART 1: Check all ring arrangements at n=8
    # ================================================================
    print("=" * 70)
    print("PART 1: All ring arrangements of {2,2,2,3,4,3,3,3} at n=8")
    print("=" * 70)

    n = 8
    base = (2, 2, 2, 3, 4, 3, 3, 3)
    arrangements = check_all_arrangements(n, base)
    print(f"Distinct ring arrangements: {len(arrangements)}")

    # For each arrangement, check EC with CW sweep, CCW sweep, and random sample
    best_overall = float('inf')
    best_arr = None

    for arr in arrangements:
        ms = arr
        cw = sweep_cycle(n, ms, 'CW')
        ccw = sweep_cycle(n, ms, 'CCW')

        cw_cycle = build_cycle_from_mover_word(n, ms, cw)
        ccw_cycle = build_cycle_from_mover_word(n, ms, ccw)

        cw_ec = check_entry_conflicts(n, ms, cw_cycle, cw)[1] if cw_cycle else 999
        ccw_ec = check_entry_conflicts(n, ms, ccw_cycle, ccw)[1] if ccw_cycle else 999

        # Small random sample
        _, _, rand_min_ec, _ = large_sample_ec_check(n, ms, num_samples=200)

        best_for_arr = min(cw_ec, ccw_ec, rand_min_ec)
        if best_for_arr < best_overall:
            best_overall = best_for_arr
            best_arr = arr

        if best_for_arr <= 2:
            print(f"  ms={arr}: CW_EC={cw_ec}, CCW_EC={ccw_ec}, rand_min={rand_min_ec} {'<-- LOW' if best_for_arr == 0 else ''}")

    print(f"\nBest overall: {best_overall} conflicts, arrangement={best_arr}")

    # ================================================================
    # PART 2: Non-incrementing transitions
    # ================================================================
    print("\n" + "=" * 70)
    print("PART 2: Non-incrementing (inc/dec) transitions")
    print("=" * 70)

    # At n=5, check all inc/dec modes for the CW sweep
    n = 5
    ms = (2, 2, 2, 3, 4)
    cw = sweep_cycle(n, ms, 'CW')
    print(f"\nn=5, ms={ms}, CW sweep: {cw}")
    results = check_decrementing_transitions(n, ms, cw)
    ec_free_modes = [(m, ec) for m, ec in results if ec == 0]
    print(f"  Total valid modes: {len(results)}")
    print(f"  EC-free modes: {len(ec_free_modes)}")
    for m, ec in results[:20]:
        print(f"    mode={m}, EC={ec}")

    # At n=8, try various mover words with all inc/dec modes
    print(f"\nn=8 with inc/dec modes:")
    n = 8
    ms_choices = [
        (2, 2, 2, 3, 4, 3, 3, 3),
        (2, 3, 2, 3, 4, 3, 2, 3),  # spread binary
        (3, 2, 3, 2, 4, 3, 2, 3),  # another arrangement
    ]

    for ms in ms_choices:
        CL = sum(ms)
        cw = sweep_cycle(n, ms, 'CW')
        ccw = sweep_cycle(n, ms, 'CCW')

        print(f"\n  ms={ms}, CL={CL}")
        for name, movers in [('CW', cw), ('CCW', ccw)]:
            results = check_decrementing_transitions(n, ms, movers)
            ec_free = [(m, ec) for m, ec in results if ec == 0]
            min_ec = min(ec for _, ec in results) if results else 999
            print(f"    {name}: {len(results)} valid modes, {len(ec_free)} EC-free, min_EC={min_ec}")
            if ec_free:
                for m, ec in ec_free[:3]:
                    print(f"      EC-FREE mode={m}")

    # ================================================================
    # PART 3: The definitive test — enumerate at n=5 with ALL modes
    # ================================================================
    print("\n" + "=" * 70)
    print("PART 3: n=5 exhaustive inc/dec sweep")
    print("=" * 70)

    n = 5
    ms = (2, 2, 2, 3, 4)
    CL = sum(ms)  # 13

    # Sample mover words, check all 2^5=32 inc/dec modes for each
    base = []
    for p in range(n):
        base.extend([p] * ms[p])

    ec_free_count = 0
    total_tested = 0

    for trial in range(10000):
        perm = list(base)
        random.shuffle(perm)

        for mode_mask in range(1 << n):
            config = [0] * n
            cycle = [tuple(config)]
            for mv in perm:
                config = list(cycle[-1])
                if (mode_mask >> mv) & 1:
                    config[mv] = (config[mv] - 1) % ms[mv]
                else:
                    config[mv] = (config[mv] + 1) % ms[mv]
                cycle.append(tuple(config))

            if cycle[-1] != cycle[0]:
                continue
            cycle = cycle[:-1]
            if len(set(cycle)) != len(cycle):
                continue

            _, ec_total = check_entry_conflicts(n, ms, cycle, perm)
            total_tested += 1
            if ec_total == 0:
                ec_free_count += 1

    print(f"n={n}: tested {total_tested} (word, mode) combos, {ec_free_count} EC-free")
    print(f"EC-free fraction: {ec_free_count/total_tested:.6f}" if total_tested > 0 else "No valid combos")

    # ================================================================
    # PART 4: Same for n=8
    # ================================================================
    print("\n" + "=" * 70)
    print("PART 4: n=8 inc/dec sweep")
    print("=" * 70)

    n = 8
    ms = (2, 2, 2, 3, 4, 3, 3, 3)
    CL = sum(ms)  # 22
    base = []
    for p in range(n):
        base.extend([p] * ms[p])

    ec_free_count = 0
    total_tested = 0
    min_ec_found = float('inf')

    for trial in range(2000):
        perm = list(base)
        random.shuffle(perm)

        for mode_mask in range(1 << n):
            config = [0] * n
            cycle = [tuple(config)]
            for mv in perm:
                config = list(cycle[-1])
                if (mode_mask >> mv) & 1:
                    config[mv] = (config[mv] - 1) % ms[mv]
                else:
                    config[mv] = (config[mv] + 1) % ms[mv]
                cycle.append(tuple(config))

            if cycle[-1] != cycle[0]:
                continue
            cycle = cycle[:-1]
            if len(set(cycle)) != len(cycle):
                continue

            _, ec_total = check_entry_conflicts(n, ms, cycle, perm)
            total_tested += 1
            if ec_total == 0:
                ec_free_count += 1
                if ec_free_count <= 3:
                    mode_str = ''.join('D' if (mode_mask >> p) & 1 else 'I' for p in range(n))
                    print(f"  EC-FREE at n=8! word={perm}, mode={mode_str}")
            if ec_total < min_ec_found:
                min_ec_found = ec_total

    print(f"n={n}: tested {total_tested}, {ec_free_count} EC-free, min_EC={min_ec_found}")

    # ================================================================
    # PART 5: Critical — check ALL arrangements at n=8 more thoroughly
    # ================================================================
    print("\n" + "=" * 70)
    print("PART 5: All arrangements at n=8 with inc/dec, larger sample")
    print("=" * 70)

    n = 8
    base_multiset = (2, 2, 2, 3, 4, 3, 3, 3)
    arrangements = check_all_arrangements(n, base_multiset)

    for arr in arrangements:
        ms = arr
        CL = sum(ms)
        base_word = []
        for p in range(n):
            base_word.extend([p] * ms[p])

        ec_free_count = 0
        total_tested = 0
        min_ec = float('inf')

        for trial in range(500):
            perm = list(base_word)
            random.shuffle(perm)
            for mode_mask in range(1 << n):
                config = [0] * n
                cycle = [tuple(config)]
                for mv in perm:
                    config = list(cycle[-1])
                    if (mode_mask >> mv) & 1:
                        config[mv] = (config[mv] - 1) % ms[mv]
                    else:
                        config[mv] = (config[mv] + 1) % ms[mv]
                    cycle.append(tuple(config))

                if cycle[-1] != cycle[0]:
                    continue
                cycle = cycle[:-1]
                if len(set(cycle)) != len(cycle):
                    continue

                _, ec_total = check_entry_conflicts(n, ms, cycle, perm)
                total_tested += 1
                if ec_total == 0:
                    ec_free_count += 1
                if ec_total < min_ec:
                    min_ec = ec_total

        if ec_free_count > 0 or min_ec <= 2:
            print(f"  ms={arr}: tested {total_tested}, EC-free={ec_free_count}, min_EC={min_ec}")

    print("\nDone.")
