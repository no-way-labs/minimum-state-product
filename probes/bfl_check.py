"""
BFL (Backward-Firing-Last) sub-case investigation.

Question: In the allNormalFormFalse2 argument, does the BFL sub-case actually occur?

Setup:
- Sandwiched ternary t: both left(t) and right(t) are binary.
- All TernaryPhases at t are normalForm (not mechanism-triggering).
- A one-sided phase (J=1,K=0 or J=0,K=1) with length >= 2.
- BFL occurs when left2t (or right2t) fires within such a phase.

We check: across all sub-threshold systems with >=3 binary at n=5,6,7,
do any normalForm phases have second-neighbor fires?
"""

import itertools
import sys
from collections import defaultdict

sys.path.insert(0, './claude')
from verifier import verify_system, all_configs, privileged_set, apply_move


def get_threshold(n):
    """Sub-threshold product bound: 4 * 3^(n-2)."""
    return 4 * (3 ** (n - 2))


def get_candidate_ms(n, max_product):
    """Generate all state vectors with >=3 binary, product < max_product."""
    # Each m_i >= 2. At least 3 must be 2 (binary).
    # Product < max_product.
    results = []
    # Max state per proc: limited by product
    max_m = max_product

    def generate(pos, remaining_product, current_ms, n_binary):
        if pos == n:
            if n_binary >= 3 and remaining_product > 0:
                results.append(tuple(current_ms))
            return
        left = n - pos
        for m in range(2, max_m + 1):
            if remaining_product <= 0:
                break
            new_product = remaining_product // m if remaining_product % m == 0 else remaining_product // m
            # Check: can we still achieve product < max_product?
            # Current partial product = max_product / remaining_product * m
            # Actually, let's track the actual product
            actual = 1
            for x in current_ms:
                actual *= x
            actual *= m
            if actual >= max_product:
                break
            # Remaining procs need at least 2 each
            min_remaining = 2 ** (left - 1)
            if actual * min_remaining >= max_product:
                continue
            new_binary = n_binary + (1 if m == 2 else 0)
            # Can we still get >=3 binary?
            max_possible_binary = new_binary + (left - 1)
            if max_possible_binary < 3:
                continue
            generate(pos + 1, max_product // actual if actual > 0 else 0,
                     current_ms + [m], new_binary)

    # Simpler approach: enumerate sorted multisets, then permutations
    from math import prod as mprod

    def gen_sorted(pos, min_val, current, product_so_far):
        if pos == n:
            if product_so_far < max_product:
                binary_count = sum(1 for x in current if x == 2)
                if binary_count >= 3:
                    results.append(tuple(current))
            return
        left = n - pos
        for m in range(min_val, max_product + 1):
            new_prod = product_so_far * m
            # Remaining procs have m >= m, so product >= new_prod * m^(left-1)
            if new_prod * (m ** (left - 1)) >= max_product:
                break
            gen_sorted(pos + 1, m, current + [m], new_prod)

    gen_sorted(0, 2, [], 1)
    return results


def get_all_orientations(ms_sorted):
    """Get all distinct circular orientations of a sorted multiset."""
    from itertools import permutations
    n = len(ms_sorted)
    seen = set()
    results = []
    for perm in permutations(ms_sorted):
        # Canonical: minimum rotation
        rotations = []
        for i in range(n):
            rotations.append(tuple(perm[i:] + perm[:i]))
        canon = min(rotations)
        if canon not in seen:
            seen.add(canon)
            results.append(list(perm))
    return results


def find_sandwiched_ternary(ms):
    """Find all ternary procs with both neighbors binary."""
    n = len(ms)
    result = []
    for t in range(n):
        if ms[t] >= 3:
            bL = (t - 1) % n
            bR = (t + 1) % n
            if ms[bL] == 2 and ms[bR] == 2:
                result.append(t)
    return result


def build_incrementing_system(ms):
    """Build system with incrementing transitions: f(L,S,R) = (S+1) % m."""
    n = len(ms)
    fs = []
    for i in range(n):
        m = ms[i]
        def make_f(m_i):
            return lambda L, S, R: (S + 1) % m_i
        fs.append(make_f(m))
    return fs


def build_all_transition_modes(ms):
    """For each proc, build inc and dec transition functions.

    At minimum fire count, each proc fires exactly m_p times.
    For binary: only inc (0->1->0).
    For ternary: inc (0->1->2->0) or dec (0->2->1->0).
    """
    n = len(ms)
    # For each ternary proc, 2 modes. Binary has only 1 mode.
    ternary_indices = [i for i in range(n) if ms[i] >= 3]
    binary_indices = [i for i in range(n) if ms[i] == 2]

    def make_inc(m):
        return lambda L, S, R: (S + 1) % m

    def make_dec(m):
        return lambda L, S, R: (S - 1) % m

    # Enumerate all mode combos for ternary procs
    num_ternary = len(ternary_indices)
    for mode_bits in range(2 ** num_ternary):
        fs = [None] * n
        for i in binary_indices:
            fs[i] = make_inc(ms[i])
        for j, ti in enumerate(ternary_indices):
            if (mode_bits >> j) & 1 == 0:
                fs[ti] = make_inc(ms[ti])
            else:
                fs[ti] = make_dec(ms[ti])
        yield fs


def extract_good_cycle_movers(ms, fs, result):
    """Extract the good cycle and its mover sequence."""
    if not result['valid']:
        return None, None
    cycle = result['cycle']
    n = len(ms)
    movers = []
    for config in cycle:
        priv = privileged_set(config, fs, ms)
        assert len(priv) == 1
        movers.append(priv[0])
    return cycle, movers


def extract_ternary_phases(movers, t, cycle_len):
    """Extract all TernaryPhases for proc t from the mover sequence.

    A TernaryPhase [a, s) is: t fires at step s, doesn't fire in (a, s).
    a is the previous step where we anchor (could be a t-fire or start).

    More precisely: find all consecutive t-fires. Between fire i and fire i+1,
    there's a phase [fire_i, fire_{i+1}).
    """
    # Find all steps where t fires
    t_fires = [i for i, m in enumerate(movers) if m == t]
    if len(t_fires) < 2:
        return []

    phases = []
    for idx in range(len(t_fires)):
        a = t_fires[idx]
        s = t_fires[(idx + 1) % len(t_fires)]
        if s <= a:
            s += cycle_len  # wrap around
        # Phase is (a, s]: t fires at a and s, doesn't fire in (a, s)
        # In the Lean definition: a is the anchor (step a), s is the next t-fire
        # TernaryPhase has a.val < s.val, moverAt s = t, moverAt a != t...
        # Actually in Lean, 'a' is NOT a t-fire; it's just any earlier step.
        # But for phase extraction, the natural partition is between consecutive t-fires.
        # The phase is [a+1, s] with t firing at s and not in [a+1, s-1].
        # Let's store (a, s) meaning: anchor at step a (a t-fire), next t-fire at s.
        # The gap interval is (a, s) = steps a+1, a+2, ..., s-1.
        phases.append((a, s))

    return phases


def check_phase_normal_form(movers, t, a, s, ms, cycle_len):
    """Check if a phase (a, s) between consecutive t-fires is normalForm.

    Phase interval: steps a+1, ..., s-1 (t doesn't fire here).
    Step s: t fires.

    J = number of left(t) fires in (a, s) exclusive = steps a+1..s-1
    K = number of right(t) fires in (a, s) exclusive = steps a+1..s-1

    normalForm = NOT mechanism-triggering:
    - NOT (Even(J) AND Even(K))       -- BothEven
    - NOT (J >= 2 AND K == 0)         -- ToggleFR-left
    - NOT (J == 0 AND K >= 2)         -- ToggleFR-right

    Returns (is_normal, J, K, phase_length)
    """
    n = len(ms)
    bL = (t - 1) % n
    bR = (t + 1) % n

    J = 0  # fires of left(t) in (a, s)
    K = 0  # fires of right(t) in (a, s)

    for step in range(a + 1, s):
        actual_step = step % cycle_len
        mover = movers[actual_step]
        if mover == bL:
            J += 1
        if mover == bR:
            K += 1

    phase_length = s - a - 1  # number of steps in the gap (a+1 to s-1)

    # Check mechanism-triggering conditions
    both_even = (J % 2 == 0) and (K % 2 == 0)
    toggle_left = (J >= 2) and (K == 0)
    toggle_right = (J == 0) and (K >= 2)

    is_normal = not (both_even or toggle_left or toggle_right)

    return is_normal, J, K, phase_length


def check_bfl_in_phase(movers, t, a, s, ms, cycle_len):
    """Check if left2t or right2t fires in a one-sided normalForm phase.

    Returns dict with details if BFL occurs, None otherwise.
    """
    n = len(ms)
    bL = (t - 1) % n
    bR = (t + 1) % n
    left2t = (t - 2) % n
    right2t = (t + 2) % n

    is_normal, J, K, phase_length = check_phase_normal_form(
        movers, t, a, s, ms, cycle_len)

    if not is_normal:
        return None

    # Check one-sided with length >= 2
    is_one_sided_left = (J == 1 and K == 0)
    is_one_sided_right = (J == 0 and K == 1)

    if not (is_one_sided_left or is_one_sided_right):
        return None

    if phase_length < 2:
        return None

    # Now check for second-neighbor fires in the gap (a+1, ..., s-1)
    left2t_fires = []
    right2t_fires = []

    for step in range(a + 1, s):
        actual_step = step % cycle_len
        mover = movers[actual_step]
        if mover == left2t:
            left2t_fires.append(step)
        if mover == right2t:
            right2t_fires.append(step)

    has_bfl = False
    bfl_details = {}

    if is_one_sided_left and len(left2t_fires) > 0:
        has_bfl = True
        bfl_details = {
            'side': 'left',
            'second_neighbor': left2t,
            'second_neighbor_fires': left2t_fires,
        }

    if is_one_sided_right and len(right2t_fires) > 0:
        has_bfl = True
        bfl_details = {
            'side': 'right',
            'second_neighbor': right2t,
            'second_neighbor_fires': right2t_fires,
        }

    if has_bfl:
        return {
            'ternary_t': t,
            'phase': (a, s),
            'J': J,
            'K': K,
            'phase_length': phase_length,
            **bfl_details,
        }

    return None


def main():
    total_systems = 0
    total_valid = 0
    total_phases_checked = 0
    total_normal_one_sided_long = 0
    total_bfl = 0
    bfl_examples = []

    # Also track: how many normalForm one-sided phases exist at all
    # (even without BFL)

    for n in [5, 6, 7]:
        threshold = get_threshold(n)
        print(f"\n{'='*60}")
        print(f"n={n}, threshold={threshold}")
        print(f"{'='*60}")

        # Get sorted multisets
        multisets = get_candidate_ms(n, threshold)
        print(f"Found {len(multisets)} sorted multisets with product < {threshold}")

        n_systems_n = 0
        n_valid_n = 0
        n_phases_n = 0
        n_normal_one_sided_long_n = 0
        n_bfl_n = 0

        for ms_sorted in multisets:
            # Get all orientations
            orientations = get_all_orientations(ms_sorted)

            for ms in orientations:
                # Find sandwiched ternary procs
                sand_ternary = find_sandwiched_ternary(ms)
                if not sand_ternary:
                    continue

                # Try all transition modes
                for fs in build_all_transition_modes(ms):
                    n_systems_n += 1

                    try:
                        result = verify_system(ms, fs)
                    except Exception:
                        continue

                    if not result['valid']:
                        continue

                    n_valid_n += 1
                    cycle, movers = extract_good_cycle_movers(ms, fs, result)
                    if cycle is None:
                        continue

                    cycle_len = len(cycle)

                    for t in sand_ternary:
                        phases = extract_ternary_phases(movers, t, cycle_len)

                        # Check: are ALL phases normalForm?
                        all_normal = True
                        for (a, s) in phases:
                            is_norm, J, K, plen = check_phase_normal_form(
                                movers, t, a, s, ms, cycle_len)
                            if not is_norm:
                                all_normal = False
                                break

                        if not all_normal:
                            continue

                        # All phases are normalForm. Check each for BFL.
                        for (a, s) in phases:
                            n_phases_n += 1

                            is_norm, J, K, plen = check_phase_normal_form(
                                movers, t, a, s, ms, cycle_len)

                            # Is it one-sided with length >= 2?
                            is_one_sided = ((J == 1 and K == 0) or
                                          (J == 0 and K == 1))
                            if is_one_sided and plen >= 2:
                                n_normal_one_sided_long_n += 1

                                bfl = check_bfl_in_phase(
                                    movers, t, a, s, ms, cycle_len)
                                if bfl is not None:
                                    n_bfl_n += 1
                                    if len(bfl_examples) < 10:
                                        bfl_examples.append({
                                            'n': n,
                                            'ms': ms,
                                            'cycle_len': cycle_len,
                                            **bfl,
                                        })

        print(f"Systems checked: {n_systems_n}")
        print(f"Valid systems: {n_valid_n}")
        print(f"Phases in all-normalForm contexts: {n_phases_n}")
        print(f"One-sided normalForm phases with length >= 2: {n_normal_one_sided_long_n}")
        print(f"BFL occurrences (second-neighbor fires): {n_bfl_n}")

        total_systems += n_systems_n
        total_valid += n_valid_n
        total_phases_checked += n_phases_n
        total_normal_one_sided_long += n_normal_one_sided_long_n
        total_bfl += n_bfl_n

    print(f"\n{'='*60}")
    print(f"TOTALS")
    print(f"{'='*60}")
    print(f"Total systems checked: {total_systems}")
    print(f"Total valid systems: {total_valid}")
    print(f"Total phases (all-normalForm context): {total_phases_checked}")
    print(f"Total one-sided normalForm with length >= 2: {total_normal_one_sided_long}")
    print(f"Total BFL occurrences: {total_bfl}")

    if total_bfl == 0:
        print(f"\n*** BFL appears VACUOUS: no second-neighbor fires in any ***")
        print(f"*** normalForm one-sided phase with length >= 2.          ***")
    else:
        print(f"\n*** BFL IS NON-VACUOUS: {total_bfl} occurrences found ***")
        for ex in bfl_examples:
            print(f"\nExample: n={ex['n']}, ms={ex['ms']}")
            print(f"  t={ex['ternary_t']}, phase=({ex['phase'][0]}, {ex['phase'][1]})")
            print(f"  J={ex['J']}, K={ex['K']}, length={ex['phase_length']}")
            print(f"  side={ex['side']}, second_neighbor={ex['second_neighbor']}")
            print(f"  second_neighbor_fires_at={ex['second_neighbor_fires']}")


if __name__ == '__main__':
    main()
