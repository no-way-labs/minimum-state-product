"""
BFL (Backward-Firing-Last) sub-case investigation -- v2.

The LB proof shows that no valid system exists at sub-threshold product.
The allNormalFormFalse2 argument is one branch of that proof -- it assumes
ALL TernaryPhases at some sandwiched ternary t are normalForm and derives EC.

The BFL sub-case arises within that argument. To check whether it occurs,
we need to look at good cycles (mover words) where:
1. Architecture has a sandwiched ternary t (both neighbors binary)
2. ALL phases at t are normalForm
3. Some one-sided phase has length >= 2
4. Check: does left2t or right2t fire in such a phase?

Since no valid system exists, we generate ALL possible mover words
(cyclic sequences of procs) that could be good cycles, and check conditions.

Key insight: a "mover word" is a cyclic sequence where each proc fires
exactly m_p times (for minimum cycle length = product(ms)). We enumerate
these and check phase properties.

Actually, let's simplify: we don't need full system validity. We just need
to enumerate mover words and check whether the BFL pattern can occur under
the normalForm hypothesis. This is about the combinatorics of firing sequences.

For small n, we can enumerate all valid mover words exhaustively.
"""

import itertools
from collections import Counter


def get_threshold(n):
    return 4 * (3 ** (n - 2))


def find_sandwiched_ternary(ms):
    n = len(ms)
    result = []
    for t in range(n):
        if ms[t] >= 3:
            bL = (t - 1) % n
            bR = (t + 1) % n
            if ms[bL] == 2 and ms[bR] == 2:
                result.append(t)
    return result


def gen_mover_words(ms):
    """Generate all mover words where proc i fires exactly m_i times.
    Total length = sum(ms) but for token ring good cycles, length = product.
    Actually: in a good cycle, each proc fires at least once. For minimum
    cycle length systems, each fires exactly m_i times.

    Wait -- cycle length = number of good configs. Each proc fires fc(p) times.
    The key constraint is that each binary proc fires fc(bL) times where
    fc(bL) >= 2 (since m_bL = 2 and it must cycle through all states).
    Actually fc(p) >= m_p for each proc (must cycle through all m_p states).

    For minimum analysis, let's use fc(p) = m_p for each proc.
    Cycle length = sum of fire counts = sum(ms).

    Actually, that's not right either. In a good cycle the cycle length
    equals the number of good configurations. The total number of firings
    equals the cycle length (one firing per step).

    For sub-threshold analysis, the key constraint from the Lean proof is
    fc(t) >= 2 for the sandwiched ternary. Let's enumerate with fc(p) = m_p.
    """
    n = len(ms)
    total = sum(ms)

    # Build list of (proc, count) pairs
    procs_counts = [(i, ms[i]) for i in range(n)]

    # Generate all permutations of the multiset
    # E.g., ms = [2, 3, 2] -> word has 2 copies of proc 0, 3 of proc 1, 2 of proc 2
    # Use itertools approach
    elements = []
    for i, m in enumerate(ms):
        elements.extend([i] * m)

    # This can be very large. For n=5, ms=[2,2,2,3,3], total=12,
    # number of multiset permutations = 12! / (2!*2!*2!*3!*3!) = 166320
    # Manageable.

    # For larger n, we need to be more selective.
    # Use unique permutations generator
    def unique_permutations(seq):
        """Generate all unique permutations of seq."""
        if len(seq) <= 1:
            yield list(seq)
            return
        seen = set()
        for i, elem in enumerate(seq):
            if elem in seen:
                continue
            seen.add(elem)
            rest = seq[:i] + seq[i+1:]
            for perm in unique_permutations(rest):
                yield [elem] + perm

    return unique_permutations(elements)


def check_phases_at_t(word, t, ms):
    """Extract and analyze TernaryPhase structure at proc t.

    Returns:
    - phases: list of (a, s, J, K, length, is_normal, second_neighbor_fires)
    - all_normal: whether all phases are normalForm
    - bfl_phases: list of phases where BFL occurs
    """
    n = len(ms)
    CL = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n
    left2t = (t - 2) % n
    right2t = (t + 2) % n

    # Find all t-fires
    t_fires = [i for i, m in enumerate(word) if m == t]
    if len(t_fires) < 2:
        return [], True, []

    phases = []
    all_normal = True
    bfl_phases = []

    for idx in range(len(t_fires)):
        a = t_fires[idx]
        s = t_fires[(idx + 1) % len(t_fires)]
        # Handle wrap-around
        if s <= a:
            s += CL

        # Count fires in (a, s) exclusive = steps a+1, ..., s-1
        J = 0  # left(t) fires
        K = 0  # right(t) fires
        left2_fires = []
        right2_fires = []

        for step in range(a + 1, s):
            actual_step = step % CL
            mover = word[actual_step]
            if mover == bL:
                J += 1
            if mover == bR:
                K += 1
            if mover == left2t:
                left2_fires.append(step - a)  # relative position
            if mover == right2t:
                right2_fires.append(step - a)  # relative position

        phase_length = s - a - 1

        # Check normalForm
        both_even = (J % 2 == 0) and (K % 2 == 0)
        toggle_left = (J >= 2) and (K == 0)
        toggle_right = (J == 0) and (K >= 2)
        is_normal = not (both_even or toggle_left or toggle_right)

        if not is_normal:
            all_normal = False

        # Check BFL in one-sided long phases
        is_one_sided_left = (J == 1 and K == 0)
        is_one_sided_right = (J == 0 and K == 1)
        has_bfl = False

        if is_normal and phase_length >= 2:
            if is_one_sided_left and len(left2_fires) > 0:
                has_bfl = True
                bfl_phases.append({
                    'a': a % CL, 's': s % CL,
                    'J': J, 'K': K, 'length': phase_length,
                    'side': 'left', 'second_fires': left2_fires,
                })
            if is_one_sided_right and len(right2_fires) > 0:
                has_bfl = True
                bfl_phases.append({
                    'a': a % CL, 's': s % CL,
                    'J': J, 'K': K, 'length': phase_length,
                    'side': 'right', 'second_fires': right2_fires,
                })

        phases.append((a, s, J, K, phase_length, is_normal,
                       left2_fires, right2_fires, has_bfl))

    return phases, all_normal, bfl_phases


def main():
    """Check BFL occurrence across architectures and mover words."""

    results = {}

    # n=5: threshold = 108, sub-threshold with >=3 binary and sandwiched ternary
    # ms like (2,2,2,3,3) with product=36 < 108
    # But we need sandwiched ternary: t with ms[t]>=3, ms[left(t)]=ms[right(t)]=2
    # For (2,2,2,3,3): depends on orientation.

    # Let's enumerate specific architectures with sandwiched ternary
    test_cases = [
        # n=5
        (5, [2, 3, 2, 2, 3]),   # t=1: left=0(bin), right=2(bin). Product=72
        (5, [2, 3, 2, 3, 2]),   # t=1,3: sandwiched. Product=72
        (5, [3, 2, 3, 2, 2]),   # t=2 has left=1(bin), right=3(bin). Product=72
        (5, [2, 2, 3, 2, 3]),   # t=2: left=1(bin), right=3(bin). Product=72

        # n=5 with 4 binary
        (5, [2, 2, 2, 2, 3]),   # t=4: left=3(bin), right=0(bin). Product=48
        (5, [2, 3, 2, 2, 2]),   # t=1: left=0(bin), right=2(bin). Product=48

        # n=6
        (6, [2, 3, 2, 2, 3, 2]),  # t=1,4: sandwiched. Product=144
        (6, [2, 3, 2, 3, 2, 2]),  # t=1,3: sandwiched. Product=144
        (6, [2, 3, 2, 2, 2, 3]),  # t=1: sandwiched. Product=144

        # n=7
        (7, [2, 3, 2, 2, 3, 2, 2]),  # t=1,4. Product=288
    ]

    for n, ms in test_cases:
        threshold = get_threshold(n)
        from math import prod
        product = prod(ms)
        if product >= threshold:
            continue

        sand = find_sandwiched_ternary(ms)
        if not sand:
            continue

        total_words = 0
        words_all_normal = 0
        words_with_one_sided_long = 0
        words_with_bfl = 0
        bfl_examples = []

        print(f"\nms={ms}, product={product}, threshold={threshold}, "
              f"sandwiched_ternary={sand}")

        # Count expected permutations
        counts = Counter(ms)
        total_expected = 1
        denom = 1
        CL = sum(ms)
        for i in range(1, CL + 1):
            total_expected *= i
        for c in Counter(range(n) for _ in []).values():
            pass
        # Multiset permutation count
        from math import factorial
        num_perms = factorial(CL)
        for i in range(n):
            num_perms //= factorial(ms[i])
        print(f"  Cycle length = {CL}, unique mover words = {num_perms}")

        if num_perms > 500000:
            print(f"  SKIPPING: too many permutations")
            continue

        for word in gen_mover_words(ms):
            total_words += 1

            found_all_normal_at_some_t = False
            found_one_sided_long = False
            found_bfl = False

            for t in sand:
                phases, all_normal, bfl_found = check_phases_at_t(word, t, ms)
                if all_normal and phases:
                    found_all_normal_at_some_t = True

                    # Check for one-sided long phases
                    for (a, s, J, K, plen, is_norm, l2f, r2f, has_bfl) in phases:
                        if is_norm and plen >= 2:
                            is_os = (J == 1 and K == 0) or (J == 0 and K == 1)
                            if is_os:
                                found_one_sided_long = True

                    if bfl_found:
                        found_bfl = True
                        if len(bfl_examples) < 5:
                            bfl_examples.append({
                                'word': list(word),
                                't': t,
                                'bfl': bfl_found,
                            })

            if found_all_normal_at_some_t:
                words_all_normal += 1
            if found_one_sided_long:
                words_with_one_sided_long += 1
            if found_bfl:
                words_with_bfl += 1

        print(f"  Total words: {total_words}")
        print(f"  Words where all phases normalForm at some sandwiched t: "
              f"{words_all_normal}")
        print(f"  Words with one-sided long normalForm phase: "
              f"{words_with_one_sided_long}")
        print(f"  Words with BFL (second-neighbor fires): {words_with_bfl}")

        if bfl_examples:
            for ex in bfl_examples[:3]:
                print(f"  BFL Example: word={ex['word']}, t={ex['t']}")
                for bf in ex['bfl']:
                    print(f"    Phase ({bf['a']},{bf['s']}): "
                          f"J={bf['J']},K={bf['K']},len={bf['length']}, "
                          f"side={bf['side']}, 2nd-fires={bf['second_fires']}")

        results[tuple(ms)] = {
            'total': total_words,
            'all_normal': words_all_normal,
            'one_sided_long': words_with_one_sided_long,
            'bfl': words_with_bfl,
        }

    print(f"\n{'='*60}")
    print("SUMMARY")
    print(f"{'='*60}")
    total_bfl = sum(r['bfl'] for r in results.values())
    total_osl = sum(r['one_sided_long'] for r in results.values())
    total_an = sum(r['all_normal'] for r in results.values())
    print(f"Total words with all-normalForm at some t: {total_an}")
    print(f"Total words with one-sided long phases: {total_osl}")
    print(f"Total BFL occurrences: {total_bfl}")

    if total_bfl == 0:
        print("\n*** BFL appears VACUOUS across all tested architectures ***")
    else:
        print(f"\n*** BFL IS NON-VACUOUS: {total_bfl} words with BFL ***")


if __name__ == '__main__':
    main()
