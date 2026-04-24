#!/usr/bin/env python3
"""binscc_p0p2_separation.py — Can non-binary neighbors separate P0/P2 overlap?

For P1-free cycles (no P1 overlap): P0 and P2 have 2D projection overlap
but non-binary neighbors c_{n-1} (for P0) and c_3 (for P2) can separate.

KEY QUESTION: For each P1-free cycle at sub-threshold product,
does there EXIST a choice of non-binary values that separates
ALL overlapping 2D projections at P0 AND P2 simultaneously?

If NO → overlap unavoidable → impossibility for ANY transition function
If YES → some transition functions can avoid overlap → need other obstruction
"""

from itertools import product as iproduct
from collections import Counter, defaultdict
import sys


def enumerate_mover_words_smart(ms, n, max_length):
    ring_adj = {}
    for p in range(n):
        ring_adj[p] = [(p-1) % n, (p+1) % n]
    results = []
    start_config = tuple(0 for _ in range(n))
    def dfs(word, fire_counts, current_config):
        if len(word) > max_length:
            return
        if len(word) >= 6 and current_config == start_config:
            fair = all(fire_counts[p] > 0 and fire_counts[p] % ms[p] == 0
                       for p in range(n))
            if fair:
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fire_counts[p]) for p in range(n)
                     if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            new_config = list(current_config)
            new_config[nxt] = (new_config[nxt] + 1) % ms[nxt]
            new_config = tuple(new_config)
            new_counts = list(fire_counts)
            new_counts[nxt] += 1
            word.append(nxt)
            dfs(word, new_counts, new_config)
            word.pop()
    for p in range(n):
        first = list(start_config)
        first[p] = (first[p] + 1) % ms[p]
        first = tuple(first)
        dfs([p], [1 if i == p else 0 for i in range(n)], first)
    return results


def check_separation_possible(ms, n, mover_word, bp0=0, bp1=1, bp2=2):
    """Check if non-binary neighbors can simultaneously separate P0 and P2.

    Returns (is_valid, has_p1_overlap, p0_separable, p2_separable, both_separable)
    """
    ell = len(mover_word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = mover_word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))

    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    fire_counts = [0] * n
    for p in mover_word:
        fire_counts[p] += 1
    for p in range(n):
        if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0:
            return None
    for i in range(ell):
        p1 = mover_word[i]
        p2 = mover_word[(i+1) % ell]
        diff = abs(p1 - p2)
        if diff != 1 and diff != n - 1:
            return None

    # P1 overlap check
    p1_mover = set()
    p1_nonmover = set()
    for i in range(ell):
        v = (configs[i][bp0], configs[i][bp1], configs[i][bp2])
        if mover_word[i] == bp1:
            p1_mover.add(v)
        else:
            p1_nonmover.add(v)
    has_p1_overlap = bool(p1_mover & p1_nonmover)

    if has_p1_overlap:
        return (True, True, None, None, None)

    # P0 overlap analysis: ctx = (c_{n-1}, c_0, c_1)
    # 2D projection: (c_0, c_1). Separator: c_{n-1} ∈ {0,...,ms[n-1]-1}
    # For each (c_0, c_1) pair that appears as both P0-mover and P0-nonmover:
    #   mover steps have c_{n-1} values from the cycle
    #   nonmover steps have c_{n-1} values from the cycle
    #   Separation requires: mover c_{n-1} values ∩ nonmover c_{n-1} values = ∅ at this (c_0,c_1)

    # But with general transitions, c_{n-1} values can be DIFFERENT from incrementing!
    # The mover word determines WHICH processor fires at each step.
    # Binary states are determined (always flip). Non-binary states can be anything.

    # So the question is: for the mover word structure, can we assign c_{n-1} values
    # to each step such that the cycle closes AND separation holds?

    # Actually, the non-binary states are not freely assignable — they're determined
    # by the non-binary transition functions. But the transition functions are free
    # (we're asking if ANY transition function works).

    # Simplification: the cube walk determines WHEN P_{n-1} fires. At those steps,
    # c_{n-1} changes. At other steps, c_{n-1} stays. The sequence of c_{n-1} values
    # is determined by: initial value + when P_{n-1} fires + what values it transitions to.

    # With m_{n-1} = 3 and general transitions, P_{n-1} can go to ANY of {0,1,2}.
    # So c_{n-1} can take any value at any P_{n-1}-firing step.

    # Wait, that's not quite right. The transition is f_{n-1}(c_{n-2}, c_{n-1}, c_0).
    # The value depends on the context. Different contexts can map to different values.
    # But the context includes c_{n-2} (non-binary) and c_0 (binary), which vary.

    # This is very complex. Let me simplify by checking:
    # For the INCREMENTING transition, what's the separation status?
    # And then: is there ANY assignment of c_{n-1} values (consistent with cycle)
    # that achieves separation?

    # For incrementing: c_{n-1} values are determined.
    p0_2d_overlap_pairs = []  # (c_0, c_1) pairs with P0 2D overlap
    p0_mover_by_2d = defaultdict(set)  # (c_0,c_1) -> set of c_{n-1} at mover steps
    p0_nonmover_by_2d = defaultdict(set)  # (c_0,c_1) -> set of c_{n-1} at nonmover steps

    for i in range(ell):
        c = configs[i]
        c_01 = (c[bp0], c[bp1])
        cn1 = c[(bp0 - 1) % n]  # c_{n-1}
        if mover_word[i] == bp0:
            p0_mover_by_2d[c_01].add(cn1)
        else:
            p0_nonmover_by_2d[c_01].add(cn1)

    p0_inc_separated = True  # with incrementing transitions
    for c_01 in p0_mover_by_2d:
        if c_01 in p0_nonmover_by_2d:
            if p0_mover_by_2d[c_01] & p0_nonmover_by_2d[c_01]:
                p0_inc_separated = False
                p0_2d_overlap_pairs.append(c_01)

    # P2 overlap analysis: ctx = (c_1, c_2, c_3)
    p2_mover_by_2d = defaultdict(set)
    p2_nonmover_by_2d = defaultdict(set)

    for i in range(ell):
        c = configs[i]
        c_12 = (c[bp1], c[bp2])
        c3 = c[(bp2 + 1) % n]
        if mover_word[i] == bp2:
            p2_mover_by_2d[c_12].add(c3)
        else:
            p2_nonmover_by_2d[c_12].add(c3)

    p2_inc_separated = True
    p2_2d_overlap_pairs = []
    for c_12 in p2_mover_by_2d:
        if c_12 in p2_nonmover_by_2d:
            if p2_mover_by_2d[c_12] & p2_nonmover_by_2d[c_12]:
                p2_inc_separated = False
                p2_2d_overlap_pairs.append(c_12)

    # Check: with incrementing, is P0 or P2 overlapping?
    inc_has_overlap = (not p0_inc_separated) or (not p2_inc_separated)

    # Now check: how many c_{n-1} values would be needed to separate P0?
    # For each 2D pair with overlap: need mover c_{n-1} ∩ nonmover c_{n-1} = ∅
    # Max needed: |mover| + |nonmover| colors for each pair
    p0_max_colors_needed = 0
    for c_01 in p0_mover_by_2d:
        if c_01 in p0_nonmover_by_2d:
            needed = len(p0_mover_by_2d[c_01]) + len(p0_nonmover_by_2d[c_01])
            p0_max_colors_needed = max(p0_max_colors_needed, needed)

    p2_max_colors_needed = 0
    for c_12 in p2_mover_by_2d:
        if c_12 in p2_nonmover_by_2d:
            needed = len(p2_mover_by_2d[c_12]) + len(p2_nonmover_by_2d[c_12])
            p2_max_colors_needed = max(p2_max_colors_needed, needed)

    return {
        'is_valid': True,
        'has_p1_overlap': False,
        'p0_inc_separated': p0_inc_separated,
        'p2_inc_separated': p2_inc_separated,
        'inc_has_overlap': inc_has_overlap,
        'p0_2d_overlap_pairs': p0_2d_overlap_pairs,
        'p2_2d_overlap_pairs': p2_2d_overlap_pairs,
        'p0_max_colors': p0_max_colors_needed,
        'p2_max_colors': p2_max_colors_needed,
        'p0_mover_by_2d': dict(p0_mover_by_2d),
        'p0_nonmover_by_2d': dict(p0_nonmover_by_2d),
        'p2_mover_by_2d': dict(p2_mover_by_2d),
        'p2_nonmover_by_2d': dict(p2_nonmover_by_2d),
    }


def main():
    print("=" * 70)
    print("P0/P2 SEPARATION ANALYSIS FOR P1-FREE CYCLES")
    print("=" * 70)

    for n, ms, label in [
        (5, [2, 2, 2, 3, 3], "n=5 prod=72 sub-threshold"),
        (5, [2, 2, 2, 3, 4], "n=5 prod=96 = M_5"),
    ]:
        max_len = 3 * n + 6
        words = enumerate_mover_words_smart(ms, n, max_len)

        p1_free_results = []

        for word in words:
            result = check_separation_possible(ms, n, word)
            if result is None:
                continue
            if isinstance(result, tuple):
                continue  # has P1 overlap
            if result['has_p1_overlap']:
                continue
            p1_free_results.append((word, result))

        print(f"\n--- {label} ---")
        print(f"  {len(p1_free_results)} P1-free cycles")

        # Count separation patterns
        both_inc_sep = 0  # both P0 and P2 separated with incrementing
        p0_only_inc_ovl = 0
        p2_only_inc_ovl = 0
        both_inc_ovl = 0

        max_p0_colors = Counter()
        max_p2_colors = Counter()

        for word, r in p1_free_results:
            if r['p0_inc_separated'] and r['p2_inc_separated']:
                both_inc_sep += 1
            elif not r['p0_inc_separated'] and r['p2_inc_separated']:
                p0_only_inc_ovl += 1
            elif r['p0_inc_separated'] and not r['p2_inc_separated']:
                p2_only_inc_ovl += 1
            else:
                both_inc_ovl += 1

            max_p0_colors[r['p0_max_colors']] += 1
            max_p2_colors[r['p2_max_colors']] += 1

        print(f"  With incrementing transitions:")
        print(f"    Both P0,P2 separated (no overlap): {both_inc_sep}")
        print(f"    P0 overlap only: {p0_only_inc_ovl}")
        print(f"    P2 overlap only: {p2_only_inc_ovl}")
        print(f"    Both P0,P2 overlap: {both_inc_ovl}")

        if both_inc_sep > 0:
            print(f"\n  ★ {both_inc_sep} cycles have NO overlap at ANY proc with incrementing!")
            # These should only exist at threshold (prod=M_n), not sub-threshold
        else:
            print(f"\n  All P1-free cycles have P0 or P2 overlap with incrementing ✓")

        print(f"\n  P0 max colors needed for separation: {dict(max_p0_colors)}")
        print(f"  P2 max colors needed for separation: {dict(max_p2_colors)}")
        print(f"  Available colors: ms[{n-1}]={ms[n-1]} for P0, ms[3]={ms[3]} for P2")

        # Key question: how many need > available colors?
        p0_unseparable = sum(v for k, v in max_p0_colors.items() if k > ms[n-1])
        p2_unseparable = sum(v for k, v in max_p2_colors.items() if k > ms[3])
        print(f"\n  P0 color-unseparable (need > {ms[n-1]}): {p0_unseparable}")
        print(f"  P2 color-unseparable (need > {ms[3]}): {p2_unseparable}")

        # Show detailed examples
        if p1_free_results:
            print(f"\n  Detailed examples (first 3 P1-free cycles):")
            for word, r in p1_free_results[:3]:
                print(f"\n    Word: {word}")
                print(f"    P0 2D overlap pairs: {r['p0_2d_overlap_pairs']}")
                print(f"    P2 2D overlap pairs: {r['p2_2d_overlap_pairs']}")
                for c_01 in r['p0_2d_overlap_pairs'][:2]:
                    m = r['p0_mover_by_2d'].get(c_01, set())
                    nm = r['p0_nonmover_by_2d'].get(c_01, set())
                    print(f"    P0 at {c_01}: mover c_{n-1}={m}, nonmover c_{n-1}={nm}, "
                          f"overlap={m & nm}")
                for c_12 in r['p2_2d_overlap_pairs'][:2]:
                    m = r['p2_mover_by_2d'].get(c_12, set())
                    nm = r['p2_nonmover_by_2d'].get(c_12, set())
                    print(f"    P2 at {c_12}: mover c_3={m}, nonmover c_3={nm}, "
                          f"overlap={m & nm}")

        sys.stdout.flush()

    # Now the critical question: with general transitions, can P0 and P2
    # BOTH be separated? The cycle structure constrains c_{n-1} and c_3 values,
    # but general transitions allow more freedom.

    print(f"\n{'='*70}")
    print("SEPARATION FEASIBILITY: Can general transitions avoid ALL overlap?")
    print("="*70)
    print()
    print("The color-count argument gives a NECESSARY condition:")
    print("  If max colors needed > available, separation impossible.")
    print("But it's NOT sufficient: the cycle structure constrains which")
    print("color assignments are consistent (c_{n-1} must form a valid sequence).")
    print()
    print("For sub-threshold with all ternary (ms_i = 3):")
    print("  3 colors available at both P0 and P2.")
    print("  If any 2D pair needs > 3 colors → unseparable.")


if __name__ == "__main__":
    main()
