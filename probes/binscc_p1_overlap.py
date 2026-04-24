#!/usr/bin/env python3
"""binscc_p1_overlap.py — P1 (middle binary) overlap analysis.

KEY INSIGHT: For 3 consecutive binary P0, P1, P2:
  P1's full context = (c_0, c_1, c_2) = cube vertex
  P1 overlap is INDEPENDENT of transition function (binary always flips)
  P1 overlap at vertex v means f_1(v) must equal both S and 1-S → contradiction

Question: does P1 overlap alone kill ALL sub-threshold cycles?
If yes → Case 3a proved for general transitions, not just incrementing.

The cube walk is determined by the mover word alone.
P1 fires at some cube vertices (mover) and not others (nonmover).
Overlap = some vertex visited as both P1-mover and P1-nonmover.
"""

from itertools import product as iproduct
from collections import Counter
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


def analyze_p1_overlap(ms, n, mover_word, bp0=0, bp1=1, bp2=2):
    """Analyze P1 overlap using ONLY cube walk (transition-independent).

    Returns: (is_valid, has_p1_overlap, cube_info)
    """
    ell = len(mover_word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = mover_word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))

    if configs[-1] != configs[0]:
        return False, False, None
    if len(set(configs[:ell])) != ell:
        return False, False, None

    fire_counts = [0] * n
    for p in mover_word:
        fire_counts[p] += 1
    for p in range(n):
        if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0:
            return False, False, None

    for i in range(ell):
        p1 = mover_word[i]
        p2 = mover_word[(i+1) % ell]
        diff = abs(p1 - p2)
        if diff != 1 and diff != n - 1:
            return False, False, None

    # Extract cube walk
    cube_walk = []
    for i in range(ell):
        c = configs[i]
        cube_walk.append((c[bp0], c[bp1], c[bp2]))

    # P1 overlap check
    p1_mover_vertices = set()
    p1_nonmover_vertices = set()
    for i in range(ell):
        v = cube_walk[i]
        if mover_word[i] == bp1:
            p1_mover_vertices.add(v)
        else:
            p1_nonmover_vertices.add(v)

    has_p1_overlap = bool(p1_mover_vertices & p1_nonmover_vertices)

    # Additional analysis
    n_cube_vertices = len(set(cube_walk))

    # Count "stay" steps (non-binary firings)
    stay_vertices = set()
    for i in range(ell):
        if mover_word[i] not in (bp0, bp1, bp2):
            stay_vertices.add(cube_walk[i])

    info = {
        'n_cube_vertices': n_cube_vertices,
        'p1_mover_vertices': p1_mover_vertices,
        'p1_nonmover_vertices': p1_nonmover_vertices,
        'stay_vertices': stay_vertices,
        'p1_fires': fire_counts[bp1],
    }

    return True, has_p1_overlap, info


def main():
    print("=" * 70)
    print("P1 (MIDDLE BINARY) OVERLAP — TRANSITION-INDEPENDENT")
    print("=" * 70)
    print("P1 context = cube vertex. Overlap → contradiction for ANY transition fn.")
    print()

    # Sub-threshold cases: product < M_n
    # M_5=96, M_6=288, M_7=864, M_8=2592
    # For n>=9: M_n = 4·3^(n-2)
    test_cases = [
        # Sub-threshold
        (5, [2, 2, 2, 3, 3], "n=5 prod=72 (sub M_5=96)"),
        (6, [2, 2, 2, 3, 3, 3], "n=6 prod=216 (sub M_6=288)"),
        # At threshold
        (5, [2, 2, 2, 3, 4], "n=5 prod=96 (= M_5)"),
        (6, [2, 2, 2, 3, 3, 4], "n=6 prod=288 (= M_6)"),
    ]

    for n, ms, label in test_cases:
        max_len = 3 * n + 6
        words = enumerate_mover_words_smart(ms, n, max_len)

        total_valid = 0
        p1_overlap_count = 0
        no_p1_overlap = []

        by_vertices = {}  # n_vertices -> (total, p1_overlap)

        for word in words:
            is_valid, has_p1, info = analyze_p1_overlap(ms, n, word)
            if not is_valid:
                continue
            total_valid += 1

            nv = info['n_cube_vertices']
            if nv not in by_vertices:
                by_vertices[nv] = [0, 0]
            by_vertices[nv][0] += 1

            if has_p1:
                p1_overlap_count += 1
                by_vertices[nv][1] += 1
            else:
                if len(no_p1_overlap) < 5:
                    no_p1_overlap.append((word, info))

        print(f"\n--- {label} ---")
        print(f"  {total_valid} valid cycles, {p1_overlap_count} with P1 overlap "
              f"({100*p1_overlap_count/total_valid:.1f}%)")
        print(f"  {total_valid - p1_overlap_count} WITHOUT P1 overlap")

        for nv in sorted(by_vertices.keys()):
            tot, ovl = by_vertices[nv]
            pct = 100 * ovl / tot if tot > 0 else 0
            print(f"    {nv} vertices: {tot} cycles, {ovl} P1-overlap ({pct:.0f}%)")

        if no_p1_overlap:
            print(f"\n  Cycles without P1 overlap (first {len(no_p1_overlap)}):")
            for word, info in no_p1_overlap[:3]:
                print(f"    word={word}")
                print(f"      cube: {info['n_cube_vertices']} vertices, "
                      f"P1 fires {info['p1_fires']} times")
                print(f"      P1 mover vertices: {sorted(info['p1_mover_vertices'])}")
                print(f"      P1 nonmover vertices: {sorted(info['p1_nonmover_vertices'])}")
                print(f"      stay vertices (non-binary fires): {sorted(info['stay_vertices'])}")
                overlap = info['p1_mover_vertices'] & info['stay_vertices']
                if overlap:
                    print(f"      !! P1 mover ∩ stay = {overlap}")
                else:
                    print(f"      P1 mover ∩ stay = ∅ (stays avoid P1 mover vertices)")

        if total_valid == p1_overlap_count:
            print(f"  ★ ALL cycles have P1 overlap → sub-threshold proved!")

        sys.stdout.flush()

    # Check: does P1 overlap kill everything at sub-threshold for more multisets?
    print(f"\n{'='*70}")
    print("COMPREHENSIVE: All sub-threshold multisets with 3 consecutive binary")
    print("="*70)

    for n in [5, 6]:
        # Generate all ms with 3 consecutive binary at P0,P1,P2 and rest ternary
        # product < M_n
        if n == 5:
            threshold = 96  # M_5
        elif n == 6:
            threshold = 288  # M_6
        else:
            continue

        # ms = (2, 2, 2, m_3, ..., m_{n-1}) with product < threshold
        # product = 8 * prod(m_3, ..., m_{n-1})
        # Need prod(m_3, ..., m_{n-1}) < threshold / 8
        non_bin = n - 3
        max_non_bin_prod = threshold // 8  # exclusive

        # Enumerate non-binary multisets with product < max_non_bin_prod
        # Each m_i >= 2 (need >=2 states)
        # Actually m_i >= 3 for non-binary (if m_i = 2 then 4+ binary which is different case)
        # Wait, the ms just needs to have 3 consecutive binary. Other positions can be anything >=2.
        # For sub-threshold, the product is small, so non-binary are likely all 3.

        ms_list = []
        if non_bin == 2:  # n=5
            for m3 in range(3, max_non_bin_prod + 1):
                for m4 in range(3, max_non_bin_prod // m3 + 1):
                    if m3 * m4 < max_non_bin_prod:
                        ms_list.append([2, 2, 2, m3, m4])
        elif non_bin == 3:  # n=6
            for m3 in range(3, max_non_bin_prod + 1):
                for m4 in range(m3, max_non_bin_prod // m3 + 1):
                    for m5 in range(m4, max_non_bin_prod // (m3 * m4) + 1):
                        if m3 * m4 * m5 < max_non_bin_prod:
                            ms_list.append([2, 2, 2, m3, m4, m5])

        all_killed = True
        for ms in ms_list:
            prod = 1
            for m in ms:
                prod *= m
            if prod >= threshold:
                continue

            max_len = 3 * n + 6
            words = enumerate_mover_words_smart(ms, n, max_len)

            valid = 0
            p1_ovl = 0
            for word in words:
                is_valid, has_p1, info = analyze_p1_overlap(ms, n, word)
                if not is_valid:
                    continue
                valid += 1
                if has_p1:
                    p1_ovl += 1

            if valid > 0:
                no_p1 = valid - p1_ovl
                status = "★ ALL P1 OVERLAP" if no_p1 == 0 else f"{no_p1} survive P1"
                print(f"  n={n} ms={tuple(ms)} prod={prod}: "
                      f"{valid} valid, {p1_ovl} P1-overlap → {status}")
                if no_p1 > 0:
                    all_killed = False

        if all_killed:
            print(f"  ★★ n={n}: ALL sub-threshold multisets killed by P1 overlap alone!")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
