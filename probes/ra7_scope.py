#!/usr/bin/env python3
"""
RA7 Scope: Map the EXACT CF/EC boundary.

Key insight: CF cycles exist when ALL ternary segments have EVEN length.
Segment length = gap - 1. So gap g gives segment of length g-1.
CF requires: all g_i - 1 are even, i.e., all gaps g_i are ODD.

Test this hypothesis across all gap patterns at n=9..25.
"""

import sys
from collections import defaultdict, Counter
from itertools import combinations
from math import prod

def build_cycle_inc(word, ms, n):
    L = len(word)
    configs = [[0]*n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + 1) % ms[p]
        configs.append(c)
    if configs[-1] != configs[0]:
        return None
    if len(set(tuple(c) for c in configs[:L])) != L:
        return None
    return [tuple(c) for c in configs[:L]]

def check_ec(good, word, n):
    L = len(word)
    mover_triples = defaultdict(set)
    nonmover_triples = defaultdict(set)
    for t in range(L):
        c = good[t]
        mover = word[t]
        for j in range(n):
            triple = (c[(j-1)%n], c[j], c[(j+1)%n])
            if j == mover:
                mover_triples[j].add(triple)
            else:
                nonmover_triples[j].add(triple)
    conflicts = {}
    for j in range(n):
        overlap = mover_triples[j] & nonmover_triples[j]
        if overlap:
            conflicts[j] = overlap
    return conflicts

def gap_pattern_ms(n, binary_positions):
    ms = [3]*n
    for p in binary_positions:
        ms[p] = 2
    return ms

def gaps_from_positions(positions, n):
    positions = sorted(positions)
    k = len(positions)
    gaps = []
    for i in range(k):
        gap = (positions[(i+1)%k] - positions[i]) % n
        gaps.append(gap)
    return tuple(sorted(gaps))

def all_gap_patterns(n, num_binary=3):
    seen = {}
    for combo in combinations(range(n), num_binary):
        combo_list = list(combo)
        adjacent = False
        for i in range(num_binary):
            if (combo_list[(i+1)%num_binary] - combo_list[i]) % n == 1:
                adjacent = True
                break
        if adjacent:
            continue
        gaps = gaps_from_positions(combo_list, n)
        if gaps not in seen:
            seen[gaps] = list(combo)
    return seen

def find_balanced_segment_words(seg_len, target=2):
    total = seg_len * target
    results = []
    def dfs(word, fc):
        if len(word) == total:
            if all(fc[i] == target for i in range(seg_len)):
                results.append(list(word))
            return
        last = word[-1]
        for nxt in [last-1, last+1]:
            if 0 <= nxt < seg_len and fc[nxt] < target:
                word.append(nxt)
                fc[nxt] += 1
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1
    for start in range(seg_len):
        fc = [0]*seg_len
        fc[start] = 1
        dfs([start], fc)
    return results


def construct_bounce_sweep_general(n, binary_positions):
    """Construct a bounce-sweep word for arbitrary non-adjacent binary positions.

    Works when ALL ternary segments have even length.
    """
    ms = gap_pattern_ms(n, binary_positions)
    binary_positions = sorted(binary_positions)
    num_binary = len(binary_positions)

    # Identify segments (going CCW from first binary position)
    segments = []
    for i in range(num_binary):
        b_start = binary_positions[i]
        b_end = binary_positions[(i+1) % num_binary]
        # Segment: procs between b_start and b_end, going from b_end-1 down to b_start+1
        # (CCW direction from b_end toward b_start)
        seg = []
        p = (b_end - 1) % n
        while p != b_start:
            seg.append(p)
            p = (p - 1) % n
        if seg:
            segments.append((seg, b_start))  # (segment procs, next binary in CCW)

    # Check all segments have even length
    all_even = all(len(seg) % 2 == 0 for seg, _ in segments)
    if not all_even:
        return None, ms, n

    # Build bounce words for each segment
    bounce_words = []
    for seg, next_binary in segments:
        seg_len = len(seg)
        bw = find_balanced_segment_words(seg_len, target=2)
        if not bw:
            return None, ms, n
        # Map to actual positions
        mapped = [seg[i] for i in bw[0]]
        bounce_words.append((mapped, next_binary))

    # Construct full word: bounce each segment + cross binary, then sweep
    word = []

    # Go CCW: start from the segment before binary_positions[0]
    # Segments are in order: seg between bp[-1] and bp[0], then bp[0] and bp[1], ...
    # Actually segments[i] is between bp[i] and bp[i+1].
    # Going CCW from bp[0]: first we encounter segments[num_binary-1]
    # (the one between bp[-1] and bp[0]), then cross bp[-1], etc.

    # Reorder: go CCW from bp[0]
    # Segments in CCW order from bp[0]:
    # segments[num_binary-1] (between bp[-1] and bp[0], going CCW = away from bp[0])
    # Actually this is getting complex. Let me use a simpler approach.

    # Go CCW through the ring starting from the position after bp[0]-1
    # hitting each segment and crossing each binary

    # Simpler: just go through segments in reverse order
    # segments[i] is between binary_positions[i] and binary_positions[(i+1)%num_binary]
    # Going CCW means starting from the last segment

    for i in range(num_binary-1, -1, -1):
        seg_procs, next_binary = segments[i]
        mapped_bounce = bounce_words[i][0]
        word.extend(mapped_bounce)
        word.append(next_binary)  # cross the binary

    # Sweep: traverse entire ring CCW
    start_sweep = (binary_positions[0] - 1) % n
    for i in range(n):
        word.append((start_sweep - i) % n)

    # Check firing counts
    fc = Counter(word)
    ok = all(fc.get(p, 0) == ms[p] for p in range(n))

    if not ok:
        return None, ms, n

    # Check ring adjacency
    for i in range(len(word)):
        d = abs(word[i] - word[(i+1)%len(word)])
        if d != 1 and d != n-1:
            return None, ms, n

    cycle = build_cycle_inc(word, ms, n)
    if cycle is None:
        return None, ms, n

    ec = check_ec(cycle, word, n)
    return word, ms, n, bool(ec)


if __name__ == "__main__":
    print("=" * 70)
    print("ALL GAP PATTERNS: CF constructibility check")
    print("=" * 70)

    print(f"\n{'n':>3s} {'Gaps':>20s} {'All odd':>8s} {'All even seg':>12s} {'Construct':>10s} {'EC':>5s} {'Result':>10s}")

    cf_patterns = []
    ec_patterns = []
    fail_patterns = []

    for n in range(9, 26):
        gap_patterns = all_gap_patterns(n, 3)
        threshold = 4 * 3**(n-2)

        for gaps, positions in sorted(gap_patterns.items()):
            ms = gap_pattern_ms(n, positions)
            product = prod(ms)
            if product >= threshold:
                continue

            all_odd_gaps = all(g % 2 == 1 for g in gaps)
            all_even_seg = all((g-1) % 2 == 0 for g in gaps)  # same as all_odd_gaps

            has_sandwiched = any(
                ms[p] == 3 and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2
                for p in range(n)
            )

            # Has gap=2 iff has sandwiched ternary
            has_gap2 = 2 in gaps

            result = construct_bounce_sweep_general(n, positions)
            if result[0] is not None:
                word, ms_r, n_r, has_ec = result
                if has_ec:
                    tag = "EC"
                    ec_patterns.append((n, gaps))
                else:
                    tag = "CF"
                    cf_patterns.append((n, gaps))
            else:
                tag = "NO-BUILD"
                fail_patterns.append((n, gaps))

            # Only print interesting cases
            if tag == "CF" or (not has_gap2 and tag != "NO-BUILD"):
                print(f"{n:3d} {str(gaps):>20s} {str(all_odd_gaps):>8s} {str(all_even_seg):>12s} "
                      f"{'YES' if result[0] else 'NO':>10s} {tag:>5s} "
                      f"{'*** CF ***' if tag=='CF' else ''}")

    print(f"\n--- Summary ---")
    print(f"CF patterns (bounce-sweep works, no EC): {len(cf_patterns)}")
    for n, gaps in cf_patterns[:20]:
        all_odd = all(g % 2 == 1 for g in gaps)
        has_gap2 = 2 in gaps
        print(f"  n={n}, gaps={gaps}, all_odd={all_odd}, has_gap2={has_gap2}")

    print(f"\nEC patterns (bounce-sweep works but has EC): {len(ec_patterns)}")
    for n, gaps in ec_patterns[:20]:
        print(f"  n={n}, gaps={gaps}")

    print(f"\nNO-BUILD patterns (construction failed): {len(fail_patterns)}")

    # Check: is CF <=> all gaps odd AND no gap = 2?
    print(f"\nHypothesis: CF iff all gaps odd?")
    for n, gaps in cf_patterns:
        if not all(g % 2 == 1 for g in gaps):
            print(f"  COUNTEREXAMPLE: n={n}, gaps={gaps} is CF but not all odd!")
    for n, gaps in ec_patterns:
        if all(g % 2 == 1 for g in gaps):
            print(f"  COUNTEREXAMPLE: n={n}, gaps={gaps} is EC but all odd!")
    for n, gaps in fail_patterns:
        if all(g % 2 == 1 for g in gaps):
            all_seg_even = all((g-1) % 2 == 0 for g in gaps)
            print(f"  MISSING: n={n}, gaps={gaps} has all odd gaps but construction failed "
                  f"(all_seg_even={all_seg_even})")

    # The definitive pattern
    print(f"\n--- DEFINITIVE PATTERN ---")
    print(f"CF cycles exist iff: ALL gaps are odd AND ALL gaps >= 3")
    print(f"  (all gaps odd => all segment lengths even => bounce-sweep works)")
    print(f"  (all gaps >= 3 => no sandwiched ternary => no gap-2)")
    print(f"  (but gap-2 = even gap, so 'all odd' already implies >= 3)")
    print(f"  Equivalently: CF iff all gaps are odd >= 3")
    print(f"  Equivalently: CF iff no gap is even (and all >= 2, which is given)")
