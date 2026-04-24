#!/usr/bin/env python3
"""binscc_p1_large_n.py — P1 overlap universality for n=6..9 sub-threshold.

Test whether P1 (middle binary) overlap kills ALL cycles at sub-threshold
for larger n. If yes for n ≥ 6, this closes Case 3a analytically.

Key insight: more non-binary processors → more "stay" steps on cube →
harder to avoid P1-mover vertices.
"""

from collections import Counter
import sys
import time


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


def check_p1_overlap(ms, n, mover_word, bp1=1):
    """Check P1 overlap. Returns (is_valid, has_p1_overlap)."""
    ell = len(mover_word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = mover_word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))

    if configs[-1] != configs[0]:
        return False, False
    if len(set(configs[:ell])) != ell:
        return False, False

    fire_counts = [0] * n
    for p in mover_word:
        fire_counts[p] += 1
    for p in range(n):
        if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0:
            return False, False

    for i in range(ell):
        p1 = mover_word[i]
        p2 = mover_word[(i+1) % ell]
        diff = abs(p1 - p2)
        if diff != 1 and diff != n - 1:
            return False, False

    # P1 overlap: cube vertex (c_0, c_1, c_2) at P1
    bp0, bp2 = bp1 - 1, bp1 + 1
    p1_mover = set()
    p1_nonmover = set()
    for i in range(ell):
        c = configs[i]
        v = (c[bp0], c[bp1], c[bp2])
        if mover_word[i] == bp1:
            p1_mover.add(v)
        else:
            p1_nonmover.add(v)

    return True, bool(p1_mover & p1_nonmover)


def main():
    print("=" * 70)
    print("P1 OVERLAP UNIVERSALITY — LARGE n")
    print("=" * 70)

    # Sub-threshold pure ternary: ms = (2,2,2,3,...,3)
    # Product = 8 * 3^(n-3)
    # Threshold M_n:
    #   n=5: M_5=96, prod=72 < 96 ✓
    #   n=6: M_6=288, prod=216 < 288 ✓
    #   n=7: M_7=864, prod=648 < 864 ✓
    #   n=8: M_8=2592, prod=1944 < 2592 ✓
    #   n=9: M_9=8748, prod=5832 < 8748 ✓
    #   General: 8*3^(n-3) vs 4*3^(n-2) = 12*3^(n-3). Always 8 < 12. ✓

    for n in range(5, 10):
        ms = [2, 2, 2] + [3] * (n - 3)
        prod = 8 * (3 ** (n - 3))

        # Also compute threshold
        if n <= 8:
            threshold = 32 * (3 ** (n - 4))
        else:
            threshold = 4 * (3 ** (n - 2))

        # Use generous max_length but not too large (exponential blowup)
        max_len = 3 * n + 4
        # For n >= 8, this might be too slow. Limit.
        if n >= 8:
            max_len = 3 * n + 2

        print(f"\nn={n}: ms={tuple(ms)}, prod={prod}, threshold={threshold}")
        sys.stdout.flush()

        t0 = time.time()
        words = enumerate_mover_words_smart(ms, n, max_len)
        t1 = time.time()
        print(f"  Enumerated {len(words)} words in {t1-t0:.1f}s")
        sys.stdout.flush()

        valid = 0
        p1_overlap = 0
        no_p1 = 0
        no_p1_example = None

        for word in words:
            is_valid, has_p1 = check_p1_overlap(ms, n, word)
            if not is_valid:
                continue
            valid += 1
            if has_p1:
                p1_overlap += 1
            else:
                no_p1 += 1
                if no_p1_example is None:
                    no_p1_example = word

        elapsed = time.time() - t0
        print(f"  {valid} valid cycles, {p1_overlap} P1-overlap, {no_p1} survive P1 ({elapsed:.1f}s)")

        if no_p1 == 0 and valid > 0:
            print(f"  ★ ALL KILLED by P1 overlap!")
        elif no_p1 > 0:
            pct = 100 * p1_overlap / valid if valid > 0 else 0
            print(f"  P1 overlap rate: {pct:.1f}%")
            if no_p1_example:
                print(f"  Example surviving word: {no_p1_example}")
                print(f"    Length: {len(no_p1_example)}, fires: {Counter(no_p1_example)}")
        sys.stdout.flush()

    print(f"\n{'='*70}")
    print("SUMMARY")
    print("="*70)
    print("If P1 overlap universal for n >= 6, then Case 3a:")
    print("  3 consecutive binary + all ternary → no valid system")
    print("  Works for ANY transition function (binary always flips)")
    print()
    print("Open: extend to mixed multisets (some m_i = 4, 5, ...)")


if __name__ == "__main__":
    main()
