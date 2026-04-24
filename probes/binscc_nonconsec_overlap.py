#!/usr/bin/env python3
"""binscc_nonconsec_overlap.py — Test unconditional overlap for non-consecutive binary.

KEY QUESTION: Does every good cycle with 3 non-consecutive binary
have mover/nonmover overlap at some binary processor?

If YES → unconditional result, theorem complete.
If NO → sweep-only shadow not sufficient, need different approach.

Test approach: enumerate ALL fair mover words for small n (n=5,6,7)
with non-consecutive binary architectures, check overlap.

For consecutive binary: UBO handles this (walk-on-cube).
For non-consecutive: no cube structure, context spaces are 18-24.
"""

from itertools import combinations, product as iproduct
from collections import Counter
import time
import sys


def generate_non_consec_orientations(n, ms_base):
    """Generate non-consecutive binary orientations."""
    seen = set()
    results = []
    for perm in set(__import__('itertools').permutations(tuple(sorted(ms_base)))):
        # Check 3 consecutive binary
        has_3_consec = False
        for i in range(n):
            if perm[i] == 2 and perm[(i+1)%n] == 2 and perm[(i+2)%n] == 2:
                has_3_consec = True
                break
        if has_3_consec:
            continue
        # Normalize
        rotations = [perm[i:] + perm[:i] for i in range(n)]
        reflected = perm[::-1]
        ref_rotations = [reflected[i:] + reflected[:i] for i in range(n)]
        canonical = min(rotations + ref_rotations)
        if canonical not in seen:
            seen.add(canonical)
            results.append(canonical)
    return results


def check_overlap_for_mover_word(ms, n, mover_word):
    """Given a mover word, construct the cycle and check overlap at binary procs.

    Returns (is_valid_cycle, has_overlap, overlap_proc).
    """
    ell = len(mover_word)

    # Build cycle from all-zeros
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = mover_word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))

    # Check closure
    if configs[-1] != configs[0]:
        return False, False, None

    # Check distinctness
    if len(set(configs[:ell])) != ell:
        return False, False, None

    # Check fairness
    fire_counts = [0] * n
    for p in mover_word:
        fire_counts[p] += 1
    for p in range(n):
        if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0:
            return False, False, None

    # Check ring adjacency
    for i in range(ell):
        p1 = mover_word[i]
        p2 = mover_word[(i+1) % ell]
        diff = abs(p1 - p2)
        if diff != 1 and diff != n - 1:
            return False, False, None

    # Check overlap at binary processors
    for p in range(n):
        if ms[p] != 2:
            continue
        mover_ctx = set()
        nonmover_ctx = set()
        for i in range(ell):
            c = configs[i]
            ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
            if mover_word[i] == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        if mover_ctx & nonmover_ctx:
            return True, True, p

    return True, False, None


def enumerate_mover_words_smart(ms, n, max_length):
    """Enumerate fair ring-adjacent mover words with pruning."""
    ring_adj = {}
    for p in range(n):
        ring_adj[p] = [(p-1) % n, (p+1) % n]

    results = []
    start_config = tuple(0 for _ in range(n))

    def dfs(word, fire_counts, current_config):
        if len(word) > max_length:
            return

        # Check closure
        if len(word) >= 6 and current_config == start_config:
            fair = all(fire_counts[p] > 0 and fire_counts[p] % ms[p] == 0
                       for p in range(n))
            if fair:
                results.append(tuple(word))
            return  # Don't extend past closure

        # Pruning: remaining length insufficient for fairness
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


def main():
    print("=" * 70)
    print("UNCONDITIONAL OVERLAP TEST: Non-consecutive binary")
    print("=" * 70)

    # Test pure {2,3} non-consecutive at n=5,6
    print("\n--- Pure {2,3}: 3 binary + ternary, non-consecutive ---")

    for n in [5, 6]:
        ms_base = [2, 2, 2] + [3] * (n - 3)
        non_consec = generate_non_consec_orientations(n, ms_base)

        print(f"\nn={n}: {len(non_consec)} non-consecutive orientations")
        sys.stdout.flush()

        max_len = 3 * n + 4  # generous bound
        total_valid = 0
        total_overlap = 0
        total_clean = 0

        for ms_tuple in non_consec:
            ms = list(ms_tuple)
            t0 = time.time()
            words = enumerate_mover_words_smart(ms, n, max_len)
            elapsed = time.time() - t0

            ms_valid = 0
            ms_overlap = 0
            ms_clean = 0
            clean_words = []

            for word in words:
                is_valid, has_ovlp, proc = check_overlap_for_mover_word(ms, n, word)
                if is_valid:
                    ms_valid += 1
                    if has_ovlp:
                        ms_overlap += 1
                    else:
                        ms_clean += 1
                        if len(clean_words) < 5:
                            clean_words.append(word)

            total_valid += ms_valid
            total_overlap += ms_overlap
            total_clean += ms_clean

            if ms_clean > 0:
                print(f"  ms={ms_tuple}: {ms_valid} valid, "
                      f"{ms_overlap} overlap, {ms_clean} CLEAN ({elapsed:.1f}s)")
                for w in clean_words:
                    print(f"    Clean word: {w}")
            else:
                print(f"  ms={ms_tuple}: {ms_valid} valid, ALL OVERLAP ({elapsed:.1f}s)")
            sys.stdout.flush()

        if total_clean == 0 and total_valid > 0:
            print(f"\n  ★ n={n}: ALL {total_valid} valid cycles overlap! Unconditional!")
        else:
            print(f"\n  n={n}: {total_clean} clean cycles found. NOT unconditional.")

    # Test mixed {2,3,4} non-consecutive at n=5,6
    print(f"\n{'='*70}")
    print("Mixed {2,3,4}: 3 binary + quaternary + ternary, non-consecutive")
    print("="*70)

    for n in [5, 6]:
        ms_base = [2, 2, 2, 4] + [3] * (n - 4)
        non_consec = generate_non_consec_orientations(n, ms_base)

        print(f"\nn={n}: {len(non_consec)} non-consecutive orientations")
        sys.stdout.flush()

        max_len = 3 * n + 4
        total_valid = 0
        total_overlap = 0
        total_clean = 0

        for ms_tuple in non_consec:
            ms = list(ms_tuple)
            t0 = time.time()
            words = enumerate_mover_words_smart(ms, n, max_len)
            elapsed = time.time() - t0

            ms_valid = 0
            ms_overlap = 0
            ms_clean = 0
            clean_words = []

            for word in words:
                is_valid, has_ovlp, proc = check_overlap_for_mover_word(ms, n, word)
                if is_valid:
                    ms_valid += 1
                    if has_ovlp:
                        ms_overlap += 1
                    else:
                        ms_clean += 1
                        if len(clean_words) < 5:
                            clean_words.append(word)

            total_valid += ms_valid
            total_overlap += ms_overlap
            total_clean += ms_clean

            if ms_clean > 0:
                print(f"  ms={ms_tuple}: {ms_valid} valid, "
                      f"{ms_overlap} overlap, {ms_clean} CLEAN ({elapsed:.1f}s)")
                for w in clean_words:
                    fire_counts = Counter(w)
                    print(f"    Clean word (len={len(w)}): {w}")
                    print(f"      fires: {dict(fire_counts)}")
            else:
                print(f"  ms={ms_tuple}: {ms_valid} valid, ALL OVERLAP ({elapsed:.1f}s)")
            sys.stdout.flush()

        if total_clean == 0 and total_valid > 0:
            print(f"\n  ★ n={n}: ALL {total_valid} valid cycles overlap! Unconditional!")
        else:
            print(f"\n  n={n}: {total_clean} clean cycles found. NOT unconditional.")


if __name__ == "__main__":
    main()
