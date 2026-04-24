#!/usr/bin/env python3
"""binscc_overlap_n789.py — Test all-processor overlap at n=7,8,9.

Expectation:
- n=7,8: survivors exist (valid systems exist at product 32·3^(n-4))
- n=9: NO survivors (all product-7776 multisets fail)

If n=9 has no survivors → overlap kills Case 3c for n≥9.
"""

from itertools import combinations
from collections import Counter
import time
import sys


def generate_non_consec_necklaces(n, ms_base):
    """Generate non-consecutive-3-binary necklaces."""
    seen = set()
    results = []
    for perm in set(__import__('itertools').permutations(tuple(sorted(ms_base)))):
        has_3_consec = False
        for i in range(n):
            if perm[i] == 2 and perm[(i+1)%n] == 2 and perm[(i+2)%n] == 2:
                has_3_consec = True
                break
        if has_3_consec:
            continue
        rotations = [perm[i:] + perm[:i] for i in range(n)]
        reflected = perm[::-1]
        ref_rotations = [reflected[i:] + reflected[:i] for i in range(n)]
        canonical = min(rotations + ref_rotations)
        if canonical not in seen:
            seen.add(canonical)
            results.append(canonical)
    return results


def check_overlap_all_procs(ms, n, mover_word):
    """Check mover/nonmover overlap at ALL processors."""
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

    for p in range(n):
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


def enumerate_mover_words(ms, n, max_length):
    """Enumerate fair ring-adjacent mover words."""
    ring_adj = {}
    for p in range(n):
        ring_adj[p] = [(p-1) % n, (p+1) % n]

    results = []
    start_config = tuple(0 for _ in range(n))
    min_length = sum(ms)  # minimum: each proc fires m_i times

    def dfs(word, fire_counts, current_config):
        if len(word) > max_length:
            return
        if len(word) >= min_length and current_config == start_config:
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


def main():
    print("=" * 70)
    print("ALL-PROCESSOR OVERLAP: n=5..9")
    print("=" * 70)
    print("Testing mixed {2,3,4} non-consecutive orientations")
    print()

    for n in [5, 6, 7]:
        ms_base = [2, 2, 2, 4] + [3] * (n - 4)
        product = 1
        for m in ms_base:
            product *= m

        t0 = time.time()

        # For n≤7, use permutation-based necklace generation
        non_consec = generate_non_consec_necklaces(n, ms_base)

        max_len = sum(ms_base) + 6  # min cycle + some slack

        print(f"n={n}: product={product}, {len(non_consec)} non-consec orientations, "
              f"max_len={max_len}")

        total_valid = 0
        total_overlap = 0
        total_clean = 0

        for ms_tuple in non_consec:
            ms = list(ms_tuple)

            t1 = time.time()
            words = enumerate_mover_words(ms, n, max_len)
            enum_time = time.time() - t1

            ms_valid = 0
            ms_overlap = 0
            ms_clean = 0

            for word in words:
                is_valid, has_ovlp, proc = check_overlap_all_procs(ms, n, word)
                if not is_valid:
                    continue
                ms_valid += 1
                if has_ovlp:
                    ms_overlap += 1
                else:
                    ms_clean += 1

            total_valid += ms_valid
            total_overlap += ms_overlap
            total_clean += ms_clean

            if ms_clean > 0:
                print(f"  ms={ms_tuple}: {ms_valid} valid → "
                      f"{ms_overlap} overlap, {ms_clean} CLEAN ({enum_time:.1f}s)")
            elif ms_valid > 0:
                print(f"  ms={ms_tuple}: {ms_valid} valid, ALL OVERLAP ({enum_time:.1f}s)")
            sys.stdout.flush()

        elapsed = time.time() - t0

        if total_clean == 0 and total_valid > 0:
            print(f"  ★ n={n}: ALL {total_valid} cycles overlap → BLOCKED ({elapsed:.1f}s)")
        else:
            print(f"  n={n}: {total_clean}/{total_valid} clean cycles ({elapsed:.1f}s)")
        print()
        sys.stdout.flush()

    # For n=8,9: too many necklaces via permutation, use combination-based
    print(f"\n{'='*70}")
    print("n=8,9: Combination-based necklace generation + targeted test")
    print("="*70)

    for n in [8, 9]:
        ms_base = [2, 2, 2, 4] + [3] * (n - 4)
        product = 1
        for m in ms_base:
            product *= m

        # Generate necklaces via combinations
        seen = set()
        non_consec = []
        for bin_positions in combinations(range(n), 3):
            bp = sorted(bin_positions)
            has_3_consec = False
            for i in range(3):
                a, b, c = bp[i], bp[(i+1)%3], bp[(i+2)%3]
                if (b - a) % n == 1 and (c - b) % n == 1:
                    has_3_consec = True
                    break
            if has_3_consec:
                continue
            remaining = [i for i in range(n) if i not in bin_positions]
            for q_pos in remaining:
                ms_arr = [3] * n
                for bp_i in bin_positions:
                    ms_arr[bp_i] = 2
                ms_arr[q_pos] = 4
                ms_tuple = tuple(ms_arr)
                rotations = [ms_tuple[i:] + ms_tuple[:i] for i in range(n)]
                reflected = ms_tuple[::-1]
                ref_rotations = [reflected[i:] + reflected[:i] for i in range(n)]
                canonical = min(rotations + ref_rotations)
                if canonical not in seen:
                    seen.add(canonical)
                    non_consec.append(canonical)

        print(f"\nn={n}: product={product}, {len(non_consec)} non-consec orientations")

        # Test a sample of orientations with tight max_length
        max_len = sum(ms_base)  # minimum cycle length only
        sample_size = min(5, len(non_consec))
        sample = non_consec[:sample_size]

        total_valid = 0
        total_overlap = 0
        total_clean = 0

        for ms_tuple in sample:
            ms = list(ms_tuple)

            t1 = time.time()
            words = enumerate_mover_words(ms, n, max_len)
            enum_time = time.time() - t1

            ms_valid = 0
            ms_overlap = 0
            ms_clean = 0

            for word in words:
                is_valid, has_ovlp, proc = check_overlap_all_procs(ms, n, word)
                if not is_valid:
                    continue
                ms_valid += 1
                if has_ovlp:
                    ms_overlap += 1
                else:
                    ms_clean += 1

            total_valid += ms_valid
            total_overlap += ms_overlap
            total_clean += ms_clean

            status = "ALL OVERLAP" if ms_clean == 0 and ms_valid > 0 else f"{ms_clean} CLEAN"
            print(f"  ms={ms_tuple}: {ms_valid} valid → {status} ({enum_time:.1f}s)")
            sys.stdout.flush()

        if total_clean == 0 and total_valid > 0:
            print(f"  ★ n={n} (sample): ALL {total_valid} min-length cycles overlap")
        else:
            print(f"  n={n} (sample): {total_clean}/{total_valid} clean")

        # Also try max_len = min + 2
        if total_clean == 0 and n <= 8:
            max_len2 = sum(ms_base) + 2
            print(f"\n  Extending to max_len={max_len2}...")
            total_valid2 = 0
            total_clean2 = 0

            for ms_tuple in sample[:2]:
                ms = list(ms_tuple)
                t1 = time.time()
                words = enumerate_mover_words(ms, n, max_len2)
                enum_time = time.time() - t1

                for word in words:
                    if len(word) <= max_len:
                        continue  # already counted
                    is_valid, has_ovlp, proc = check_overlap_all_procs(ms, n, word)
                    if not is_valid:
                        continue
                    total_valid2 += 1
                    if not has_ovlp:
                        total_clean2 += 1

                print(f"    ms={ms_tuple}: +{total_valid2} new cycles, "
                      f"{total_clean2} clean ({enum_time:.1f}s)")
                sys.stdout.flush()

    # Also test pure {2,3} at n=7 to confirm pattern
    print(f"\n{'='*70}")
    print("PURE {2,3} at n=7: all-processor overlap")
    print("="*70)

    n = 7
    ms_base = [2, 2, 2] + [3] * (n - 3)
    non_consec = generate_non_consec_necklaces(n, ms_base)
    max_len = sum(ms_base)

    print(f"n={n}: {len(non_consec)} non-consec orientations, max_len={max_len}")

    total_valid = 0
    total_overlap = 0
    total_clean = 0

    for ms_tuple in non_consec:
        ms = list(ms_tuple)
        t1 = time.time()
        words = enumerate_mover_words(ms, n, max_len)
        enum_time = time.time() - t1

        ms_valid = 0
        ms_overlap = 0
        ms_clean = 0

        for word in words:
            is_valid, has_ovlp, proc = check_overlap_all_procs(ms, n, word)
            if not is_valid:
                continue
            ms_valid += 1
            if has_ovlp:
                ms_overlap += 1
            else:
                ms_clean += 1

        total_valid += ms_valid
        total_overlap += ms_overlap
        total_clean += ms_clean

        if ms_valid > 0:
            status = "ALL OVERLAP" if ms_clean == 0 else f"{ms_clean} CLEAN"
            print(f"  ms={ms_tuple}: {ms_valid} valid → {status} ({enum_time:.1f}s)")
        sys.stdout.flush()

    if total_clean == 0 and total_valid > 0:
        print(f"  ★ n={n}: ALL {total_valid} min-length cycles overlap")
    else:
        print(f"  n={n}: {total_clean}/{total_valid} clean")


if __name__ == "__main__":
    main()
