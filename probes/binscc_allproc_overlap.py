#!/usr/bin/env python3
"""binscc_allproc_overlap.py — Check overlap at ALL processors, not just binary.

The previous scripts only checked mover/nonmover overlap at binary procs.
But the SCC obstruction applies at ANY processor: if context (L,S,R) appears
both as mover (S→S') and nonmover (S→S, stay), and S'≠S, then conflict.

Key question: do the 108 survivors at ms=(2,2,3,3,2,4) have overlap at
ternary or quaternary processors?
"""

from itertools import product as iproduct
from collections import Counter
import sys


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
        return False, False, None, None

    if len(set(configs[:ell])) != ell:
        return False, False, None, None

    fire_counts = [0] * n
    for p in mover_word:
        fire_counts[p] += 1
    for p in range(n):
        if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0:
            return False, False, None, None

    for i in range(ell):
        p1 = mover_word[i]
        p2 = mover_word[(i+1) % ell]
        diff = abs(p1 - p2)
        if diff != 1 and diff != n - 1:
            return False, False, None, None

    # Check overlap at ALL processors
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
            return True, True, p, configs[:ell]

    return True, False, None, configs[:ell]


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


def main():
    print("=" * 70)
    print("ALL-PROCESSOR OVERLAP CHECK")
    print("=" * 70)
    print("Does checking overlap at ALL procs (not just binary) kill survivors?")
    print()

    # Test the surviving orientation
    for n in [5, 6]:
        for ms_label, ms_list in [
            ("pure {2,3}", [2, 2, 2] + [3] * (n - 3)),
        ]:
            seen = set()
            non_consec = []
            for perm in set(__import__('itertools').permutations(tuple(sorted(ms_list)))):
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
                    non_consec.append(canonical)

            print(f"\n--- n={n}, {ms_label}, {len(non_consec)} orientations ---")
            for ms_tuple in non_consec:
                ms = list(ms_tuple)
                max_len = 3 * n + 4
                words = enumerate_mover_words_smart(ms, n, max_len)

                total = 0
                binary_overlap = 0
                all_overlap = 0
                no_overlap = 0

                for word in words:
                    # Binary-only overlap check
                    is_valid_b, has_ovlp_b, _, _ = check_overlap_binary_only(ms, n, word)
                    if not is_valid_b:
                        continue
                    total += 1

                    # All-proc overlap check
                    _, has_ovlp_a, proc_a, _ = check_overlap_all_procs(ms, n, word)

                    if has_ovlp_b:
                        binary_overlap += 1
                    elif has_ovlp_a:
                        all_overlap += 1
                    else:
                        no_overlap += 1

                if total > 0:
                    print(f"  ms={ms_tuple}: {total} valid → "
                          f"{binary_overlap} bin_overlap + {all_overlap} nonbin_overlap + "
                          f"{no_overlap} clean")
            sys.stdout.flush()

    # Now test mixed {2,3,4}
    print(f"\n{'='*70}")
    print("MIXED {2,3,4} — ALL-PROCESSOR OVERLAP")
    print("="*70)

    for n in [5, 6]:
        ms_list = [2, 2, 2, 4] + [3] * (n - 4)
        seen = set()
        non_consec = []
        for perm in set(__import__('itertools').permutations(tuple(sorted(ms_list)))):
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
                non_consec.append(canonical)

        print(f"\nn={n}, {len(non_consec)} non-consec orientations")

        total_all = 0
        total_overlap = 0
        total_clean = 0

        for ms_tuple in non_consec:
            ms = list(ms_tuple)
            max_len = 3 * n + 4
            words = enumerate_mover_words_smart(ms, n, max_len)

            ms_total = 0
            ms_overlap = 0
            ms_clean = 0
            clean_examples = []

            for word in words:
                is_valid, has_ovlp, proc, configs = check_overlap_all_procs(ms, n, word)
                if not is_valid:
                    continue
                ms_total += 1
                if has_ovlp:
                    ms_overlap += 1
                else:
                    ms_clean += 1
                    if len(clean_examples) < 3:
                        clean_examples.append((word, configs))

            total_all += ms_total
            total_overlap += ms_overlap
            total_clean += ms_clean

            if ms_clean > 0:
                print(f"  ms={ms_tuple}: {ms_total} valid → "
                      f"{ms_overlap} overlap, {ms_clean} CLEAN")
                for word, configs in clean_examples:
                    # Show which procs have overlap
                    proc_status = []
                    for p in range(n):
                        mover_ctx = set()
                        nonmover_ctx = set()
                        for i in range(len(word)):
                            c = configs[i]
                            ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
                            if word[i] == p:
                                mover_ctx.add(ctx)
                            else:
                                nonmover_ctx.add(ctx)
                        ovlp = mover_ctx & nonmover_ctx
                        proc_status.append(f"P{p}({'OVL' if ovlp else 'ok'})")
                    print(f"    {' '.join(proc_status)}")
            else:
                print(f"  ms={ms_tuple}: {ms_total} valid, ALL OVERLAP ★")
            sys.stdout.flush()

        if total_clean == 0:
            print(f"\n  ★ ALL {total_all} valid cycles overlap at SOME processor!")
        else:
            print(f"\n  {total_clean} clean cycles remain (no overlap at any proc)")


def check_overlap_binary_only(ms, n, mover_word):
    """Check mover/nonmover overlap at binary processors only."""
    ell = len(mover_word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = mover_word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))

    if configs[-1] != configs[0]:
        return False, False, None, None
    if len(set(configs[:ell])) != ell:
        return False, False, None, None

    fire_counts = [0] * n
    for p in mover_word:
        fire_counts[p] += 1
    for p in range(n):
        if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0:
            return False, False, None, None

    for i in range(ell):
        p1 = mover_word[i]
        p2 = mover_word[(i+1) % ell]
        diff = abs(p1 - p2)
        if diff != 1 and diff != n - 1:
            return False, False, None, None

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
            return True, True, p, configs[:ell]

    return True, False, None, configs[:ell]


if __name__ == "__main__":
    main()
