#!/usr/bin/env python3
"""Quick check: what fire counts do the enumerated mover words have?
Do any ternary procs fire 6+ times (enabling context-dependent transitions)?"""

from itertools import product as iproduct
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


def check_fire_counts(n, ms, label):
    max_len = 3 * n + 6
    words = enumerate_mover_words_smart(ms, n, max_len)

    print(f"\n{label}: n={n} ms={ms} max_len={max_len}")
    print(f"  Total mover words: {len(words)}")

    # Check fire counts
    from collections import Counter
    length_dist = Counter()
    max_fire_per_ternary = Counter()  # maps max ternary fire count -> num words
    has_6plus = 0

    for word in words:
        ell = len(word)
        length_dist[ell] += 1
        fc = [0] * n
        for p in word:
            fc[p] += 1
        ternary_max = max(fc[p] for p in range(n) if ms[p] > 2) if any(ms[p] > 2 for p in range(n)) else 0
        max_fire_per_ternary[ternary_max] += 1
        if ternary_max >= 6:
            has_6plus += 1

    print(f"  Length distribution: {dict(sorted(length_dist.items()))}")
    print(f"  Max ternary fire count dist: {dict(sorted(max_fire_per_ternary.items()))}")
    print(f"  Words with ternary proc firing 6+ times: {has_6plus}")

    if has_6plus > 0:
        print(f"  ★ Context-dependent transitions possible for {has_6plus} words!")
    else:
        print(f"  ✓ All words have min ternary fires (3) — proc-level modes exhaustive")


check_fire_counts(5, [2, 2, 2, 3, 3], "n=5 sub-threshold")
check_fire_counts(7, [2, 2, 2, 3, 3, 3, 3], "n=7 sub-threshold")
