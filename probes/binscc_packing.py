#!/usr/bin/env python3
"""Verify: at n=6 alternating, no two ternary firings are adjacent in
any valid cycle. This implies binary firings >= ternary firings (packing).
Also check minimum cycle length."""
import sys

def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n)
                      if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            dfs(word, nf, tuple(nc))
            word.pop()
    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))
    return results

def build_cycle(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]

# n=6 alternating
n, ms = 6, [2, 3, 2, 3, 2, 3]
tern = {1, 3, 5}
binn = {0, 2, 4}

words = enumerate_mover_words(ms, n, 24)
print(f"n={n} ms={ms}: {len(words)} words")

from collections import Counter
len_dist = Counter()
adj_tern = 0  # consecutive ternary firings
min_gap_size = float('inf')  # minimum gap between ternary firings

total = 0
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None:
        continue
    total += 1
    ell = len(word)
    len_dist[ell] += 1

    # Check consecutive ternary firings
    for i in range(ell):
        if word[i] in tern and word[(i+1) % ell] in tern:
            adj_tern += 1

    # Count gap sizes between consecutive ternary firings
    t_positions = [i for i in range(ell) if word[i] in tern]
    for j in range(len(t_positions)):
        gap = (t_positions[(j+1) % len(t_positions)] - t_positions[j]) % ell - 1
        if gap < min_gap_size:
            min_gap_size = gap

print(f"Total cycles: {total}")
print(f"Adjacent ternary firings: {adj_tern}")
print(f"Min gap between ternary firings: {min_gap_size}")
print(f"\nCycle length distribution:")
for l, cnt in sorted(len_dist.items()):
    print(f"  ℓ={l}: {cnt}")

# Verify B >= T for all cycles
bt_violations = 0
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None:
        continue
    ell = len(word)
    T = sum(1 for p in word if p in tern)
    B = sum(1 for p in word if p in binn)
    if B < T:
        bt_violations += 1
print(f"\nB < T violations: {bt_violations}/{total}")

# Quick check for n=5
print(f"\n{'='*60}")
n5, ms5 = 5, [2, 3, 2, 3, 2]
tern5 = {1, 3}
words5 = enumerate_mover_words(ms5, n5, 21)
total5 = 0
bt5 = 0
len5 = Counter()
for word in words5:
    cycle = build_cycle(ms5, n5, word)
    if cycle is None:
        continue
    total5 += 1
    ell = len(word)
    len5[ell] += 1
    T = sum(1 for p in word if p in tern5)
    B = sum(1 for p in word if p in {0,2,4})
    if B < T:
        bt5 += 1
print(f"n=5 ms={ms5}: {total5} cycles")
print(f"B < T violations at n=5: {bt5}/{total5}")
print(f"Lengths: {dict(sorted(len5.items()))}")

sys.stdout.flush()
