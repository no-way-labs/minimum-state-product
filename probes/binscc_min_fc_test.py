#!/usr/bin/env python3
"""Can all ternary simultaneously have minimum fire counts in alternating ring?

If fc[binary]=2 and fc[ternary]=3 for all, the cycle length is 5k (minimum).
With minimum (J,K), each ternary's 3 phases have (1,0),(0,1),(1,1) — all avoiding FR.

But can such a cycle EXIST? The walk and config distinctness constraints may prevent it.
"""
import time
from collections import Counter

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

def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)

def has_entry_conflict_at(ms, n, word, cycle, p):
    ell = len(word)
    bL, bR = (p-1)%n, (p+1)%n
    mover, nonmover = set(), set()
    for s in range(ell):
        lsr = (cycle[s][bL], cycle[s][p], cycle[s][bR])
        if word[s] == p: mover.add(lsr)
        else: nonmover.add(lsr)
    return bool(mover & nonmover)

# Test: minimum length cycles
for n, ms, label in [
    (5, [2,3,2,3,2], "n=5"),
    (6, [2,3,2,3,2,3], "n=6"),
]:
    ternary = [p for p in range(n) if ms[p] >= 3]
    min_len = sum(ms)  # minimum cycle length
    print(f"\n{'='*60}")
    print(f"{label}: ms={ms}, min_len={min_len}")

    # Enumerate only at minimum length
    t0 = time.time()
    words = enumerate_mover_words(ms, n, min_len)
    print(f"  Words with max_len={min_len}: {len(words)} ({time.time()-t0:.1f}s)")

    total = 0
    all_min_fc = 0
    min_fc_has_ec = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total += 1

        fc = Counter(word)
        is_min = all(fc[p] == ms[p] for p in range(n))
        if is_min:
            all_min_fc += 1
            # Check entry conflict
            has_ec = any(has_entry_conflict_at(ms, n, word, cycle, t) for t in ternary)
            if has_ec:
                min_fc_has_ec += 1
            else:
                print(f"  *** MIN-FC CYCLE WITH NO TERNARY EC: {word}")

    print(f"  Wrap-adj cycles: {total}")
    print(f"  Minimum fc cycles: {all_min_fc}")
    if all_min_fc > 0:
        print(f"  Min-fc with ternary EC: {min_fc_has_ec}/{all_min_fc}")

    # Also check slightly above minimum
    t0 = time.time()
    words2 = enumerate_mover_words(ms, n, min_len + 2)
    total2 = 0
    fc_dist = Counter()
    no_ec_fc = Counter()

    for word in words2:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total2 += 1
        fc = Counter(word)
        fc_key = tuple(fc.get(p,0) for p in range(n))
        fc_dist[fc_key] += 1

        has_ec = any(has_entry_conflict_at(ms, n, word, cycle, t) for t in ternary)
        if not has_ec:
            no_ec_fc[fc_key] += 1

    print(f"\n  With max_len={min_len+2}: {total2} cycles ({time.time()-t0:.1f}s)")
    print(f"  Fire count distributions (top 10):")
    for fk, cnt in sorted(fc_dist.items(), key=lambda x: -x[1])[:10]:
        no_ec = no_ec_fc.get(fk, 0)
        print(f"    fc={list(fk)}: {cnt} cycles, no_ec={no_ec}")

# Test at n=8 alternating with tight bounds
print(f"\n{'='*60}")
print("n=8 alt, tight analysis")
n8, ms8 = 8, [2,3,2,3,2,3,2,3]
min_len8 = sum(ms8)  # 20
t0 = time.time()
words8 = enumerate_mover_words(ms8, n8, min_len8)
print(f"  Words with max_len={min_len8}: {len(words8)} ({time.time()-t0:.1f}s)")

ternary8 = [1,3,5,7]
total8 = 0
num_failing8 = Counter()

for word in words8:
    cycle = build_cycle(ms8, n8, word)
    if cycle is None or not is_wrap_adjacent(word, n8):
        continue
    total8 += 1
    failing = sum(1 for t in ternary8 if not has_entry_conflict_at(ms8, n8, word, cycle, t))
    num_failing8[failing] += 1

print(f"  Wrap-adj: {total8}")
print(f"  Failure count dist: {dict(sorted(num_failing8.items()))}")

# Also min_len + 2
t0 = time.time()
words8b = enumerate_mover_words(ms8, n8, min_len8 + 2)
print(f"\n  Words with max_len={min_len8+2}: {len(words8b)} ({time.time()-t0:.1f}s)")

total8b = 0
num_failing8b = Counter()
for word in words8b:
    cycle = build_cycle(ms8, n8, word)
    if cycle is None or not is_wrap_adjacent(word, n8):
        continue
    total8b += 1
    failing = sum(1 for t in ternary8 if not has_entry_conflict_at(ms8, n8, word, cycle, t))
    num_failing8b[failing] += 1

print(f"  Wrap-adj: {total8b}")
print(f"  Failure count dist: {dict(sorted(num_failing8b.items()))}")
