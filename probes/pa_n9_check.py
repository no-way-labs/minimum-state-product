#!/usr/bin/env python3
"""PA: n=9 check with reasonable max length.

For n=9 alternating [2,3,2,3,2,3,2,3,2]:
- 5 binary, 4 ternary
- min fc: each fires m_p times: sum = 5*2 + 4*3 = 22
- But we need configs to be distinct, so actual min may be larger
- Try max_len up to 30

For n=9, [2,3,2,3,2,3,3,3,3]:
- 3 binary, 6 ternary
- min fc: sum = 3*2 + 6*3 = 24
- Try max_len up to 30
"""
from collections import Counter
import time


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    min_len = sum(ms)
    count = [0]

    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= min_len and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
                count[0] += 1
                if count[0] % 50000 == 0:
                    print(f"    ...found {count[0]} words so far")
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


print("=" * 70)
print("n=9 EC CHECK")
print("=" * 70)

# Try n=9 alternating with max_len=28
n = 9
for ms_list, max_len, label in [
    ([2, 3, 2, 3, 2, 3, 2, 3, 2], 28, "5-binary alternating"),
    ([2, 3, 2, 3, 2, 3, 3, 3, 3], 28, "3-binary [2,3,2,3,2,3,3,3,3]"),
]:
    prod = 1
    for m in ms_list:
        prod *= m
    threshold = 4 * (3 ** (n - 2))

    print(f"\n{label}: ms={ms_list}")
    print(f"  prod={prod}, threshold={threshold}, max_len={max_len}")

    if prod >= threshold:
        print(f"  SKIP: product >= threshold")
        continue

    t0 = time.time()
    words = enumerate_mover_words(ms_list, n, max_len)
    t1 = time.time()
    print(f"  Enumerated {len(words)} words in {t1-t0:.1f}s")

    if len(words) == 0:
        print(f"  No words found")
        continue

    boundary_t = [t for t in range(n) if ms_list[t] > 2
                  and (ms_list[(t-1)%n] == 2 or ms_list[(t+1)%n] == 2)]

    total = 0
    ec_any = 0
    no_ec_list = []

    for word in words:
        cycle = build_cycle(ms_list, n, word)
        if cycle is None:
            continue
        total += 1

        ell = len(word)
        has_any = False
        for t in range(n):
            bL = (t - 1) % n
            bR = (t + 1) % n
            mover = set()
            nonmover = set()
            for s in range(ell):
                ctx = (cycle[s][bL], cycle[s][t], cycle[s][bR])
                if word[s] == t:
                    mover.add(ctx)
                else:
                    nonmover.add(ctx)
            if mover & nonmover:
                has_any = True
                break

        if has_any:
            ec_any += 1
        else:
            no_ec_list.append(word)
            if len(no_ec_list) <= 3:
                print(f"  NO EC: word={word}")

    t2 = time.time()
    print(f"\n  Total valid cycles: {total} (checked in {t2-t1:.1f}s)")
    if total > 0:
        print(f"  EC anywhere: {ec_any}/{total} ({100*ec_any/total:.1f}%)")
        print(f"  NO EC: {len(no_ec_list)}")
        if len(no_ec_list) == 0:
            print(f"  *** UNIVERSAL EC CONFIRMED ***")
    else:
        print(f"  No valid cycles found at this max_len")


# Also try a random sample approach for n=9
print(f"\n{'='*70}")
print("n=9 RANDOM SAMPLE: generate random walks")
print("=" * 70)

import random
random.seed(42)

n = 9
ms_list = [2, 3, 2, 3, 2, 3, 2, 3, 2]
prod = 1
for m in ms_list:
    prod *= m
threshold = 4 * (3 ** (n - 2))
print(f"ms={ms_list}, prod={prod}, threshold={threshold}")

def random_walk_cycle(ms, n, max_attempts=100000):
    """Try to generate a random good cycle."""
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    start = tuple(0 for _ in range(n))

    for _ in range(max_attempts):
        config = list(start)
        word = []
        configs_seen = {start}
        pos = random.randint(0, n-1)
        config[pos] = (config[pos] + 1) % ms[pos]
        word.append(pos)

        tc = tuple(config)
        if tc in configs_seen and tc == start:
            continue  # Too short
        configs_seen.add(tc)

        for step in range(1, 200):
            neighbors = ring_adj[pos]
            nxt = random.choice(neighbors)
            new_config = list(config)
            new_config[nxt] = (new_config[nxt] + 1) % ms[nxt]
            tc = tuple(new_config)

            if tc == start:
                # Check if valid cycle
                word.append(nxt)
                fc = Counter(word)
                if all(fc.get(p, 0) > 0 and fc.get(p, 0) % ms[p] == 0 for p in range(n)):
                    return word
                word.pop()

            if tc not in configs_seen:
                configs_seen.add(tc)
                config = new_config
                word.append(nxt)
                pos = nxt
            # If already seen, try other neighbor or stop
            else:
                other = [x for x in neighbors if x != nxt]
                if other:
                    nxt2 = other[0]
                    new_config2 = list(config)
                    new_config2[nxt2] = (new_config2[nxt2] + 1) % ms[nxt2]
                    tc2 = tuple(new_config2)
                    if tc2 == start:
                        word.append(nxt2)
                        fc = Counter(word)
                        if all(fc.get(p, 0) > 0 and fc.get(p, 0) % ms[p] == 0 for p in range(n)):
                            return word
                        word.pop()
                    elif tc2 not in configs_seen:
                        configs_seen.add(tc2)
                        config = new_config2
                        word.append(nxt2)
                        pos = nxt2
                    else:
                        break
                else:
                    break

    return None

found = 0
ec_count = 0
for trial in range(200):
    word = random_walk_cycle(ms_list, n)
    if word is None:
        continue

    cycle = build_cycle(ms_list, n, word)
    if cycle is None:
        continue
    found += 1

    ell = len(word)
    has_ec = False
    for t in range(n):
        bL = (t - 1) % n
        bR = (t + 1) % n
        mover = set()
        nonmover = set()
        for s in range(ell):
            ctx = (cycle[s][bL], cycle[s][t], cycle[s][bR])
            if word[s] == t:
                mover.add(ctx)
            else:
                nonmover.add(ctx)
        if mover & nonmover:
            has_ec = True
            break
    if has_ec:
        ec_count += 1
    else:
        print(f"  NO EC in random cycle: len={ell}, word={word[:20]}...")

print(f"\n  Random cycles found: {found}")
print(f"  EC: {ec_count}/{found}")
if found > 0 and ec_count == found:
    print(f"  *** All random cycles have EC ***")
