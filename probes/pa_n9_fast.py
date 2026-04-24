#!/usr/bin/env python3
"""PA: Fast n=9 check — minimum cycle length only.

For n=9, ms=[2,3,2,3,2,3,3,3,3]:
min cycle = 2*3 + 3*6 = 24.
Only check cycles of length exactly 24 (M=1 for all procs).
"""
from collections import Counter
import time


def enumerate_min_length_words(ms, n):
    """Only enumerate mover words of minimum length = sum(ms)."""
    target_len = sum(ms)
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))

    def dfs(word, fc, config):
        if len(word) > target_len:
            return
        if len(word) == target_len:
            if config == start and all(fc[p] == ms[p] for p in range(n)):
                results.append(tuple(word))
            return
        remaining = target_len - len(word)
        needed = sum(ms[p] - fc[p] for p in range(n) if fc[p] < ms[p])
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            if fc[nxt] >= ms[nxt]:
                continue  # Already fired maximum
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


# Test at n=9
print("=" * 70)
print("n=9 FAST CHECK: minimum-length cycles only")
print("=" * 70)

# Try alternating placement first (smaller)
for ms_list, label in [
    ([2, 3, 2, 3, 2, 3, 2, 3, 2], "alternating 5-binary"),
    ([2, 3, 2, 3, 2, 3, 3, 3, 3], "3-binary"),
]:
    n = 9
    prod = 1
    for m in ms_list:
        prod *= m
    threshold = 4 * (3 ** (n - 2))

    print(f"\n{label}: ms={ms_list}, prod={prod}, threshold={threshold}")
    print(f"  min cycle length = {sum(ms_list)}")

    if prod >= threshold:
        print(f"  SKIP: product >= threshold")
        continue

    t0 = time.time()
    words = enumerate_min_length_words(ms_list, n)
    t1 = time.time()
    print(f"  Enumerated {len(words)} min-length words in {t1-t0:.1f}s")

    if len(words) == 0:
        print(f"  No cycles at minimum length")
        continue

    total = 0
    ec_any = 0
    no_ec = 0
    ec_boundary = 0

    boundary_t = [t for t in range(n) if ms_list[t] > 2
                  and (ms_list[(t-1)%n] == 2 or ms_list[(t+1)%n] == 2)]

    for word in words:
        cycle = build_cycle(ms_list, n, word)
        if cycle is None:
            continue
        total += 1

        ell = len(word)

        # EC at boundary ternary
        has_bt = False
        for t in boundary_t:
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
                has_bt = True
                break
        if has_bt:
            ec_boundary += 1

        # EC anywhere
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
            no_ec += 1
            print(f"  NO EC: word={word}")

        if total % 10000 == 0:
            elapsed = time.time() - t1
            print(f"  ...checked {total} cycles in {elapsed:.1f}s")

    t2 = time.time()
    print(f"\n  Checked {total} cycles in {t2-t1:.1f}s")
    print(f"  EC at boundary ternary: {ec_boundary}/{total}")
    if total > 0:
        print(f"  EC anywhere: {ec_any}/{total} ({100*ec_any/total:.1f}%)")
        print(f"  NO EC: {no_ec}")
        if no_ec == 0:
            print(f"  *** UNIVERSAL EC AT n=9 CONFIRMED ***")
