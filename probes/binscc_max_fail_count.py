#!/usr/bin/env python3
"""How many sandwiched ternary can simultaneously fail FR in alternating rings?

Pattern so far:
- n=5 (2 sandwiched): at most 1 fails
- n=6 (3 sandwiched): at most 1 fails

Does this continue for n=8?
Also check non-alternating architectures: what's max simultaneous failures?
"""
import sys, time
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

def test_max_fail(n, ms, max_len, label):
    t0 = time.time()
    words = enumerate_mover_words(ms, n, max_len)
    elapsed = time.time() - t0

    ternary = [p for p in range(n) if ms[p] >= 3]
    sandwiched = [t for t in ternary if ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]
    nonsandwiched = [t for t in ternary if t not in sandwiched]

    total = 0
    num_fail_dist = Counter()
    fail_set_dist = Counter()
    max_fail = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total += 1

        failing = []
        for t in ternary:
            if not has_entry_conflict_at(ms, n, word, cycle, t):
                failing.append(t)

        num_fail_dist[len(failing)] += 1
        if failing:
            fail_set_dist[tuple(failing)] += 1
        if len(failing) > max_fail:
            max_fail = len(failing)

    print(f"\n--- {label}: n={n}, ms={ms}, max_len={max_len} ---")
    print(f"  Words: {len(words)} ({elapsed:.1f}s). Cycles: {total}")
    print(f"  Ternary: {ternary}")
    print(f"  Sandwiched: {sandwiched}, NonSand: {nonsandwiched}")

    if total == 0:
        print(f"  NO CYCLES (need larger max_len)")
        return

    print(f"  Max simultaneous ternary failures: {max_fail}")
    print(f"  Failure count distribution:")
    for nf, cnt in sorted(num_fail_dist.items()):
        print(f"    {nf} fail: {cnt} ({100*cnt/total:.1f}%)")

    if max_fail > 0:
        print(f"  Failing sets (top 15):")
        for fset, cnt in sorted(fail_set_dist.items(), key=lambda x: -x[1])[:15]:
            sand_f = [t for t in fset if t in sandwiched]
            nsand_f = [t for t in fset if t in nonsandwiched]
            print(f"    {fset} (sand={sand_f}, nsand={nsand_f}): {cnt}")

    # Any cycle with NO ternary having FR?
    no_tern_fr = num_fail_dist.get(len(ternary), 0)
    print(f"  ALL ternary fail: {no_tern_fr}")

    # Check: does SOME proc (any) always have entry conflict?
    any_ec = 0
    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        has = any(has_entry_conflict_at(ms, n, word, cycle, p) for p in range(n))
        if has:
            any_ec += 1
    print(f"  Entry conflict at ANY proc: {any_ec}/{total}")

    print(f"  Time: {time.time()-t0:.1f}s")

print("=" * 70)
print("MAX SIMULTANEOUS TERNARY FAILURES IN ALTERNATING RINGS")
print("=" * 70)

# n=5 alternating
test_max_fail(5, [2,3,2,3,2], 20, "n=5 alt")

# n=6 alternating
test_max_fail(6, [2,3,2,3,2,3], 24, "n=6 alt")

# n=7 non-alternating (has non-sandwiched)
test_max_fail(7, [2,3,2,3,2,3,3], 21, "n=7 (3bin)")

# n=8 alternating (important!)
test_max_fail(8, [2,3,2,3,2,3,2,3], 24, "n=8 alt")

# n=7 with different placement
test_max_fail(7, [2,3,3,2,3,2,3], 21, "n=7 shifted")
