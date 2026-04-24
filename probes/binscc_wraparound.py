#!/usr/bin/env python3
"""Check wrap-around adjacency in cycle enumeration.
The ring walk should have word[ell-1] adjacent to word[0] for a cyclic walk.
Filter and re-check Full Return with this constraint."""
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
    """Check if last and first movers are ring-adjacent."""
    return abs(word[-1] - word[0]) % n in (1, n-1)

def has_full_return_at_ternary(ms, n, word, cycle, t):
    ell = len(cycle)
    bL = (t - 1) % n
    bR = (t + 1) % n
    for k in range(ms[t]):
        phase_steps = [s for s in range(ell) if cycle[s][t] == k]
        if len(phase_steps) <= 1:
            continue
        mover_LRs = []
        for s in phase_steps:
            if word[s] == t:
                mover_LRs.append((cycle[s][bL], cycle[s][bR]))
        if not mover_LRs:
            continue
        nonmover_LRs = set()
        for s in phase_steps:
            if word[s] != t:
                nonmover_LRs.add((cycle[s][bL], cycle[s][bR]))
        for mlr in mover_LRs:
            if mlr in nonmover_LRs:
                return True
    return False

def has_mover_alias(ms, n, word, cycle, p):
    ell = len(cycle)
    mL = (p - 1) % n
    mR = (p + 1) % n
    ctx_to_count = {}
    mover_ctxs = set()
    for step in range(ell):
        c = cycle[step]
        ctx = (c[mL], c[p], c[mR])
        ctx_to_count[ctx] = ctx_to_count.get(ctx, 0) + 1
        if word[step] == p:
            mover_ctxs.add(ctx)
    for ctx in mover_ctxs:
        if ctx_to_count[ctx] >= 2:
            return True
    return False

configs = [
    (5, [2, 3, 2, 3, 2], 21),
    (6, [2, 3, 2, 3, 2, 3], 24),
]

for n, ms, max_len in configs:
    t0 = time.time()
    tern = [i for i in range(n) if ms[i] > 2]
    binn = [i for i in range(n) if ms[i] == 2]
    words = enumerate_mover_words(ms, n, max_len)
    print(f"n={n} ms={ms}: {len(words)} words")

    total = 0
    total_wrap = 0
    total_nowrap = 0
    fr_wrap = 0
    fr_nowrap = 0
    ea_wrap = 0
    ea_nowrap = 0
    bt_wrap = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        total += 1
        ell = len(word)
        wrap = is_wrap_adjacent(word, n)

        has_fr = any(has_full_return_at_ternary(ms, n, word, cycle, t) for t in tern)
        has_ea = any(has_mover_alias(ms, n, word, cycle, p) for p in range(n))
        T = sum(1 for p in word if p in set(tern))
        B = sum(1 for p in word if p in set(binn))

        if wrap:
            total_wrap += 1
            if has_fr: fr_wrap += 1
            if has_ea: ea_wrap += 1
            if B < T: bt_wrap += 1
        else:
            total_nowrap += 1
            if has_fr: fr_nowrap += 1
            if has_ea: ea_nowrap += 1

    elapsed = time.time() - t0
    print(f"  Total: {total} ({elapsed:.1f}s)")
    print(f"  Wrap-adjacent: {total_wrap}, Non-wrap: {total_nowrap}")
    if total_wrap > 0:
        print(f"  Wrap: FR={fr_wrap}/{total_wrap} "
              f"({100*fr_wrap/total_wrap:.1f}%), "
              f"EA={ea_wrap}/{total_wrap} ({100*ea_wrap/total_wrap:.1f}%)")
        print(f"  Wrap: B<T violations: {bt_wrap}")
    if total_nowrap > 0:
        print(f"  No-wrap: FR={fr_nowrap}/{total_nowrap} "
              f"({100*fr_nowrap/total_nowrap:.1f}%), "
              f"EA={ea_nowrap}/{total_nowrap} ({100*ea_nowrap/total_nowrap:.1f}%)")
    sys.stdout.flush()
