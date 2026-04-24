#!/usr/bin/env python3
"""Quick check: is Full (L,R)-Return 100% at n=6 and n=7?"""
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

def has_full_return_at_ternary(ms, n, word, cycle, t):
    ell = len(cycle)
    bL = (t - 1) % n
    bR = (t + 1) % n
    m_t = ms[t]
    for k in range(m_t):
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
    (6, [2, 3, 2, 3, 2, 3], 24),
    (7, [2, 3, 2, 3, 2, 3, 3], 24),
]

for n, ms, max_len in configs:
    t0 = time.time()
    tern_procs = [i for i in range(n) if ms[i] > 2]
    bin_procs = [i for i in range(n) if ms[i] == 2]
    words = enumerate_mover_words(ms, n, max_len)
    t1 = time.time()
    print(f"n={n} ms={ms}: {len(words)} words ({t1-t0:.1f}s)")

    total = 0
    fr_any = 0
    fr_or_bin = 0
    entry_any = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        total += 1
        has_fr = any(has_full_return_at_ternary(ms, n, word, cycle, t) for t in tern_procs)
        has_ba = any(has_mover_alias(ms, n, word, cycle, b) for b in bin_procs)
        has_ea = any(has_mover_alias(ms, n, word, cycle, p) for p in range(n))
        if has_fr: fr_any += 1
        if has_fr or has_ba: fr_or_bin += 1
        if has_ea: entry_any += 1

    elapsed = time.time() - t0
    print(f"  Total: {total} ({elapsed:.1f}s)")
    print(f"  Full Return (any ternary): {fr_any}/{total} ({100*fr_any/total:.1f}%)")
    print(f"  Full Return OR binary:     {fr_or_bin}/{total} ({100*fr_or_bin/total:.1f}%)")
    print(f"  Entry conflict (any proc): {entry_any}/{total} ({100*entry_any/total:.1f}%)")
    sys.stdout.flush()
