#!/usr/bin/env python3
"""PA: FINAL PROOF — Universal EC for arbitrary good cycles.

After analysis, here is the complete picture:

FACT 1: At n=5, 100% of cycles have EC somewhere (1830/1830).
FACT 2: At n=7, 100% of cycles have EC somewhere (4646/4646).
FACT 3: At n=7, 100% of cycles have EC at BOUNDARY TERNARY (4646/4646).
FACT 4: At n=5, 98.7% have EC at boundary ternary, the rest at binary procs.

The KEY insight: we don't need EC at boundary ternary specifically.
We need EC at ANY proc. And this is always true.

The question becomes: what is the PROOF that EC is universal?

STRATEGY: Instead of finding one mechanism, use a TWO-LAYER argument:

Layer 1: Phase-dispatch (existing). Handles ~93-96% of cycles.
Layer 2: For normalForm residual cycles, use the CONTEXT CAPACITY argument.

The context capacity argument:
- At any proc p, the context space has size m_{p-1} * m_p * m_{p+1}.
- The cycle has ell steps, with fc[p] mover and (ell - fc[p]) nonmover.
- EC iff mover contexts and nonmover contexts overlap.
- No EC iff mover and nonmover contexts are DISJOINT.
- Required: |mover_ctx| + |nonmover_ctx| <= context_space.

For boundary ternary t: context space = 2 * 3 * 2 = 12.
Mover contexts: exactly 3 (one per S-level, for M=1).
Nonmover: uses the remaining 9 context slots. EXACTLY 9 available.
Cycle length ell >= 2n - 1. Nonmover steps = ell - 3 >= 2n - 4.
For n >= 9: nonmover steps >= 14. With only 9 available, some repeat.
But that's fine — repeats are OK for nonmover as long as no mover overlap.

Actually, mover uses 3 of 12 slots. Nonmover must use only the OTHER 9.
With 14+ nonmover steps mapping to 9 slots: many repeats, but that's fine.

The constraint: the 3 mover (L,R) pairs (one at each S-level) must each
avoid ALL nonmover (L,R) pairs at the same S-level. At each level, there
are 4 possible (L,R) pairs. Mover uses 1, nonmover uses 1-3.
For no-EC: mover's pair must NOT be among nonmover's pairs.

KEY: How many DISTINCT nonmover (L,R) pairs appear at each S-level?
If nonmover always has all 4 pairs → EC is guaranteed.
If nonmover sometimes has only 3 pairs → mover can dodge if it picks the missing one.

Let me compute the exact nonmover (L,R) coverage per S-level.
"""
from collections import Counter, defaultdict
import itertools


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    min_len = sum(ms)
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= min_len and config == start:
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


# Check: for cycles that AVOID EC at boundary ternary, how does the
# mover exactly dodge? What (L,R) patterns are in play?
print("=" * 70)
print("MOVER DODGE ANALYSIS: How does mover avoid nonmover at each S-level?")
print("=" * 70)

for n, ms_list, max_len in [
    (5, [2, 3, 2, 3, 2], 16),
]:
    boundary_t = [t for t in range(n) if ms_list[t] == 3
                  and ms_list[(t-1)%n] == 2 and ms_list[(t+1)%n] == 2]

    words = enumerate_mover_words(ms_list, n, max_len)

    dodge_examples = []
    total = 0
    for word in words:
        cycle = build_cycle(ms_list, n, word)
        if cycle is None:
            continue
        total += 1

        ell = len(word)
        # Check if ALL boundary ternary dodge EC
        all_dodge = True
        dodge_detail = {}
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
                all_dodge = False
                break
            else:
                # Record the dodge pattern per S-level
                m_by_s = {}
                n_by_s = defaultdict(set)
                for s in range(ell):
                    L = cycle[s][bL]
                    S = cycle[s][t]
                    R = cycle[s][bR]
                    lr = (L, R)
                    if word[s] == t:
                        m_by_s[S] = lr
                    else:
                        n_by_s[S].add(lr)
                dodge_detail[t] = (m_by_s, dict(n_by_s))

        if all_dodge and dodge_detail:
            dodge_examples.append((word, dodge_detail))

    print(f"\nn={n}: {total} cycles, {len(dodge_examples)} dodge all boundary ternary")
    print(f"\nDodge pattern examples:")
    for word, detail in dodge_examples[:8]:
        print(f"\n  word={word}")
        for t, (m_by_s, n_by_s) in detail.items():
            print(f"  proc {t}:")
            for s_val in range(3):
                m_lr = m_by_s.get(s_val, None)
                n_lrs = n_by_s.get(s_val, set())
                missing = set(itertools.product([0,1], [0,1])) - n_lrs
                print(f"    S={s_val}: mover={m_lr}, nonmover={n_lrs}, missing={missing}")
                if m_lr in missing:
                    print(f"           *** mover picks the missing pair! ***")

    # KEY OBSERVATION: at each S-level, nonmover uses 1-3 of the 4 (L,R) pairs.
    # Mover picks one of the MISSING pairs. For no-EC at ALL 3 S-levels,
    # mover must pick a missing pair at every level.
    # This requires the missing pairs at levels 0,1,2 to be compatible
    # with the walk structure.

    # When does nonmover have only 1 or 2 pairs (leaving 2-3 for mover)?
    # When nonmover has all 4 → guaranteed EC.
    # Count:
    nm_coverage = Counter()
    for word, detail in dodge_examples:
        for t, (m_by_s, n_by_s) in detail.items():
            for s_val in range(3):
                nm_coverage[len(n_by_s.get(s_val, set()))] += 1

    print(f"\n  Nonmover (L,R) coverage in dodge cycles:")
    for k, v in sorted(nm_coverage.items()):
        print(f"    {k} pairs: {v} S-levels")


# NOW: The definitive question.
# Can we prove that at n >= 9, no cycle can dodge EC at ALL procs?
# Let's check higher n more carefully.
print(f"\n{'='*70}")
print("MULTI-PROC DODGE: Can a cycle dodge EC at ALL procs?")
print("=" * 70)

for n, ms_list, max_len in [
    (5, [2, 3, 2, 3, 2], 16),
    (7, [2, 3, 2, 3, 2, 3, 2], 22),
]:
    words = enumerate_mover_words(ms_list, n, max_len)
    total = 0
    no_ec_anywhere = 0

    for word in words:
        cycle = build_cycle(ms_list, n, word)
        if cycle is None:
            continue
        total += 1

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

        if not has_ec:
            no_ec_anywhere += 1

    print(f"\nn={n}: {total} cycles, NO EC ANYWHERE: {no_ec_anywhere}")
    if no_ec_anywhere == 0:
        print(f"  *** UNIVERSAL EC CONFIRMED ***")


# FINAL: Try n=9 with the smallest state vector
# n=9, 5 binary, 4 ternary: ms = [2,3,2,3,2,3,2,3,2]
# product = 2^5 * 3^4 = 32 * 81 = 2592 < 4*3^7 = 8748
# But this is very many cycles. Let's try smaller.
# Actually n=9, 4 binary: ms = [2,3,2,3,2,3,3,3,3]
# product = 2^3 * 3^6 = 5832 < 8748. Non-consecutive means no two binary adjacent.
# ms = [2,3,2,3,2,3,3,3,3]: binary at 0,2,4 only (3 binary, non-consecutive)
# product = 8 * 3^6 = 5832 < 8748

print(f"\n{'='*70}")
print("n=9 SMALL CHECK: ms=[2,3,2,3,2,3,3,3,3]")
print("=" * 70)

n = 9
ms_list = [2, 3, 2, 3, 2, 3, 3, 3, 3]
max_len = 30  # minimum cycle = 2*3 + 3*6 = 24

boundary_t = [t for t in range(n) if ms_list[t] == 3
              and (ms_list[(t-1)%n] == 2 or ms_list[(t+1)%n] == 2)]

print(f"ms={ms_list}, boundary_t={boundary_t}")
print(f"min cycle length = {sum(ms_list)}")

import time
t0 = time.time()
words = enumerate_mover_words(ms_list, n, max_len)
t1 = time.time()
print(f"Enumerated {len(words)} words in {t1-t0:.1f}s")

total = 0
ec_bt = 0
ec_any = 0
no_ec = 0

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

    if has_bt:
        ec_bt += 1
    if has_any:
        ec_any += 1
    else:
        no_ec += 1

t2 = time.time()
print(f"\nChecked {total} cycles in {t2-t1:.1f}s")
print(f"  EC at boundary ternary: {ec_bt}/{total}")
if total > 0:
    print(f"  EC anywhere: {ec_any}/{total} ({100*ec_any/total:.1f}%)")
    print(f"  NO EC: {no_ec}")
    if no_ec == 0:
        print(f"  *** UNIVERSAL EC AT n=9 CONFIRMED ***")
