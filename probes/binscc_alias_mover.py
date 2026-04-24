#!/usr/bin/env python3
"""binscc_alias_mover.py — Does alias≥2 always hit a mover context?

KEY QUESTION: For every good cycle with ≥3 non-adjacent binary at sub-threshold,
does alias≥2 ALWAYS occur at a MOVER context of some proc?

We know alias≥2 occurs at SOME context (pigeonhole from context bound).
Need: alias≥2 at a mover context → entry conflict.

Check: for every proc p and every cycle, how many mover contexts have alias≥2?
If 0 at all procs → no conflict. But computationally this should be impossible.
"""

import sys
from collections import Counter
import time


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 6 and config == start:
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


def main():
    print("=" * 70)
    print("ALIAS AT MOVER CONTEXT: UNIVERSAL CHECK")
    print("=" * 70)

    configs_list = [
        (5, [2, 3, 2, 3, 2], 21),
        (6, [2, 3, 2, 3, 2, 3], 24),
    ]

    for n, ms, max_len in configs_list:
        print(f"\n{'='*60}")
        print(f"n={n} ms={ms}")

        t0 = time.time()
        words = enumerate_mover_words(ms, n, max_len)
        t1 = time.time()
        print(f"  {len(words)} words ({t1-t0:.1f}s)")

        total = 0
        # Count cycles where alias≥2 at a MOVER context of ANY proc
        mover_alias = 0
        # Count where alias≥2 at some context but NOT at any mover context
        nonmover_alias_only = 0
        # Per-proc detail
        per_proc_mover_alias = Counter()
        per_proc_any_alias = Counter()

        # The key: context bound and actual distinct context counts
        context_bound_dist = Counter()

        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            total += 1
            ell = len(cycle)

            found_mover_alias = False
            found_any_alias = False

            for p in range(n):
                mL = (p - 1) % n
                mR = (p + 1) % n

                # Build context → config count map
                ctx_to_count = {}
                mover_ctxs = set()
                for step in range(ell):
                    c = cycle[step]
                    ctx = (c[mL], c[p], c[mR])
                    ctx_to_count[ctx] = ctx_to_count.get(ctx, 0) + 1
                    if word[step] == p:
                        mover_ctxs.add(ctx)

                # Check alias at mover contexts
                for ctx in mover_ctxs:
                    if ctx_to_count[ctx] >= 2:
                        found_mover_alias = True
                        per_proc_mover_alias[p] += 1
                        break

                # Check alias at any context
                if any(v >= 2 for v in ctx_to_count.values()):
                    found_any_alias = True
                    per_proc_any_alias[p] += 1

                # Context bound: F_p + 1
                F_p = ms[mL] + ms[p] + ms[mR]
                actual_distinct = len(ctx_to_count)
                context_bound_dist[(p, actual_distinct, F_p + 1)] += 1

            if found_mover_alias:
                mover_alias += 1
            elif found_any_alias:
                nonmover_alias_only += 1

        elapsed = time.time() - t0
        print(f"  Total valid: {total} ({elapsed:.1f}s)")
        print(f"  Mover alias (alias≥2 at mover ctx): "
              f"{mover_alias}/{total} ({100*mover_alias/total:.1f}%)")
        print(f"  Nonmover alias only: "
              f"{nonmover_alias_only}/{total} ({100*nonmover_alias_only/total:.1f}%)")
        print(f"  No alias at all: "
              f"{total-mover_alias-nonmover_alias_only}/{total}")
        print(f"\n  Per-proc mover alias rates:")
        for p in range(n):
            print(f"    P{p} (m={ms[p]}): "
                  f"{per_proc_mover_alias.get(p,0)}/{total} "
                  f"({100*per_proc_mover_alias.get(p,0)/total:.1f}%)")

        # Show context bound analysis for first proc
        print(f"\n  Context bound vs actual (P0):")
        p0_data = {(a, b): v for (p, a, b), v in context_bound_dist.items()
                   if p == 0}
        for (actual, bound), v in sorted(p0_data.items()):
            pct = 100 * v / total
            status = "★alias" if actual < ell else ""
            print(f"    actual={actual} bound={bound}: "
                  f"{v} ({pct:.1f}%) {status}")

        # The definitive question: alias≥2 at mover = entry conflict?
        print(f"\n  EQUIVALENCE CHECK:")
        conflict_count = 0
        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            ell = len(cycle)
            for p in range(n):
                mL = (p - 1) % n
                mR = (p + 1) % n
                ms_set = set()
                nms_set = set()
                for step in range(ell):
                    c = cycle[step]
                    ctx = (c[mL], c[p], c[mR])
                    if word[step] == p:
                        ms_set.add(ctx)
                    else:
                        nms_set.add(ctx)
                if ms_set & nms_set:
                    conflict_count += 1
                    break
        print(f"    Entry conflict (any proc): {conflict_count}/{total}")
        print(f"    Mover alias (any proc): {mover_alias}/{total}")
        diff = conflict_count - mover_alias
        print(f"    Conflict but NOT mover-alias: {diff}")
        if diff > 0:
            print(f"    These {diff} have conflict at a proc where "
                  f"alias<2 at mover, but alias≥2 at nonmover")

        sys.stdout.flush()


if __name__ == "__main__":
    main()
