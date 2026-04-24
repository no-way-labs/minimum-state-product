#!/usr/bin/env python3
"""binscc_guaranteed_alias.py — Test provable alias mechanisms.

PROVED MECHANISM 1 (Pure Return):
For ternary t between binary bL, bR: if in some phase k,
bL fires ≥2 times and bR fires 0 times (or vice versa),
then bL toggles back to start while bR is fixed → (c[bL],c[bR])
returns to start value → nonmover step at start matches mover → alias.

PROVED MECHANISM 2 (Pigeonhole Repeat):
If α_k + δ_k ≥ 4 in some phase, then ≥5 segments of (c[bL],c[bR])
on {0,1}^2 → value must repeat → some segment matches mover's segment
→ alias (if mover's segment is one of the repeated segments).
Actually not quite: need the MOVER segment to repeat. May need α_k+δ_k ≥ 5.

QUESTION: Does Mechanism 1 alone (at ANY ternary) cover 100% of cycles?
"""

import sys
from collections import Counter, defaultdict
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


def has_pure_return_at_ternary(ms, n, word, cycle, t):
    """Check if ternary t has the Pure Return mechanism:
    some phase k has one binary neighbor firing ≥2 and the other firing 0.
    This GUARANTEES alias (proved analytically).

    BUT: also need ≥2 steps in the phase (otherwise no nonmover step).
    """
    ell = len(cycle)
    bL = (t - 1) % n
    bR = (t + 1) % n
    m_t = ms[t]

    for k in range(m_t):
        # Steps in phase k
        phase_steps = [s for s in range(ell) if cycle[s][t] == k]
        if len(phase_steps) <= 1:
            continue  # degenerate phase

        alpha = sum(1 for s in phase_steps if word[s] == bL)
        delta = sum(1 for s in phase_steps if word[s] == bR)

        if (alpha >= 2 and delta == 0) or (alpha == 0 and delta >= 2):
            return True

    return False


def has_full_return_at_ternary(ms, n, word, cycle, t):
    """Stronger: check if (c[bL], c[bR]) returns to its value at any
    mover step within the same phase. This is the actual alias condition."""
    ell = len(cycle)
    bL = (t - 1) % n
    bR = (t + 1) % n
    m_t = ms[t]

    for k in range(m_t):
        phase_steps = [s for s in range(ell) if cycle[s][t] == k]
        if len(phase_steps) <= 1:
            continue

        # Find mover step in this phase
        mover_step = None
        for s in phase_steps:
            if word[s] == t:
                mover_step = s
                break
        if mover_step is None:
            continue  # no mover in this phase (shouldn't happen)

        mover_LR = (cycle[mover_step][bL], cycle[mover_step][bR])

        # Check nonmover steps
        for s in phase_steps:
            if s == mover_step:
                continue
            if word[s] == t:
                continue  # another mover (multi-round)
            step_LR = (cycle[s][bL], cycle[s][bR])
            if step_LR == mover_LR:
                return True

    return False


def main():
    print("=" * 70)
    print("GUARANTEED ALIAS MECHANISMS")
    print("=" * 70)

    configs = [
        (5, [2, 3, 2, 3, 2], 21),
        (6, [2, 3, 2, 3, 2, 3], 24),
    ]

    for n, ms, max_len in configs:
        print(f"\n{'='*60}")
        print(f"n={n} ms={ms}")
        tern_procs = [i for i in range(n) if ms[i] > 2]
        bin_procs = [i for i in range(n) if ms[i] == 2]

        t0 = time.time()
        words = enumerate_mover_words(ms, n, max_len)
        t1 = time.time()
        print(f"  {len(words)} words ({t1-t0:.1f}s)")

        total = 0
        pure_return_any = 0  # any ternary has pure return
        full_return_any = 0  # any ternary has full return
        mover_alias_any = 0  # any proc has mover alias
        bin_alias_any = 0    # any binary has mover alias

        # Combined coverage
        pure_or_bin = 0
        full_or_bin = 0

        # Per-mechanism counters
        pure_return_per_t = Counter()
        full_return_per_t = Counter()

        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            total += 1

            has_pr = any(has_pure_return_at_ternary(ms, n, word, cycle, t)
                        for t in tern_procs)
            has_fr = any(has_full_return_at_ternary(ms, n, word, cycle, t)
                        for t in tern_procs)
            has_ma = any(has_mover_alias(ms, n, word, cycle, p)
                        for p in range(n))
            has_ba = any(has_mover_alias(ms, n, word, cycle, b)
                        for b in bin_procs)

            if has_pr:
                pure_return_any += 1
            if has_fr:
                full_return_any += 1
            if has_ma:
                mover_alias_any += 1
            if has_ba:
                bin_alias_any += 1
            if has_pr or has_ba:
                pure_or_bin += 1
            if has_fr or has_ba:
                full_or_bin += 1

            for t in tern_procs:
                if has_pure_return_at_ternary(ms, n, word, cycle, t):
                    pure_return_per_t[t] += 1
                if has_full_return_at_ternary(ms, n, word, cycle, t):
                    full_return_per_t[t] += 1

        elapsed = time.time() - t0
        print(f"  Total: {total} ({elapsed:.1f}s)")
        print(f"\n  Mechanism coverage:")
        print(f"    Pure return (any ternary): "
              f"{pure_return_any}/{total} ({100*pure_return_any/total:.1f}%)")
        print(f"    Full (L,R)-return (any ternary): "
              f"{full_return_any}/{total} ({100*full_return_any/total:.1f}%)")
        print(f"    Mover alias (any proc): "
              f"{mover_alias_any}/{total} ({100*mover_alias_any/total:.1f}%)")
        print(f"    Binary alias (any binary): "
              f"{bin_alias_any}/{total} ({100*bin_alias_any/total:.1f}%)")
        print(f"\n  Combined coverage:")
        print(f"    Pure return OR binary: "
              f"{pure_or_bin}/{total} ({100*pure_or_bin/total:.1f}%)")
        print(f"    Full return OR binary: "
              f"{full_or_bin}/{total} ({100*full_or_bin/total:.1f}%)")

        print(f"\n  Per-ternary:")
        for t in tern_procs:
            print(f"    P{t}: pure={pure_return_per_t[t]} "
                  f"({100*pure_return_per_t[t]/total:.1f}%), "
                  f"full={full_return_per_t[t]} "
                  f"({100*full_return_per_t[t]/total:.1f}%)")

        # Analyze non-covered cycles (if any)
        non_covered = total - (pure_or_bin if pure_or_bin > 0 else 0)
        if pure_or_bin < total:
            print(f"\n  NON-COVERED by pure_return OR binary: "
                  f"{total - pure_or_bin}")
            count = 0
            for word in words:
                cycle = build_cycle(ms, n, word)
                if cycle is None:
                    continue
                has_pr = any(has_pure_return_at_ternary(ms, n, word, cycle, t)
                            for t in tern_procs)
                has_ba = any(has_mover_alias(ms, n, word, cycle, b)
                            for b in bin_procs)
                if has_pr or has_ba:
                    continue
                # This cycle not covered
                ell = len(cycle)
                print(f"    ℓ={ell} word={word[:12]}...")
                # Check which ternary has full return
                for t in tern_procs:
                    if has_full_return_at_ternary(ms, n, word, cycle, t):
                        bL = (t-1) % n
                        bR = (t+1) % n
                        # Show phase details
                        for k in range(ms[t]):
                            ps = [s for s in range(ell) if cycle[s][t] == k]
                            a = sum(1 for s in ps if word[s] == bL)
                            d = sum(1 for s in ps if word[s] == bR)
                            print(f"      P{t} phase {k}: α={a} δ={d} "
                                  f"({len(ps)} steps)")
                count += 1
                if count >= 5:
                    break

        if full_or_bin < total:
            print(f"\n  NON-COVERED by full_return OR binary: "
                  f"{total - full_or_bin}")
            count = 0
            for word in words:
                cycle = build_cycle(ms, n, word)
                if cycle is None:
                    continue
                has_fr = any(has_full_return_at_ternary(ms, n, word, cycle, t)
                            for t in tern_procs)
                has_ba = any(has_mover_alias(ms, n, word, cycle, b)
                            for b in bin_procs)
                if has_fr or has_ba:
                    continue
                # Which proc saves?
                ell = len(cycle)
                savers = [p for p in range(n)
                          if has_mover_alias(ms, n, word, cycle, p)]
                print(f"    ℓ={ell} saved by: {savers}")
                count += 1
                if count >= 5:
                    break

        sys.stdout.flush()


if __name__ == "__main__":
    main()
