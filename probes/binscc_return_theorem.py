#!/usr/bin/env python3
"""binscc_return_theorem.py — Test the "return theorem" for entry conflict.

HYPOTHESIS: For ternary proc t (m=3) in a ring with ≥3 non-adjacent binary:
  t fires 3 times (states 0→1→2→0). After returning to state 0,
  if both neighbors have ALSO returned to their values at t's first firing,
  then any nonmover step with that context = conflict.

  Call t's first firing's context (L0, 0, R0).
  After t's 3rd firing, t returns to state 0.
  If t then sees (L0, 0, R0) as nonmover at ANY later step: CONFLICT.

QUESTION 1: Does (L,R) always RETURN to (L0, R0) after t completes all 3 firings?
QUESTION 2: Is this return the dominant conflict mechanism?
"""

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
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
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
    print("RETURN THEOREM: TERNARY PROC RETURN → CONFLICT")
    print("=" * 70)

    configs = [
        (5, [2, 3, 2, 3, 2], 21),
        (6, [2, 3, 2, 3, 2, 3], 24),
        (5, [2, 4, 2, 3, 2], 21),
        (5, [2, 3, 2, 4, 2], 21),
    ]

    for n, ms, max_len in configs:
        print(f"\n{'='*60}")
        print(f"n={n} ms={ms}")
        print(f"{'='*60}")

        words = enumerate_mover_words(ms, n, max_len)
        ternary_procs = [i for i in range(n) if ms[i] >= 3]
        print(f"  Ternary procs: {ternary_procs}")

        total = 0
        # For each ternary proc t, check if it returns to start context
        return_conflict = 0     # t returns to start ctx AND sees it as nonmover
        return_no_later = 0     # t returns but no nonmover step with that ctx
        no_return_conflict = 0  # t doesn't return but conflict elsewhere
        no_return_no_conflict = 0
        any_conflict = 0

        # More detailed: track per-ternary return rates
        per_t_return = {t: 0 for t in ternary_procs}
        per_t_return_conflict = {t: 0 for t in ternary_procs}

        # Track the segment structure
        segment_dist = Counter()

        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            total += 1
            ell = len(cycle)

            # Check overall conflict
            has_conflict = False
            for p in range(n):
                mL = (p-1) % n; mR = (p+1) % n
                ms_set = set(); nms_set = set()
                for step in range(ell):
                    c = cycle[step]
                    ctx = (c[mL], c[p], c[mR])
                    if word[step] == p: ms_set.add(ctx)
                    else: nms_set.add(ctx)
                if ms_set & nms_set:
                    has_conflict = True
                    break
            if has_conflict:
                any_conflict += 1

            # For each ternary, check return
            any_t_return = False
            any_t_return_conflict = False

            for t in ternary_procs:
                mL = (t-1) % n; mR = (t+1) % n
                m_t = ms[t]

                # Find all firing steps for t
                t_steps = [step for step in range(ell) if word[step] == t]
                fire_count = len(t_steps)

                if fire_count < m_t:
                    continue

                # Group into rounds of m_t firings
                for round_start in range(0, fire_count, m_t):
                    if round_start + m_t > fire_count:
                        break

                    first_step = t_steps[round_start]
                    last_step = t_steps[round_start + m_t - 1]

                    # Context at first firing
                    c_first = cycle[first_step]
                    first_ctx = (c_first[mL], c_first[t], c_first[mR])

                    # After last firing, t returns to same state
                    # Check if (L, R) also return to (L0, R0)
                    # Look at steps AFTER last firing until next t firing (or end)
                    next_t = t_steps[round_start + m_t] if round_start + m_t < fire_count else t_steps[0]

                    # After last firing: step = last_step + 1, ..., until next_t
                    step = (last_step + 1) % ell
                    returned = False
                    return_gave_conflict = False

                    while step != next_t:
                        c = cycle[step]
                        if c[t] == c_first[t]:  # same state as first firing
                            lr = (c[mL], c[mR])
                            if lr == (c_first[mL], c_first[mR]):
                                returned = True
                                # This is a nonmover step with context = first mover ctx
                                if word[step] != t:
                                    return_gave_conflict = True
                        step = (step + 1) % ell

                    if returned:
                        any_t_return = True
                        per_t_return[t] += 1
                    if return_gave_conflict:
                        any_t_return_conflict = True
                        per_t_return_conflict[t] += 1

                    # Track: how are neighbor firings distributed among t's segments?
                    # Count neighbor firings between consecutive t firings
                    seg_counts = []
                    for i in range(m_t):
                        start = t_steps[round_start + i]
                        end = t_steps[round_start + (i + 1) % m_t] if i + 1 < m_t else t_steps[round_start]
                        if end <= start:
                            end += ell
                        count = 0
                        for s in range(start + 1, end):
                            s_mod = s % ell
                            if word[s_mod] == mL or word[s_mod] == mR:
                                count += 1
                        seg_counts.append(count)
                    segment_dist[tuple(seg_counts)] += 1

            if any_t_return_conflict:
                return_conflict += 1
            elif any_t_return:
                return_no_later += 1
            elif has_conflict:
                no_return_conflict += 1
            else:
                no_return_no_conflict += 1

        print(f"  Total valid: {total}")
        print(f"  Any conflict: {any_conflict}/{total} ({100*any_conflict/total:.1f}%)")
        print(f"  Return + conflict: {return_conflict}")
        print(f"  Return, no conflict at return: {return_no_later}")
        print(f"  No return, conflict elsewhere: {no_return_conflict}")
        print(f"  No return, no conflict: {no_return_no_conflict}")
        print()
        print(f"  Per-ternary return rates:")
        for t in ternary_procs:
            pct = 100 * per_t_return[t] / total if total > 0 else 0
            cpct = 100 * per_t_return_conflict[t] / total if total > 0 else 0
            print(f"    P{t} (m={ms[t]}): return {per_t_return[t]}/{total} ({pct:.1f}%), "
                  f"return+conflict {per_t_return_conflict[t]}/{total} ({cpct:.1f}%)")

        if segment_dist:
            print(f"\n  Neighbor firing distribution across t's segments (top 10):")
            for k, v in sorted(segment_dist.items(), key=lambda x: -x[1])[:10]:
                print(f"    {k}: {v}")


    # PART 2: The binary neighbor return argument
    print(f"\n\n{'='*70}")
    print("PART 2: WHY DO BINARY NEIGHBORS RETURN?")
    print("=" * 70)
    print()
    print("For ternary t with binary neighbors bL, bR:")
    print("  bL fires 2× (0→1→0), bR fires 2× (0→1→0).")
    print("  After full cycle: both return to 0.")
    print("  KEY: If both bL and bR complete their 2 firings BETWEEN t's")
    print("  first and last firing, then (L,R) returns → conflict.")
    print()
    print("  With 3 non-adj binary: each ternary is sandwiched by binary.")
    print("  Binary fires 2× in ℓ steps. Distribution across t's segments matters.")
    print()

    # Check: for each ternary, how often do BOTH binary neighbors return
    n, ms = 5, [2, 3, 2, 3, 2]
    words = enumerate_mover_words(ms, n, 21)

    for t in [1, 3]:
        mL = (t-1) % n; mR = (t+1) % n
        both_return = 0
        L_return = 0
        R_return = 0
        neither = 0
        total2 = 0

        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            total2 += 1
            ell = len(cycle)

            # Find t's first and last firing
            t_steps = [s for s in range(ell) if word[s] == t]
            if len(t_steps) < ms[t]:
                continue

            first = t_steps[0]
            last = t_steps[ms[t]-1]

            # Count mL and mR firings between first and last (inclusive range)
            mL_between = 0
            mR_between = 0
            if last > first:
                for s in range(first, last + 1):
                    if word[s] == mL: mL_between += 1
                    if word[s] == mR: mR_between += 1
            else:
                for s in range(first, ell):
                    if word[s] == mL: mL_between += 1
                    if word[s] == mR: mR_between += 1
                for s in range(0, last + 1):
                    if word[s] == mL: mL_between += 1
                    if word[s] == mR: mR_between += 1

            L_ret = (mL_between % ms[mL] == 0) and mL_between > 0
            R_ret = (mR_between % ms[mR] == 0) and mR_between > 0

            if L_ret and R_ret:
                both_return += 1
            elif L_ret:
                L_return += 1
            elif R_ret:
                R_return += 1
            else:
                neither += 1

        print(f"  P{t}: both return={both_return}, L only={L_return}, R only={R_return}, neither={neither} (total={total2})")

    # PART 3: The counting constraint
    print(f"\n\n{'='*70}")
    print("PART 3: COUNTING CONSTRAINT ON NEIGHBOR RETURNS")
    print("=" * 70)
    print()
    print("3 ternary segments per ternary proc (between its 3 firings).")
    print("2 binary neighbors, each firing 2×.")
    print("By pigeonhole: 4 neighbor firings across 3 segments →")
    print("some segment has ≥ 2 neighbor firings.")
    print()
    print("But we need BOTH neighbors to complete their 2 firings between")
    print("t's first and last firing. That's 4 firings in the 'middle' segments.")
    print()

    # Check: what fraction of the ℓ steps are between t's 1st and last firing?
    n, ms = 5, [2, 3, 2, 3, 2]
    words = enumerate_mover_words(ms, n, 21)

    span_dist = Counter()
    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        ell = len(cycle)
        for t in [1, 3]:
            t_steps = [s for s in range(ell) if word[s] == t]
            span = (t_steps[-1] - t_steps[0]) % ell
            span_dist[(t, span)] += 1

    print("  Span (first to last t-firing) distribution:")
    for k in sorted(span_dist.keys()):
        print(f"    P{k[0]} span={k[1]}: {span_dist[k]}")


if __name__ == "__main__":
    main()
