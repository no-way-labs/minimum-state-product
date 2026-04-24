#!/usr/bin/env python3
"""binscc_full_return_gap.py — Characterize cycles where Full (L,R)-Return
fails at ALL ternary procs. These are the gap cases that need binary alias.

Goal: find structural pattern that FORCES binary alias when Full Return fails.
"""

import sys
from collections import Counter, defaultdict


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


def has_full_return_at_ternary(ms, n, word, cycle, t):
    ell = len(cycle)
    bL = (t - 1) % n
    bR = (t + 1) % n
    m_t = ms[t]
    for k in range(m_t):
        phase_steps = [s for s in range(ell) if cycle[s][t] == k]
        if len(phase_steps) <= 1:
            continue
        mover_step = None
        for s in phase_steps:
            if word[s] == t:
                mover_step = s
                break
        if mover_step is None:
            continue
        mover_LR = (cycle[mover_step][bL], cycle[mover_step][bR])
        for s in phase_steps:
            if s == mover_step:
                continue
            if word[s] == t:
                continue
            step_LR = (cycle[s][bL], cycle[s][bR])
            if step_LR == mover_LR:
                return True
    return False


def main():
    print("=" * 70)
    print("FULL RETURN GAP CHARACTERIZATION")
    print("=" * 70)

    n, ms = 5, [2, 3, 2, 3, 2]
    max_len = 21
    bin_procs = [0, 2, 4]
    tern_procs = [1, 3]

    words = enumerate_mover_words(ms, n, max_len)
    print(f"n={n} ms={ms}: {len(words)} words")

    # Find cycles where Full Return fails at ALL ternary
    gap_cycles = []
    total = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        total += 1

        has_fr = any(has_full_return_at_ternary(ms, n, word, cycle, t)
                    for t in tern_procs)
        if not has_fr:
            gap_cycles.append((word, cycle))

    print(f"Total: {total}, Full Return gaps: {len(gap_cycles)}")

    # PART 1: Basic characterization
    print(f"\nPART 1: CYCLE LENGTH DISTRIBUTION")
    len_dist = Counter(len(w) for w, _ in gap_cycles)
    for l, cnt in sorted(len_dist.items()):
        print(f"  ℓ={l}: {cnt}")

    # PART 2: Phase distribution at each ternary for gap cycles
    print(f"\nPART 2: PHASE DISTRIBUTIONS (gap cycles)")
    phase_dist_counter = Counter()
    for word, cycle in gap_cycles:
        ell = len(cycle)
        for t in tern_procs:
            bL = (t - 1) % n
            bR = (t + 1) % n
            dist = []
            for k in range(ms[t]):
                ps = [s for s in range(ell) if cycle[s][t] == k]
                alpha = sum(1 for s in ps if word[s] == bL)
                delta = sum(1 for s in ps if word[s] == bR)
                dist.append((alpha, delta))
            phase_dist_counter[(t, tuple(sorted(dist)))] += 1

    for (t, dist), cnt in sorted(phase_dist_counter.items()):
        print(f"  P{t}: {dist} × {cnt}")

    # PART 3: Mover position within phase (is mover always at end?)
    print(f"\nPART 3: MOVER POSITION IN PHASE")
    mover_pos_stats = Counter()
    for word, cycle in gap_cycles[:20]:
        ell = len(cycle)
        for t in tern_procs:
            bL = (t - 1) % n
            bR = (t + 1) % n
            for k in range(ms[t]):
                ps = [s for s in range(ell) if cycle[s][t] == k]
                if len(ps) <= 1:
                    continue
                mover_idx = None
                for i, s in enumerate(ps):
                    if word[s] == t:
                        mover_idx = i
                        break
                if mover_idx is not None:
                    pos = "first" if mover_idx == 0 else \
                          "last" if mover_idx == len(ps) - 1 else \
                          f"mid({mover_idx}/{len(ps)})"
                    mover_pos_stats[pos] += 1

    for pos, cnt in sorted(mover_pos_stats.items()):
        print(f"  Mover at {pos}: {cnt}")

    # PART 4: What's the step immediately before the mover?
    print(f"\nPART 4: STEP BEFORE MOVER")
    before_mover = Counter()
    for word, cycle in gap_cycles[:20]:
        ell = len(cycle)
        for t in tern_procs:
            bL = (t - 1) % n
            bR = (t + 1) % n
            for k in range(ms[t]):
                ps = [s for s in range(ell) if cycle[s][t] == k]
                mover_step = None
                for s in ps:
                    if word[s] == t:
                        mover_step = s
                        break
                if mover_step is None:
                    continue
                prev = (mover_step - 1) % ell
                prev_proc = word[prev]
                if prev_proc == bL:
                    before_mover["bL"] += 1
                elif prev_proc == bR:
                    before_mover["bR"] += 1
                else:
                    before_mover[f"P{prev_proc}"] += 1

    for proc, cnt in sorted(before_mover.items()):
        print(f"  {proc}: {cnt}")

    # PART 5: (c[bL], c[bR]) trajectory in each phase
    print(f"\nPART 5: (c[bL], c[bR]) TRAJECTORY (first 5 gap cycles)")
    for idx, (word, cycle) in enumerate(gap_cycles[:5]):
        ell = len(cycle)
        print(f"\n  Cycle {idx}: ℓ={ell} word={word[:15]}...")
        for t in tern_procs:
            bL = (t - 1) % n
            bR = (t + 1) % n
            for k in range(ms[t]):
                ps = [s for s in range(ell) if cycle[s][t] == k]
                if len(ps) <= 1:
                    continue
                mover_step = None
                for s in ps:
                    if word[s] == t:
                        mover_step = s
                        break
                mover_LR = (cycle[mover_step][bL], cycle[mover_step][bR]) \
                    if mover_step is not None else None
                traj = []
                for s in ps:
                    lr = (cycle[s][bL], cycle[s][bR])
                    is_mover = "M" if word[s] == t else ""
                    is_bin = "b" if word[s] in (bL, bR) else ""
                    traj.append(f"{lr}{is_mover}{is_bin}")
                print(f"    P{t} phase {k}: {' '.join(traj)}  "
                      f"mover_LR={mover_LR}")

    # PART 6: Binary alias detail for gap cycles
    print(f"\nPART 6: BINARY ALIAS DETAIL")
    bin_alias_which = Counter()
    bin_alias_count = Counter()
    all_have_bin = True

    for word, cycle in gap_cycles:
        ell = len(cycle)
        has_any = False
        for b in bin_procs:
            if has_mover_alias(ms, n, word, cycle, b):
                bin_alias_which[b] += 1
                has_any = True
        if not has_any:
            all_have_bin = False
            print(f"  NO BINARY ALIAS: word={word[:15]}...")

        # Count how many binaries have alias
        cnt = sum(1 for b in bin_procs
                 if has_mover_alias(ms, n, word, cycle, b))
        bin_alias_count[cnt] += 1

    print(f"  All gap cycles have binary alias: {all_have_bin}")
    for b in bin_procs:
        cnt = bin_alias_which.get(b, 0)
        print(f"    P{b}: {cnt}/{len(gap_cycles)} "
              f"({100*cnt/len(gap_cycles):.1f}%)")
    print(f"  # binaries with alias: {dict(sorted(bin_alias_count.items()))}")

    # PART 7: For gap cycles, what's the binary's mover context multiplicity?
    print(f"\nPART 7: BINARY CONTEXT MULTIPLICITY (gap cycles)")
    for word, cycle in gap_cycles[:5]:
        ell = len(cycle)
        for b in bin_procs:
            mL = (b - 1) % n
            mR = (b + 1) % n
            ctx_steps = defaultdict(list)
            mover_ctxs = {}
            for s in range(ell):
                ctx = (cycle[s][mL], cycle[s][b], cycle[s][mR])
                ctx_steps[ctx].append(s)
                if word[s] == b:
                    mover_ctxs[ctx] = s
            for ctx, m_step in mover_ctxs.items():
                mult = len(ctx_steps[ctx])
                if mult >= 2:
                    nm = [s for s in ctx_steps[ctx] if s != m_step]
                    print(f"  P{b} ctx={ctx}: mover@{m_step}, "
                          f"nonmover@{nm} (mult={mult})")

    # PART 8: Key structural test — when Full Return fails at ternary,
    # what's the (c[bL], c[bR]) mover value at each phase?
    print(f"\nPART 8: MOVER (L,R) VALUES ACROSS PHASES")
    mover_pattern = Counter()
    for word, cycle in gap_cycles:
        ell = len(cycle)
        for t in tern_procs:
            bL = (t - 1) % n
            bR = (t + 1) % n
            vals = []
            for k in range(ms[t]):
                ps = [s for s in range(ell) if cycle[s][t] == k]
                for s in ps:
                    if word[s] == t:
                        vals.append((cycle[s][bL], cycle[s][bR]))
                        break
            # Are all 3 mover (L,R) values distinct?
            mover_pattern[(t, len(set(vals)), tuple(vals))] += 1

    for (t, ndist, vals), cnt in sorted(mover_pattern.items()):
        if cnt >= 1:
            print(f"  P{t}: {ndist} distinct, vals={vals} × {cnt}")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
