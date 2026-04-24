#!/usr/bin/env python3
"""binscc_conflict_anatomy_nc.py — Anatomy of entry conflicts for non-consecutive binary.

For ≥3 non-adjacent binary, analyze WHERE conflicts occur:
- Which processor has the conflict?
- Is it at a binary proc or a non-binary neighbor?
- Is the conflicting context from a binary UP/DOWN move?
- What's the (L,S,R) pattern?

Goal: understand the mechanism well enough to prove it analytically.
"""

from itertools import product as iproduct
from collections import Counter, defaultdict
import sys
import time


def enumerate_mover_words(ms, n, max_length):
    """Enumerate fair ring-adjacent mover words returning to start config."""
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))

    def dfs(word, fire_counts, config):
        if len(word) > max_length:
            return
        if len(word) >= 6 and config == start:
            if all(fire_counts[p] > 0 and fire_counts[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fire_counts[p]) for p in range(n)
                     if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            new_config = list(config)
            new_config[nxt] = (new_config[nxt] + 1) % ms[nxt]
            new_config = tuple(new_config)
            new_counts = list(fire_counts)
            new_counts[nxt] += 1
            word.append(nxt)
            dfs(word, new_counts, new_config)
            word.pop()

    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))
    return results


def build_cycle(ms, n, word):
    """Build config sequence from mover word. Returns cycle configs or None."""
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


def analyze_conflicts(cycle, ms, n, word):
    """Detailed conflict analysis. Returns list of conflict records."""
    ell = len(cycle)
    bin_procs = set(i for i in range(n) if ms[i] == 2)

    # Build mover and nonmover entry sets per processor
    mover_entries = defaultdict(set)    # proc -> set of (L,S,R)
    nonmover_entries = defaultdict(set)  # proc -> set of (L,S,R)
    mover_details = defaultdict(list)   # (proc, L, S, R) -> step indices
    nonmover_details = defaultdict(list)

    for step in range(ell):
        c = cycle[step]
        c_next = cycle[(step + 1) % ell]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return None
        mover = diffs[0]

        # Mover entry
        L_m = c[(mover-1) % n]
        S_m = c[mover]
        R_m = c[(mover+1) % n]
        mover_entries[mover].add((L_m, S_m, R_m))
        mover_details[(mover, L_m, S_m, R_m)].append(step)

        # Nonmover entries
        for j in range(n):
            if j != mover:
                L_j = c[(j-1) % n]
                S_j = c[j]
                R_j = c[(j+1) % n]
                nonmover_entries[j].add((L_j, S_j, R_j))
                nonmover_details[(j, L_j, S_j, R_j)].append(step)

    # Find conflicts: (L,S,R) appears in both mover and nonmover for same proc
    conflicts = []
    for proc in range(n):
        overlap = mover_entries[proc] & nonmover_entries[proc]
        for ctx in overlap:
            L, S, R = ctx
            # The mover entry says f(L,S,R) = S' ≠ S
            # The nonmover entry says f(L,S,R) = S
            # These conflict iff S' ≠ S, which is always true for mover
            conflicts.append({
                'proc': proc,
                'ctx': (L, S, R),
                'is_binary': proc in bin_procs,
                'L_binary': (proc-1) % n in bin_procs,
                'R_binary': (proc+1) % n in bin_procs,
                'mover_steps': mover_details[(proc, L, S, R)],
                'nonmover_steps': nonmover_details[(proc, L, S, R)],
                'S_val': S,
            })

    return conflicts


def main():
    print("=" * 70)
    print("CONFLICT ANATOMY: NON-CONSECUTIVE BINARY SYSTEMS")
    print("=" * 70)
    print()

    test_configs = [
        # (n, ms, label, max_len)
        (5, [2, 3, 2, 3, 2], "3B alternating", 21),
        (5, [2, 4, 2, 3, 2], "3B alt mixed", 21),
        (6, [2, 3, 2, 3, 2, 3], "3B alternating", 24),
        (6, [2, 4, 2, 3, 2, 3], "3B alt mixed", 24),
        (7, [2, 3, 2, 3, 2, 3, 3], "3B spread", 27),
        (7, [2, 4, 2, 3, 2, 3, 3], "3B spread mixed", 27),
    ]

    for n, ms, label, max_len in test_configs:
        print(f"\n{'='*60}")
        print(f"n={n} ms={ms} [{label}]")
        print(f"{'='*60}")
        sys.stdout.flush()

        bin_procs = [i for i in range(n) if ms[i] == 2]
        nb_procs = [i for i in range(n) if ms[i] > 2]
        print(f"  Binary procs: {bin_procs}")
        print(f"  Non-binary procs: {nb_procs}")

        t0 = time.time()
        words = enumerate_mover_words(ms, n, max_len)
        t1 = time.time()
        print(f"  {len(words)} mover words ({t1-t0:.1f}s)")

        # Detailed anatomy
        conflict_proc_counts = Counter()
        conflict_type_counts = Counter()
        conflict_ctx_counts = Counter()
        conflict_binary_neighbor = Counter()
        total_valid = 0
        total_conflicting = 0
        first_examples = []
        no_conflict_examples = []

        # Track: which binary proc's firing causes the conflict?
        binary_cause = Counter()  # which binary proc's UP/DOWN creates the overlapping ctx

        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            total_valid += 1

            conflicts = analyze_conflicts(cycle, ms, n, word)
            if conflicts is None:
                continue

            if len(conflicts) > 0:
                total_conflicting += 1
                for conf in conflicts:
                    proc = conf['proc']
                    conflict_proc_counts[proc] += 1
                    L, S, R = conf['ctx']

                    # Classify conflict type
                    if conf['is_binary']:
                        conflict_type_counts['at_binary'] += 1
                    else:
                        conflict_type_counts['at_nonbinary'] += 1

                    # Count binary neighbors of conflicting proc
                    bn = sum([conf['L_binary'], conf['R_binary']])
                    conflict_binary_neighbor[bn] += 1

                    # Track which neighbor values are binary (0 or 1)
                    L_is_bin = L in (0, 1) and (proc-1) % n in bin_procs
                    R_is_bin = R in (0, 1) and (proc+1) % n in bin_procs
                    conflict_ctx_counts[(L_is_bin, R_is_bin)] += 1

                if len(first_examples) < 5:
                    first_examples.append((word, conflicts))
            else:
                no_conflict_examples.append(word)

        elapsed = time.time() - t0
        print(f"  Valid: {total_valid}, Conflicting: {total_conflicting} ({elapsed:.1f}s)")

        if total_valid == 0:
            continue

        pct = 100 * total_conflicting / total_valid
        print(f"  Conflict rate: {pct:.1f}%")

        if total_conflicting == total_valid:
            print(f"  ★ 100% conflict rate!")

        print(f"\n  Conflict processor distribution:")
        for proc in sorted(conflict_proc_counts.keys()):
            is_bin = "BINARY" if ms[proc] == 2 else f"m={ms[proc]}"
            print(f"    P{proc} ({is_bin}): {conflict_proc_counts[proc]} conflicts")

        print(f"\n  Conflict location type:")
        for k, v in sorted(conflict_type_counts.items()):
            print(f"    {k}: {v}")

        print(f"\n  Binary neighbors of conflicting proc:")
        for k, v in sorted(conflict_binary_neighbor.items()):
            print(f"    {k} binary neighbors: {v}")

        print(f"\n  Context binary-neighbor pattern (L_bin, R_bin):")
        for k, v in sorted(conflict_ctx_counts.items()):
            print(f"    {k}: {v}")

        if first_examples:
            print(f"\n  First 3 detailed examples:")
            for word, conflicts in first_examples[:3]:
                print(f"    word={word}")
                for conf in conflicts[:3]:
                    p = conf['proc']
                    L, S, R = conf['ctx']
                    print(f"      P{p} ctx=({L},{S},{R}) [{'BIN' if conf['is_binary'] else 'NB'}]"
                          f" mover@{conf['mover_steps'][:3]} nonmover@{conf['nonmover_steps'][:3]}")

        if no_conflict_examples:
            print(f"\n  !! {len(no_conflict_examples)} cycles WITHOUT conflict!")
            for w in no_conflict_examples[:3]:
                print(f"    {w}")

        sys.stdout.flush()

    # Part 2: Focus on the binary processor itself
    print(f"\n\n{'='*70}")
    print("PART 2: BINARY PROCESSOR SELF-CONFLICT ANALYSIS")
    print("=" * 70)
    print()
    print("For each binary proc, check if IT has a self-conflict:")
    print("  binary proc p fires UP at (L,0,R) and is nonmover at (L,0,R)")
    print("  OR fires DOWN at (L,1,R) and is nonmover at (L,1,R)")
    print()

    for n, ms, label, max_len in test_configs[:4]:  # n=5,6
        print(f"\n--- n={n} ms={ms} [{label}] ---")
        bin_procs = [i for i in range(n) if ms[i] == 2]

        words = enumerate_mover_words(ms, n, max_len)
        total = 0
        binary_self = 0
        nb_only = 0

        binary_self_which = Counter()  # which binary proc has self-conflict

        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            total += 1

            ell = len(cycle)
            has_binary_self = False
            has_nb_conflict = False

            for proc in range(n):
                mover_ctxs = set()
                nonmover_ctxs = set()
                for step in range(ell):
                    c = cycle[step]
                    c_next = cycle[(step+1) % ell]
                    diffs = [j for j in range(n) if c[j] != c_next[j]]
                    mover = diffs[0]
                    L = c[(proc-1) % n]
                    S = c[proc]
                    R = c[(proc+1) % n]
                    if mover == proc:
                        mover_ctxs.add((L, S, R))
                    else:
                        nonmover_ctxs.add((L, S, R))

                overlap = mover_ctxs & nonmover_ctxs
                if overlap:
                    if ms[proc] == 2:
                        has_binary_self = True
                        binary_self_which[proc] += 1
                    else:
                        has_nb_conflict = True

            if has_binary_self:
                binary_self += 1
            elif has_nb_conflict:
                nb_only += 1

        print(f"  Valid: {total}")
        print(f"  Binary self-conflict: {binary_self} ({100*binary_self/total:.1f}%)")
        print(f"  Non-binary only conflict: {nb_only} ({100*nb_only/total:.1f}%)")
        print(f"  No conflict: {total - binary_self - nb_only}")
        print(f"  Binary self-conflict by proc: {dict(binary_self_which)}")
        sys.stdout.flush()

    # Part 3: Minimal conflict analysis — what's the SIMPLEST conflict?
    print(f"\n\n{'='*70}")
    print("PART 3: MINIMAL CONFLICT — BINARY UP/DOWN OVERLAP")
    print("=" * 70)
    print()
    print("For binary proc p: it fires UP at some (L,0,R) and DOWN at some (L',1,R').")
    print("For conflict: need (L,0,R) or (L',1,R') to also appear as nonmover.")
    print("Check: when p is nonmover, what (L,S,R) does it see?")
    print()

    for n, ms, label, max_len in test_configs[:2]:  # just n=5
        print(f"\n--- n={n} ms={ms} [{label}] ---")
        bin_procs = [i for i in range(n) if ms[i] == 2]

        words = enumerate_mover_words(ms, n, max_len)
        # Sample first 200 valid cycles
        count = 0
        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            count += 1
            if count > 200:
                break

            ell = len(cycle)
            for bp in bin_procs:
                up_ctxs = []
                down_ctxs = []
                nonmover_ctxs = []

                for step in range(ell):
                    c = cycle[step]
                    c_next = cycle[(step+1) % ell]
                    diffs = [j for j in range(n) if c[j] != c_next[j]]
                    mover = diffs[0]
                    L = c[(bp-1) % n]
                    S = c[bp]
                    R = c[(bp+1) % n]

                    if mover == bp:
                        if S == 0:
                            up_ctxs.append((L, 0, R))
                        else:
                            down_ctxs.append((L, 1, R))
                    else:
                        nonmover_ctxs.append((L, S, R))

                nm_set = set(nonmover_ctxs)
                up_overlap = set(up_ctxs) & nm_set
                down_overlap = set(down_ctxs) & nm_set

                if count <= 5:  # Print first 5 cycles in detail
                    print(f"  cycle #{count}, P{bp}:")
                    print(f"    UP ctxs:   {sorted(set(up_ctxs))}")
                    print(f"    DOWN ctxs: {sorted(set(down_ctxs))}")
                    print(f"    NM ctxs:   {sorted(nm_set)}")
                    if up_overlap:
                        print(f"    ★ UP overlap: {up_overlap}")
                    if down_overlap:
                        print(f"    ★ DOWN overlap: {down_overlap}")

    # Part 4: Context space counting
    print(f"\n\n{'='*70}")
    print("PART 4: CONTEXT SPACE COUNTING")
    print("=" * 70)
    print()
    print("For each binary proc p with neighbors (m_L, m_R):")
    print("  Total contexts = m_L × 2 × m_R")
    print("  Mover contexts = #UP + #DOWN (exactly 2 per cycle if fires twice)")
    print("  Nonmover contexts = L × remaining steps")
    print()

    for n, ms, label, max_len in test_configs[:4]:
        print(f"\n--- n={n} ms={ms} [{label}] ---")
        bin_procs = [i for i in range(n) if ms[i] == 2]

        words = enumerate_mover_words(ms, n, max_len)
        ctx_stats = defaultdict(lambda: {'total_ctx': 0, 'mover_ctx': Counter(),
                                         'nonmover_ctx': Counter(), 'cycles': 0})

        total = 0
        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            total += 1
            ell = len(cycle)

            for bp in bin_procs:
                mL = ms[(bp-1) % n]
                mR = ms[(bp+1) % n]
                total_ctx = mL * 2 * mR

                mover_set = set()
                nonmover_set = set()
                fire_count = 0
                for step in range(ell):
                    c = cycle[step]
                    c_next = cycle[(step+1) % ell]
                    diffs = [j for j in range(n) if c[j] != c_next[j]]
                    mover = diffs[0]
                    L = c[(bp-1) % n]
                    S = c[bp]
                    R = c[(bp+1) % n]
                    if mover == bp:
                        mover_set.add((L, S, R))
                        fire_count += 1
                    else:
                        nonmover_set.add((L, S, R))

                stats = ctx_stats[bp]
                stats['total_ctx'] = total_ctx
                stats['mover_ctx'][len(mover_set)] += 1
                stats['nonmover_ctx'][len(nonmover_set)] += 1
                stats['cycles'] += 1

        for bp in sorted(ctx_stats.keys()):
            stats = ctx_stats[bp]
            mL = ms[(bp-1) % n]
            mR = ms[(bp+1) % n]
            print(f"  P{bp} (m_L={mL}, m_R={mR}): ctx_space={stats['total_ctx']}")
            print(f"    Distinct mover ctxs:    {dict(stats['mover_ctx'])}")
            print(f"    Distinct nonmover ctxs: {dict(stats['nonmover_ctx'])}")
        sys.stdout.flush()

    # Part 5: THE KEY TEST — do nonmover contexts always COVER all possible binary contexts?
    print(f"\n\n{'='*70}")
    print("PART 5: NONMOVER CONTEXT COVERAGE AT BINARY PROCS")
    print("=" * 70)
    print()
    print("If nonmover contexts at binary p cover ALL m_L × 2 × m_R contexts,")
    print("then any mover context MUST overlap → universal conflict.")
    print()

    for n, ms, label, max_len in test_configs:
        print(f"\n--- n={n} ms={ms} [{label}] ---")
        bin_procs = [i for i in range(n) if ms[i] == 2]

        words = enumerate_mover_words(ms, n, max_len)
        total = 0
        full_coverage_any = 0  # cycles where SOME binary proc has full NM coverage
        full_coverage_all = 0  # cycles where ALL binary procs have full NM coverage
        min_uncovered = Counter()  # min uncovered contexts across cycles

        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            total += 1
            ell = len(cycle)

            any_full = False
            all_full = True
            for bp in bin_procs:
                mL = ms[(bp-1) % n]
                mR = ms[(bp+1) % n]
                total_ctx = mL * 2 * mR

                nonmover_set = set()
                for step in range(ell):
                    c = cycle[step]
                    c_next = cycle[(step+1) % ell]
                    diffs = [j for j in range(n) if c[j] != c_next[j]]
                    mover = diffs[0]
                    if mover != bp:
                        L = c[(bp-1) % n]
                        S = c[bp]
                        R = c[(bp+1) % n]
                        nonmover_set.add((L, S, R))

                uncovered = total_ctx - len(nonmover_set)
                min_uncovered[uncovered] += 1
                if uncovered == 0:
                    any_full = True
                else:
                    all_full = False

            if any_full:
                full_coverage_any += 1
            if all_full:
                full_coverage_all += 1

        print(f"  Valid: {total}")
        print(f"  SOME binary proc full NM coverage: {full_coverage_any} ({100*full_coverage_any/total:.1f}%)")
        print(f"  ALL binary procs full NM coverage: {full_coverage_all} ({100*full_coverage_all/total:.1f}%)")
        print(f"  Uncovered count distribution: {dict(sorted(min_uncovered.items()))}")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
