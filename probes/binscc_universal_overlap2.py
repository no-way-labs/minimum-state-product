#!/usr/bin/env python3
"""binscc_universal_overlap2.py — Universal overlap test WITH fairness check.

Critical fix: cycles must visit ALL n processors as movers (fairness).
Without fairness, "clean" cycles are meaningless — they can't be valid good cycles.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict, Counter
import random
import time

random.seed(42)

EXOTIC_WORDS_PATH = os.path.join(
    os.path.dirname(__file__), '..', 'gpt', 'scripts',
    'glb_wrap_unknown_rotation_reps_n9.txt'
)


def load_exotic_words(path, max_words=None):
    words = []
    with open(path) as f:
        for line in f:
            s = line.strip()
            if not s:
                continue
            words.append(tuple(int(x) for x in s.split()))
            if max_words and len(words) >= max_words:
                break
    return words


def build_cycle_from_movers(ms, n, movers_word, max_reps=10):
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = list(movers_word) * max_reps
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            return cycle, full[:step+1]
        if nc in visited:
            return None, None
        visited.add(nc)
        cycle.append(nc)
    return None, None


def check_overlap(cycle, movers, n):
    mover_triples = defaultdict(set)
    nonmover_triples = defaultdict(set)
    for idx in range(len(cycle)):
        c = cycle[idx]
        mv = movers[idx]
        for p in range(n):
            triple = (c[(p-1)%n], c[p], c[(p+1)%n])
            if p == mv:
                mover_triples[p].add(triple)
            else:
                nonmover_triples[p].add(triple)
    for p in range(n):
        if mover_triples[p] & nonmover_triples[p]:
            return True
    return False


def check_overlap_details(cycle, movers, n, ms):
    """Return which processors overlap and whether they're binary."""
    mover_triples = defaultdict(set)
    nonmover_triples = defaultdict(set)
    for idx in range(len(cycle)):
        c = cycle[idx]
        mv = movers[idx]
        for p in range(n):
            triple = (c[(p-1)%n], c[p], c[(p+1)%n])
            if p == mv:
                mover_triples[p].add(triple)
            else:
                nonmover_triples[p].add(triple)

    overlap_procs = []
    for p in range(n):
        ov = mover_triples[p] & nonmover_triples[p]
        if ov:
            overlap_procs.append((p, ms[p], len(ov)))
    return overlap_procs


def is_fair(movers, n):
    """Check if all n processors appear as movers."""
    return len(set(movers)) == n


def parity_compatible(ms, movers):
    n = len(ms)
    counts = Counter(movers)
    for p in range(n):
        if ms[p] == 2 and counts.get(p, 0) % 2 != 0:
            return False
    return True


def generate_random_fair_adjacent_walk(n, length, max_attempts=100):
    """Generate a random fair ring-adjacent walk."""
    for _ in range(max_attempts):
        walk = [0]
        visited = {0}
        for _ in range(length - 1):
            pos = walk[-1]
            choices = [(pos - 1) % n, (pos + 1) % n]
            unvisited = [c for c in choices if c not in visited]
            if unvisited and len(visited) < n:
                nxt = random.choice(unvisited)
            else:
                nxt = random.choice(choices)
            walk.append(nxt)
            visited.add(nxt)
        if len(visited) == n and abs(walk[-1] - walk[0]) in [1, n-1]:
            return tuple(walk)
    return None


if __name__ == "__main__":
    n = 9

    # ================================================================
    # Part 1: ALL exotic words on key ≥3-binary architectures
    # ================================================================
    print("=" * 78)
    print("UNIVERSAL OVERLAP TEST (with fairness check)")
    print("=" * 78)

    exotic_words = load_exotic_words(EXOTIC_WORDS_PATH)  # all 19,728
    print(f"Loaded {len(exotic_words)} exotic mover words\n")

    # Family words
    bounce_word = tuple(list(range(n)) + list(range(n-2, 0, -1)) + list(range(n)))
    insertion_word = tuple([0,1,0] + list(range(1,n)) + list(range(n-2,0,-1)) + list(range(2,n)))
    top_insertion = (0,8,7,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,6,5,4,3,2,1)
    all_words = list(exotic_words) + [bounce_word, insertion_word, top_insertion]

    test_architectures = [
        # Consecutive binary
        (2, 2, 2, 3, 3, 3, 3, 3, 3),   # 3B consec
        (2, 2, 2, 2, 3, 3, 3, 3, 3),   # 4B consec
        (2, 2, 2, 2, 2, 3, 3, 3, 3),   # 5B consec
        # Spread binary
        (2, 3, 2, 3, 2, 3, 3, 3, 3),   # 3B spread
        (2, 3, 3, 2, 3, 3, 2, 3, 3),   # 3B evenly
        (2, 3, 2, 3, 2, 3, 2, 3, 3),   # 4B spread
        (3, 2, 3, 2, 3, 2, 3, 3, 3),   # 3B non-endpoint
        # Control
        (2, 3, 3, 3, 3, 3, 3, 3, 2),   # 2B (valid witness)
    ]

    for ms in test_architectures:
        nb = sum(1 for m in ms if m == 2)
        product_val = 1
        for m in ms:
            product_val *= m

        parity_fail = 0
        no_cycle = 0
        not_fair = 0
        fair_cycles = 0
        overlap_count = 0
        clean_count = 0
        clean_examples = []

        for word in all_words:
            if not parity_compatible(ms, word):
                parity_fail += 1
                continue

            cycle, movers = build_cycle_from_movers(ms, n, word)
            if cycle is None:
                no_cycle += 1
                continue

            if not is_fair(movers, n):
                not_fair += 1
                continue

            fair_cycles += 1
            if check_overlap(cycle, movers, n):
                overlap_count += 1
            else:
                clean_count += 1
                if len(clean_examples) < 3:
                    clean_examples.append((word, len(cycle)))

        pct = overlap_count / fair_cycles * 100 if fair_cycles else 0
        marker = " ***CLEAN***" if clean_count > 0 and nb >= 3 else ""
        print(f"  {ms} ({nb}B, prod={product_val}):")
        print(f"    parity_ok={len(all_words)-parity_fail}, no_cycle={no_cycle}, "
              f"not_fair={not_fair}")
        print(f"    FAIR cycles: {fair_cycles}, overlap={overlap_count} ({pct:.1f}%), "
              f"CLEAN={clean_count}{marker}")

        if clean_examples:
            for word, clen in clean_examples[:2]:
                movers_str = ','.join(str(m) for m in word[:15]) + '...'
                print(f"      Clean example: cyc_len={clen}, movers=[{movers_str}]")

    # ================================================================
    # Part 2: Random fair adjacent walks with fairness
    # ================================================================
    print(f"\n{'=' * 78}")
    print("RANDOM FAIR ADJACENT WALKS (with fairness check)")
    print("=" * 78)

    key_architectures = [
        (2, 2, 2, 3, 3, 3, 3, 3, 3),
        (2, 3, 2, 3, 2, 3, 3, 3, 3),
        (2, 3, 3, 2, 3, 3, 2, 3, 3),
        (2, 3, 3, 3, 3, 3, 3, 3, 2),
    ]

    for ms in key_architectures:
        nb = sum(1 for m in ms if m == 2)

        total_walks = 0
        parity_ok = 0
        has_cycle = 0
        fair_count = 0
        overlap_count = 0

        for length in [3*n-2, 3*n, 4*n-3]:
            for _ in range(30000):
                walk = generate_random_fair_adjacent_walk(n, length)
                if walk is None:
                    continue
                total_walks += 1

                if not parity_compatible(ms, walk):
                    continue
                parity_ok += 1

                cycle, movers = build_cycle_from_movers(ms, n, walk)
                if cycle is None:
                    continue
                has_cycle += 1

                if not is_fair(movers, n):
                    continue
                fair_count += 1

                if check_overlap(cycle, movers, n):
                    overlap_count += 1

        clean = fair_count - overlap_count
        pct = overlap_count / fair_count * 100 if fair_count else 0
        print(f"  {ms} ({nb}B): walks={total_walks}, parity={parity_ok}, "
              f"cycle={has_cycle}, fair={fair_count}, "
              f"overlap={overlap_count} ({pct:.1f}%), CLEAN={clean}")

    # ================================================================
    # Part 3: Focused context-space analysis
    # ================================================================
    print(f"\n{'=' * 78}")
    print("CONTEXT SPACE SATURATION ANALYSIS")
    print("=" * 78)
    print("For fair cycles, how full is each binary processor's context space?")

    ms = (2, 3, 2, 3, 2, 3, 3, 3, 3)  # 3B spread — 100% overlap architecture

    sample_count = 0
    proc_stats = defaultdict(lambda: {'mover': 0, 'nonmover': 0, 'total': 0,
                                       'overlap': 0, 'count': 0})

    for word in all_words[:5000]:
        if not parity_compatible(ms, word):
            continue
        cycle, movers = build_cycle_from_movers(ms, n, word)
        if cycle is None:
            continue
        if not is_fair(movers, n):
            continue

        sample_count += 1

        mover_triples = defaultdict(set)
        nonmover_triples = defaultdict(set)
        for idx in range(len(cycle)):
            c = cycle[idx]
            mv = movers[idx]
            for p in range(n):
                triple = (c[(p-1)%n], c[p], c[(p+1)%n])
                if p == mv:
                    mover_triples[p].add(triple)
                else:
                    nonmover_triples[p].add(triple)

        for p in range(n):
            m_L = ms[(p-1)%n]
            m_S = ms[p]
            m_R = ms[(p+1)%n]
            total_ctx = m_L * m_S * m_R
            ov = len(mover_triples[p] & nonmover_triples[p])

            proc_stats[p]['mover'] += len(mover_triples[p])
            proc_stats[p]['nonmover'] += len(nonmover_triples[p])
            proc_stats[p]['total'] += total_ctx
            proc_stats[p]['overlap'] += ov
            proc_stats[p]['count'] += 1

    print(f"\n  Architecture: {ms}, {sample_count} fair cycles analyzed")
    print(f"  {'Proc':>4} {'m':>2} {'ctx':>4} {'m_L':>3}×{'m_R':>3} "
          f"{'avg_mover':>10} {'avg_nonmover':>13} {'avg_overlap':>12}")
    print(f"  {'-'*60}")
    for p in range(n):
        s = proc_stats[p]
        if s['count'] == 0:
            continue
        nc = s['count']
        m_L = ms[(p-1)%n]
        m_R = ms[(p+1)%n]
        total_ctx = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]
        print(f"  P{p:>2} {ms[p]:>2} {total_ctx:>4}  {m_L:>2} × {m_R:>2}  "
              f"{s['mover']/nc:>10.1f} {s['nonmover']/nc:>13.1f} "
              f"{s['overlap']/nc:>12.2f}")

    # Also do same for 2B control
    print()
    ms2 = (2, 3, 3, 3, 3, 3, 3, 3, 2)
    proc_stats2 = defaultdict(lambda: {'mover': 0, 'nonmover': 0, 'total': 0,
                                        'overlap': 0, 'count': 0,
                                        'clean_mover': 0, 'clean_nonmover': 0})
    sample2 = 0
    clean2 = 0

    for word in all_words[:5000]:
        if not parity_compatible(ms2, word):
            continue
        cycle, movers = build_cycle_from_movers(ms2, n, word)
        if cycle is None:
            continue
        if not is_fair(movers, n):
            continue

        sample2 += 1
        is_clean = not check_overlap(cycle, movers, n)
        if is_clean:
            clean2 += 1

        mover_triples = defaultdict(set)
        nonmover_triples = defaultdict(set)
        for idx in range(len(cycle)):
            c = cycle[idx]
            mv = movers[idx]
            for p in range(n):
                triple = (c[(p-1)%n], c[p], c[(p+1)%n])
                if p == mv:
                    mover_triples[p].add(triple)
                else:
                    nonmover_triples[p].add(triple)

        for p in range(n):
            s = proc_stats2[p]
            s['mover'] += len(mover_triples[p])
            s['nonmover'] += len(nonmover_triples[p])
            s['overlap'] += len(mover_triples[p] & nonmover_triples[p])
            s['count'] += 1
            if is_clean:
                s['clean_mover'] += len(mover_triples[p])
                s['clean_nonmover'] += len(nonmover_triples[p])

    print(f"  Architecture: {ms2} (CONTROL 2B), {sample2} fair cycles, {clean2} clean")
    print(f"  {'Proc':>4} {'m':>2} {'ctx':>4} {'m_L':>3}×{'m_R':>3} "
          f"{'avg_mover':>10} {'avg_nonmover':>13} {'avg_overlap':>12}")
    print(f"  {'-'*60}")
    for p in [0, 1, 7, 8]:  # binary endpoints + their neighbors
        s = proc_stats2[p]
        if s['count'] == 0:
            continue
        nc = s['count']
        m_L = ms2[(p-1)%n]
        m_R = ms2[(p+1)%n]
        total_ctx = m_L * ms2[p] * m_R
        cnc = clean2 if clean2 > 0 else 1
        print(f"  P{p:>2} {ms2[p]:>2} {total_ctx:>4}  {m_L:>2} × {m_R:>2}  "
              f"{s['mover']/nc:>10.1f} {s['nonmover']/nc:>13.1f} "
              f"{s['overlap']/nc:>12.2f}")

    # ================================================================
    # Part 4: The key question — does EVERY fair cycle on ≥3B overlap?
    # ================================================================
    print(f"\n{'=' * 78}")
    print("DEFINITIVE TEST: All 19,731 words on key architectures")
    print("=" * 78)

    key_3b = [
        (2, 2, 2, 3, 3, 3, 3, 3, 3),
        (3, 2, 2, 2, 3, 3, 3, 3, 3),
        (3, 3, 2, 2, 2, 3, 3, 3, 3),
        (3, 2, 3, 2, 3, 2, 3, 3, 3),
        (2, 3, 2, 3, 2, 3, 3, 3, 3),
        (2, 3, 3, 2, 3, 3, 2, 3, 3),
        (3, 2, 3, 3, 2, 3, 3, 2, 3),
        (3, 3, 2, 3, 3, 2, 3, 3, 2),
    ]

    for ms in key_3b:
        nb = sum(1 for m in ms if m == 2)
        bin_pos = [i for i, m in enumerate(ms) if m == 2]

        fair_cycles = 0
        overlap_count = 0
        clean_list = []

        for word in all_words:
            if not parity_compatible(ms, word):
                continue
            cycle, movers = build_cycle_from_movers(ms, n, word)
            if cycle is None:
                continue
            if not is_fair(movers, n):
                continue

            fair_cycles += 1
            if check_overlap(cycle, movers, n):
                overlap_count += 1
            else:
                clean_list.append(word)

        clean = len(clean_list)
        pct = overlap_count / fair_cycles * 100 if fair_cycles else 0
        marker = " ***COUNTEREXAMPLE***" if clean > 0 else ""
        print(f"  {ms} bin_at={bin_pos}: fair={fair_cycles}, "
              f"overlap={overlap_count} ({pct:.1f}%), CLEAN={clean}{marker}")

        if clean_list:
            # Analyze the clean cases
            for word in clean_list[:2]:
                cycle, movers = build_cycle_from_movers(ms, n, word)
                mover_counts = Counter(movers)
                print(f"    Clean word (cyc={len(cycle)}): "
                      f"mover_counts={dict(sorted(mover_counts.items()))}")
                # Check overlap details
                ov = check_overlap_details(cycle, movers, n, ms)
                print(f"    No overlap at any processor")

    print(f"\n{'=' * 78}")
    print("DONE")
    print("=" * 78)
