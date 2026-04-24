#!/usr/bin/env python3
"""binscc_universal_overlap.py — Test whether overlap is universal for ALL
mover patterns (not just bounce) on ≥3-binary architectures.

Uses GLB's 19,728 exotic mover words + random adjacent walks.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
import random
import time

random.seed(42)

EXOTIC_WORDS_PATH = os.path.join(
    os.path.dirname(__file__), '..', 'gpt', 'scripts',
    'glb_wrap_unknown_rotation_reps_n9.txt'
)


def load_exotic_words(path, max_words=None):
    """Load mover words from GLB's file."""
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
    """Build a good cycle by repeating the mover word until config returns to start."""
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
            return None, None  # hit a non-start repeat → won't close
        visited.add(nc)
        cycle.append(nc)
    return None, None


def check_overlap(cycle, movers, n):
    """Check if any processor sees same (L,S,R) as both mover and nonmover."""
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
    overlapping_procs = []
    for p in range(n):
        ov = mover_triples[p] & nonmover_triples[p]
        if ov:
            overlapping_procs.append(p)
    return overlapping_procs


def check_overlap_binary_only(cycle, movers, n, ms):
    """Check overlap only at binary processors."""
    mover_triples = defaultdict(set)
    nonmover_triples = defaultdict(set)
    for idx in range(len(cycle)):
        c = cycle[idx]
        mv = movers[idx]
        for p in range(n):
            if ms[p] != 2:
                continue
            triple = (c[(p-1)%n], c[p], c[(p+1)%n])
            if p == mv:
                mover_triples[p].add(triple)
            else:
                nonmover_triples[p].add(triple)
    for p in range(n):
        if ms[p] == 2 and mover_triples[p] & nonmover_triples[p]:
            return True
    return False


def generate_random_adjacent_walk(n, length):
    """Generate a random fair ring-adjacent walk of given length starting at 0."""
    walk = [0]
    visited = {0}
    for _ in range(length - 1):
        pos = walk[-1]
        choices = [(pos - 1) % n, (pos + 1) % n]
        # Prefer unvisited positions
        unvisited = [c for c in choices if c not in visited]
        if unvisited and len(visited) < n:
            nxt = random.choice(unvisited)
        else:
            nxt = random.choice(choices)
        walk.append(nxt)
        visited.add(nxt)
    # Check fairness
    if len(visited) < n:
        return None
    # Check adjacency closure (last -> first must be adjacent)
    if abs(walk[-1] - walk[0]) not in [1, n-1]:
        return None
    return tuple(walk)


def parity_compatible(ms, movers):
    """Check binary parity: each binary processor must fire an even number of times."""
    n = len(ms)
    counts = defaultdict(int)
    for m in movers:
        counts[m] += 1
    for p in range(n):
        if ms[p] == 2 and counts[p] % 2 != 0:
            return False
    return True


if __name__ == "__main__":
    n = 9

    # Test architectures (≥3 binary)
    test_architectures = [
        (2, 2, 2, 3, 3, 3, 3, 3, 3),   # 3B (3+6)
        (2, 3, 2, 3, 2, 3, 3, 3, 3),   # 3B spread
        (2, 3, 3, 2, 3, 3, 2, 3, 3),   # 3B evenly spread
        (2, 2, 2, 2, 3, 3, 3, 3, 3),   # 4B
        (2, 3, 2, 3, 2, 3, 2, 3, 3),   # 4B spread
        (2, 2, 2, 2, 2, 3, 3, 3, 3),   # 5B
        (2, 2, 2, 2, 2, 2, 3, 3, 3),   # 6B
    ]

    # Control: 2-binary (should NOT overlap universally)
    control_architectures = [
        (2, 3, 3, 3, 3, 3, 3, 3, 2),   # 2B endpoints (valid witness)
        (3, 2, 3, 3, 3, 3, 3, 2, 3),   # 2B spread
    ]

    # ================================================================
    # Part 1: Test GLB's exotic words on ≥3-binary architectures
    # ================================================================
    print("=" * 78)
    print("UNIVERSAL OVERLAP TEST: Exotic mover words on ≥3-binary architectures")
    print("=" * 78)

    exotic_words = load_exotic_words(EXOTIC_WORDS_PATH, max_words=2000)
    print(f"Loaded {len(exotic_words)} exotic mover words")

    # Also add known family words
    bounce_word = tuple(list(range(n)) + list(range(n-2, 0, -1)) + list(range(n)))
    insertion_word = tuple([0,1,0] + list(range(1,n)) + list(range(n-2,0,-1)) + list(range(2,n)))
    # top insertion (GLB's discovery)
    top_insertion = (0,8,7,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,6,5,4,3,2,1)

    family_words = [bounce_word, insertion_word, top_insertion]

    for ms in test_architectures + control_architectures:
        nb = sum(1 for m in ms if m == 2)
        product_val = 1
        for m in ms:
            product_val *= m

        total_tested = 0
        total_with_cycle = 0
        overlap_count = 0
        overlap_at_binary = 0
        overlap_at_nonbinary = 0
        parity_fail = 0

        # Test exotic words
        for word in exotic_words:
            if not parity_compatible(ms, word):
                parity_fail += 1
                continue

            total_tested += 1
            cycle, movers = build_cycle_from_movers(ms, n, word)
            if cycle is None:
                continue

            total_with_cycle += 1
            overlap_procs = check_overlap(cycle, movers, n)

            if overlap_procs:
                overlap_count += 1
                has_binary_overlap = any(ms[p] == 2 for p in overlap_procs)
                has_nonbinary_overlap = any(ms[p] != 2 for p in overlap_procs)
                if has_binary_overlap:
                    overlap_at_binary += 1
                if has_nonbinary_overlap:
                    overlap_at_nonbinary += 1

        # Test family words
        for word in family_words:
            if not parity_compatible(ms, word):
                continue
            total_tested += 1
            cycle, movers = build_cycle_from_movers(ms, n, word)
            if cycle is None:
                continue
            total_with_cycle += 1
            overlap_procs = check_overlap(cycle, movers, n)
            if overlap_procs:
                overlap_count += 1

        clean = total_with_cycle - overlap_count
        pct = overlap_count / total_with_cycle * 100 if total_with_cycle else 0
        tag = "≥3B" if nb >= 3 else "2B"

        marker = " ***" if clean > 0 and nb >= 3 else ""
        print(f"  {ms} ({nb}B {tag}): tested={total_tested}, parity_fail={parity_fail}, "
              f"cycles={total_with_cycle}, overlap={overlap_count} ({pct:.1f}%), "
              f"CLEAN={clean}{marker}")
        if overlap_at_binary > 0 or overlap_at_nonbinary > 0:
            print(f"    overlap at binary={overlap_at_binary}, "
                  f"at nonbinary={overlap_at_nonbinary}")

    # ================================================================
    # Part 2: Generate random adjacent walks and test overlap
    # ================================================================
    print(f"\n{'=' * 78}")
    print("RANDOM ADJACENT WALKS: overlap test")
    print("=" * 78)

    for ms in test_architectures[:3] + control_architectures[:1]:
        nb = sum(1 for m in ms if m == 2)

        total_gen = 0
        total_fair = 0
        total_parity = 0
        total_with_cycle = 0
        overlap_count = 0

        for _ in range(50000):
            total_gen += 1
            walk = generate_random_adjacent_walk(n, 3*n - 2)
            if walk is None:
                continue
            total_fair += 1
            if not parity_compatible(ms, walk):
                continue
            total_parity += 1

            cycle, movers = build_cycle_from_movers(ms, n, walk)
            if cycle is None:
                continue
            total_with_cycle += 1

            overlap_procs = check_overlap(cycle, movers, n)
            if overlap_procs:
                overlap_count += 1

        clean = total_with_cycle - overlap_count
        pct = overlap_count / total_with_cycle * 100 if total_with_cycle else 0
        print(f"  {ms} ({nb}B): gen={total_gen}, fair={total_fair}, "
              f"parity={total_parity}, cycles={total_with_cycle}, "
              f"overlap={overlap_count} ({pct:.1f}%), CLEAN={clean}")

    # ================================================================
    # Part 3: Longer cycles — try different cycle lengths
    # ================================================================
    print(f"\n{'=' * 78}")
    print("CYCLE LENGTH VARIATION: test lengths 2n+1 to 5n")
    print("=" * 78)

    ms_test = (2, 2, 2, 3, 3, 3, 3, 3, 3)

    for target_len in [2*n+1, 3*n-2, 3*n, 4*n-3, 4*n, 5*n]:
        total_gen = 0
        total_fair = 0
        total_parity = 0
        total_with_cycle = 0
        overlap_count = 0

        for _ in range(50000):
            total_gen += 1
            walk = generate_random_adjacent_walk(n, target_len)
            if walk is None:
                continue
            total_fair += 1
            if not parity_compatible(ms_test, walk):
                continue
            total_parity += 1

            cycle, movers = build_cycle_from_movers(ms_test, n, walk)
            if cycle is None:
                continue
            total_with_cycle += 1

            overlap_procs = check_overlap(cycle, movers, n)
            if overlap_procs:
                overlap_count += 1

        clean = total_with_cycle - overlap_count
        pct = overlap_count / total_with_cycle * 100 if total_with_cycle else 0
        print(f"  len={target_len}: gen={total_gen}, fair={total_fair}, "
              f"parity={total_parity}, cycles={total_with_cycle}, "
              f"overlap={overlap_count} ({pct:.1f}%), CLEAN={clean}")

    # ================================================================
    # Part 4: Context analysis — WHY does overlap happen?
    # ================================================================
    print(f"\n{'=' * 78}")
    print("CONTEXT ANALYSIS: Why overlap is forced at binary processors")
    print("=" * 78)

    # For each binary processor p in a cycle, count:
    # - Number of distinct mover contexts
    # - Number of distinct nonmover contexts
    # - Total context space size
    # - Overlap fraction

    ms = (2, 2, 2, 3, 3, 3, 3, 3, 3)

    # Use a variety of exotic words that produce cycles
    sample_words = exotic_words[:500]
    context_stats = defaultdict(lambda: {'mover_ctx': 0, 'nonmover_ctx': 0,
                                          'total_ctx': 0, 'overlaps': 0, 'cycles': 0})

    for word in sample_words:
        if not parity_compatible(ms, word):
            continue
        cycle, movers = build_cycle_from_movers(ms, n, word)
        if cycle is None:
            continue

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
            m_L = ms[(p-1) % n]
            m_S = ms[p]
            m_R = ms[(p+1) % n]
            total = m_L * m_S * m_R
            ov = mover_triples[p] & nonmover_triples[p]

            stats = context_stats[(p, ms[p])]
            stats['cycles'] += 1
            stats['mover_ctx'] += len(mover_triples[p])
            stats['nonmover_ctx'] += len(nonmover_triples[p])
            stats['total_ctx'] += total
            stats['overlaps'] += len(ov)

    print(f"\n  Architecture: {ms}")
    print(f"  {'Proc':>4} {'m':>2} {'Avg mover ctx':>14} {'Avg nonmover ctx':>17} "
          f"{'Total ctx':>10} {'Avg overlaps':>13} {'Overlap rate':>12}")
    print(f"  {'-'*75}")

    for (p, mp), stats in sorted(context_stats.items()):
        if stats['cycles'] == 0:
            continue
        nc = stats['cycles']
        avg_m = stats['mover_ctx'] / nc
        avg_nm = stats['nonmover_ctx'] / nc
        avg_tc = stats['total_ctx'] / nc
        avg_ov = stats['overlaps'] / nc
        ov_rate = stats['overlaps'] / max(1, stats['mover_ctx']) * 100
        bstr = "BIN" if mp == 2 else "TER"
        print(f"  P{p:>2} ({bstr}) {avg_m:>14.1f} {avg_nm:>17.1f} "
              f"{avg_tc:>10.0f} {avg_ov:>13.2f} {ov_rate:>11.1f}%")

    # ================================================================
    # Part 5: Pigeonhole analysis — counting argument
    # ================================================================
    print(f"\n{'=' * 78}")
    print("PIGEONHOLE ANALYSIS")
    print("=" * 78)

    print(f"\n  For binary processor p (m_p = 2) with neighbors m_L, m_R:")
    print(f"  Total context space = m_L × 2 × m_R")
    print(f"  In cycle of length L, p is mover at k steps, nonmover at L-k steps.")
    print(f"  Mover contexts: up to k distinct (from k visits)")
    print(f"  Nonmover contexts: up to L-k distinct (from L-k visits)")
    print(f"  If k + (L-k) = L > m_L × 2 × m_R, pigeonhole forces overlap.")
    print(f"  But mover and nonmover share the same space, so overlap needs:")
    print(f"  mover_set ∩ nonmover_set ≠ ∅")
    print()

    # Actually compute: for each architecture, what's the min context space
    # at binary processors and what's the cycle length?
    for ms in test_architectures + control_architectures:
        nb = sum(1 for m in ms if m == 2)
        bin_positions = [p for p in range(n) if ms[p] == 2]
        min_ctx = float('inf')
        for p in bin_positions:
            m_L = ms[(p-1)%n]
            m_R = ms[(p+1)%n]
            ctx = m_L * 2 * m_R
            min_ctx = min(min_ctx, ctx)

        # A fair cycle of length L visits each processor at least twice (parity).
        # With n=9 and L=25 (3n-2), each processor fires ≈ 2.8 times.
        # Nonmover visits: L - fires ≈ 22.
        # Total visits to ANY context = L = 25.
        # With min_ctx contexts, by pigeonhole at least ceil(L/min_ctx) visits
        # share a context. If a mover and nonmover share, that's overlap.

        # More refined: mover contexts are at most k (2-3). Nonmover: L-k (22-23).
        # If nonmover uses ALL min_ctx contexts, then mover has no "free" context.
        # But nonmover visits are only min_ctx = 8..18 possible, and 22 visits,
        # so nonmover uses at most min(22, min_ctx) = min_ctx distinct contexts.
        # If nonmover covers all min_ctx contexts, then ANY mover context overlaps.

        print(f"  {ms} ({nb}B): binary at {bin_positions}, min_ctx_space={min_ctx}")

    # For the key case: 3 binary with ternary neighbors
    print(f"\n  Key case: binary p with ternary neighbors (m_L=3, m_R=3)")
    print(f"  Context space: 3 × 2 × 3 = 18")
    print(f"  In cycle of length 25: p fires 2-3 times, nonmover 22-23 times")
    print(f"  Nonmover can see at most 18 distinct contexts")
    print(f"  Mover sees 2-3 contexts")
    print(f"  Question: can those 2-3 mover contexts avoid the 18 nonmover contexts?")
    print(f"  If nonmover covers ALL 18, NO — overlap is forced.")
    print(f"  If nonmover covers only 16/18, mover has 2 safe contexts — just enough!")
    print()
    print(f"  Key case: binary p with binary neighbor (m_L=2, m_R=3 or m_L=2, m_R=2)")
    print(f"  Context space: 2 × 2 × 3 = 12 or 2 × 2 × 2 = 8")
    print(f"  With 8 total contexts and 22+ nonmover visits → nonmover covers all 8")
    print(f"  → OVERLAP FORCED at binary processors with binary neighbors!")
    print(f"  This is WHY ≥3 consecutive binaries always overlap.")

    print(f"\n{'=' * 78}")
    print("DONE")
    print("=" * 78)
