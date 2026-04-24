#!/usr/bin/env python3
"""
RA7: Comprehensive investigation of the UEC scope gap.

Tasks:
1. Verify RA6's counterexample independently
2. Map exact scope of UEC across gap patterns
3. Identify what makes gap-(3,3,3) special
4. Determine correct UEC scope
5. Investigate alternative obstructions for gap-(3,3,3)
6. Enumerate all gap patterns at n=9..12
"""

import random
import sys
from collections import defaultdict
from itertools import product as iproduct
from math import prod

random.seed(42)

# =========================================================================
# Core utilities
# =========================================================================

def build_cycle_inc(word, ms, n):
    """Build good cycle with incrementing transition from all-zero start."""
    L = len(word)
    configs = [[0]*n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + 1) % ms[p]
        configs.append(c)
    if configs[-1] != configs[0]:
        return None
    if len(set(tuple(c) for c in configs[:L])) != L:
        return None
    return [tuple(c) for c in configs[:L]]


def build_cycle_trans(word, ms, n, trans):
    """Build good cycle with specified transition functions.
    trans[p] is a dict: (L,S,R) -> new_S, or a function."""
    L = len(word)
    configs = [[0]*n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
        if callable(trans[p]):
            new_val = trans[p](*ctx)
        else:
            new_val = trans[p][ctx]
        c[p] = new_val
        configs.append(c)
    if configs[-1] != configs[0]:
        return None
    if len(set(tuple(c) for c in configs[:L])) != L:
        return None
    return [tuple(c) for c in configs[:L]]


def check_ec(good, word, n):
    """Check entry conflict at each proc. Returns dict: proc -> set of overlapping triples."""
    L = len(word)
    mover_triples = defaultdict(set)
    nonmover_triples = defaultdict(set)
    for t in range(L):
        c = good[t]
        mover = word[t]
        for j in range(n):
            triple = (c[(j-1)%n], c[j], c[(j+1)%n])
            if j == mover:
                mover_triples[j].add(triple)
            else:
                nonmover_triples[j].add(triple)
    conflicts = {}
    for j in range(n):
        overlap = mover_triples[j] & nonmover_triples[j]
        if overlap:
            conflicts[j] = overlap
    return conflicts


def is_ring_adjacent(word, n):
    """Check all consecutive movers (including wrap) are ring-adjacent."""
    L = len(word)
    for i in range(L):
        diff = abs(word[i] - word[(i+1)%L])
        if diff != 1 and diff != n-1:
            return False
    return True


def is_hfull(word, ms, n):
    """Check if every proc fires a multiple of its modulus (hfull)."""
    from collections import Counter
    fc = Counter(word)
    for p in range(n):
        if fc.get(p, 0) == 0 or fc[p] % ms[p] != 0:
            return False
    return True


def generate_random_words(ms, n, count=5000, max_attempts=50000):
    """Generate random ring-adjacent hfull mover words."""
    results = []
    for _ in range(max_attempts):
        if len(results) >= count:
            break
        target_fc = list(ms)
        total_fires = sum(target_fc)
        fc = [0]*n
        start = random.randint(0, n-1)
        word = [start]
        fc[start] = 1
        ok = True
        for step in range(total_fires - 1):
            last = word[-1]
            neighbors = [(last+1)%n, (last-1)%n]
            random.shuffle(neighbors)
            scores = []
            for nxt in neighbors:
                need = max(0, target_fc[nxt] - fc[nxt])
                scores.append((need, nxt))
            scores.sort(reverse=True)
            if scores[0][0] > 0:
                nxt = scores[0][1]
            elif scores[1][0] > 0:
                nxt = scores[1][1]
            else:
                nxt = random.choice(neighbors)
            word.append(nxt)
            fc[nxt] += 1

        if not all(fc[p] >= target_fc[p] and fc[p] % ms[p] == 0 for p in range(n)):
            continue
        if abs(word[-1] - word[0]) % n not in (1, n-1):
            continue
        cycle = build_cycle_inc(word, ms, n)
        if cycle is None:
            continue
        results.append((word, cycle))
    return results


def gap_pattern_ms(n, binary_positions):
    """Build ms vector: 2 at binary positions, 3 elsewhere."""
    ms = [3]*n
    for p in binary_positions:
        ms[p] = 2
    return ms


def gaps_from_positions(positions, n):
    """Compute gap sizes between binary positions on ring of size n."""
    positions = sorted(positions)
    k = len(positions)
    gaps = []
    for i in range(k):
        gap = (positions[(i+1)%k] - positions[i]) % n
        gaps.append(gap)
    return tuple(sorted(gaps))


def all_gap_patterns(n, num_binary=3):
    """All distinct gap patterns for num_binary binary procs on ring of size n.
    Returns dict: gap_tuple -> example binary positions."""
    seen = {}
    from itertools import combinations
    for combo in combinations(range(n), num_binary):
        # Check non-adjacent
        combo_list = list(combo)
        adjacent = False
        for i in range(num_binary):
            if (combo_list[(i+1)%num_binary] - combo_list[i]) % n == 1:
                adjacent = True
                break
        if adjacent:
            continue
        gaps = gaps_from_positions(combo_list, n)
        if gaps not in seen:
            seen[gaps] = list(combo)
    return seen


# =========================================================================
# TASK 1: Verify RA6's counterexample
# =========================================================================

def task1():
    print("=" * 70)
    print("TASK 1: Verify RA6's counterexample")
    print("=" * 70)

    n = 9
    ms = [2, 3, 3, 2, 3, 3, 2, 3, 3]
    word = [8, 7, 8, 7, 6, 5, 4, 5, 4, 3, 2, 1, 2, 1, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0]
    product = prod(ms)
    threshold = 4 * 3**(n-2)

    print(f"ms = {ms}")
    print(f"Product = {product}")
    print(f"Threshold = {threshold}")
    print(f"Sub-threshold: {product < threshold}")
    print(f"Word length = {len(word)}")
    print(f"Word = {word}")

    # Check ring-adjacent
    print(f"Ring-adjacent: {is_ring_adjacent(word, n)}")

    # Check hfull
    print(f"Hfull: {is_hfull(word, ms, n)}")

    # Build cycle with incrementing transition
    cycle = build_cycle_inc(word, ms, n)
    if cycle is None:
        print("FAILED: Cannot build valid cycle with incrementing transition!")
        # Try to figure out why
        L = len(word)
        configs = [[0]*n]
        for t in range(L):
            c = list(configs[-1])
            p = word[t]
            c[p] = (c[p] + 1) % ms[p]
            configs.append(c)
        print(f"  Start: {configs[0]}")
        print(f"  End:   {configs[-1]}")
        print(f"  Closes: {configs[-1] == configs[0]}")
        unique = len(set(tuple(c) for c in configs[:L]))
        print(f"  Distinct configs: {unique} / {L}")
        return False

    print(f"Cycle length: {len(cycle)}")
    print(f"All configs distinct: {len(set(cycle)) == len(cycle)}")

    # Check EC
    conflicts = check_ec(cycle, word, n)
    print(f"\nEntry conflicts: {len(conflicts)} procs with EC")
    if conflicts:
        for p, triples in conflicts.items():
            print(f"  Proc {p}: {len(triples)} overlapping triples")
        print("COUNTEREXAMPLE IS WRONG: has entry conflict!")
        return False
    else:
        print("CONFIRMED: Zero entry conflict at ALL processors")

    # Now try ALL transition modes (inc and dec for ternary)
    # For binary (m=2): only one non-identity transition: 0->1, 1->0 (both inc and dec)
    # For ternary (m=3): inc = 0->1->2->0, dec = 0->2->1->0
    print("\n--- Testing all 2^6 = 64 transition combos (ternary inc/dec) ---")
    ternary_procs = [p for p in range(n) if ms[p] == 3]
    num_ternary = len(ternary_procs)
    cf_count = 0
    ec_count = 0

    for mask in range(2**num_ternary):
        trans = {}
        for p in range(n):
            if ms[p] == 2:
                trans[p] = lambda L, S, R: 1 - S
            else:
                idx = ternary_procs.index(p)
                if mask & (1 << idx):
                    trans[p] = lambda L, S, R: (S + 2) % 3  # dec
                else:
                    trans[p] = lambda L, S, R: (S + 1) % 3  # inc

        cyc = build_cycle_trans(word, ms, n, trans)
        if cyc is None:
            continue
        conflicts = check_ec(cyc, word, n)
        if not conflicts:
            cf_count += 1
        else:
            ec_count += 1

    print(f"Valid cycles: {cf_count + ec_count}")
    print(f"  Conflict-free: {cf_count}")
    print(f"  With EC: {ec_count}")

    # Check firing count details
    from collections import Counter
    fc = Counter(word)
    print(f"\nFiring counts:")
    for p in range(n):
        print(f"  Proc {p} (m={ms[p]}): fires {fc[p]} times, fc/m = {fc[p]//ms[p]}")

    print("\nTASK 1 RESULT: Counterexample CONFIRMED" if cf_count > 0 else "TASK 1 RESULT: Counterexample INVALID")
    return cf_count > 0


# =========================================================================
# TASK 2: Map exact scope of UEC
# =========================================================================

def task2():
    print("\n" + "=" * 70)
    print("TASK 2: Map exact scope of UEC across gap patterns")
    print("=" * 70)

    results = {}

    for n in [9, 10, 11, 12]:
        print(f"\n--- n = {n} ---")
        gap_patterns = all_gap_patterns(n, 3)
        print(f"  Gap patterns: {sorted(gap_patterns.keys())}")

        for gaps, positions in sorted(gap_patterns.items()):
            ms = gap_pattern_ms(n, positions)
            product = prod(ms)
            threshold = 4 * 3**(n-2)

            if product >= threshold:
                print(f"  Gap {gaps}: product {product} >= threshold {threshold}, SKIP")
                continue

            # Generate random cycles
            cycles = generate_random_words(ms, n, count=2000, max_attempts=30000)

            if not cycles:
                print(f"  Gap {gaps}: 0 cycles found (ms={ms})")
                continue

            total = len(cycles)
            ec_cycles = 0
            cf_cycles = 0
            for word, cycle in cycles:
                conflicts = check_ec(cycle, word, n)
                if conflicts:
                    ec_cycles += 1
                else:
                    cf_cycles += 1

            ec_rate = ec_cycles / total * 100
            print(f"  Gap {gaps}: {total} cycles, EC={ec_cycles} ({ec_rate:.1f}%), "
                  f"CF={cf_cycles} ({100-ec_rate:.1f}%), positions={positions}")
            results[(n, gaps)] = {
                'total': total, 'ec': ec_cycles, 'cf': cf_cycles,
                'positions': positions, 'ms': ms
            }

    print("\n--- SUMMARY ---")
    print(f"{'n':>3s} {'Gap pattern':>20s} {'Total':>6s} {'EC%':>7s} {'CF':>6s}")
    for (n, gaps), r in sorted(results.items()):
        ec_pct = r['ec'] / r['total'] * 100 if r['total'] > 0 else 0
        marker = " *** GAP ***" if r['cf'] > 0 else ""
        print(f"{n:3d} {str(gaps):>20s} {r['total']:6d} {ec_pct:6.1f}% {r['cf']:6d}{marker}")

    return results


# =========================================================================
# TASK 3: What makes gap-(3,3,3) special
# =========================================================================

def task3():
    print("\n" + "=" * 70)
    print("TASK 3: Identify what makes gap-(3,3,3) special")
    print("=" * 70)

    n = 9
    ms = [2, 3, 3, 2, 3, 3, 2, 3, 3]
    word_cf = [8, 7, 8, 7, 6, 5, 4, 5, 4, 3, 2, 1, 2, 1, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0]
    cycle_cf = build_cycle_inc(word_cf, ms, n)

    from collections import Counter

    # (a) Check bounce pattern
    print("\n(a) Bounce pattern analysis:")
    fc = Counter(word_cf)
    binary_pos = [p for p in range(n) if ms[p] == 2]
    ternary_pos = [p for p in range(n) if ms[p] == 3]
    print(f"  Binary positions: {binary_pos}")
    print(f"  Ternary positions: {ternary_pos}")
    print(f"  Firing counts: {dict(sorted(fc.items()))}")

    # Analyze mover movement pattern
    print(f"\n  Mover word: {word_cf}")
    # Look for bounces: consecutive pairs like [...a, b, a, b...]
    bounces = 0
    for i in range(len(word_cf) - 3):
        if (word_cf[i] == word_cf[i+2] and word_cf[i+1] == word_cf[i+3]
                and word_cf[i] != word_cf[i+1]):
            bounces += 1
    print(f"  Bounce patterns (a,b,a,b): {bounces}")

    # Look for oscillations: a,b,a
    oscillations = []
    for i in range(len(word_cf) - 2):
        if word_cf[i] == word_cf[i+2] and word_cf[i] != word_cf[i+1]:
            oscillations.append((i, word_cf[i], word_cf[i+1]))
    print(f"  Oscillations (a,b,a): {len(oscillations)}")
    for i, a, b in oscillations:
        print(f"    Step {i}: {a} -> {b} -> {a}")

    # (b) Binary proc firing counts
    print(f"\n(b) Binary firing counts:")
    for p in binary_pos:
        print(f"  Proc {p}: fires {fc[p]} times (fc/m = {fc[p]//ms[p]})")

    # (c) Sandwiched ternary analysis
    print(f"\n(c) Sandwiched ternary analysis:")
    for p in ternary_pos:
        left_type = "binary" if ms[(p-1)%n] == 2 else "ternary"
        right_type = "binary" if ms[(p+1)%n] == 2 else "ternary"
        sandwiched = (ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2)
        print(f"  Proc {p}: left={left_type}, right={right_type}, sandwiched={sandwiched}")

    # (d) Segment structure
    print(f"\n(d) Ternary segment structure:")
    segments = []
    seg = []
    for p in range(n):
        if ms[p] == 3:
            seg.append(p)
        else:
            if seg:
                segments.append(seg)
            seg = []
    if seg:
        # Handle wrap-around
        if segments and ms[0] == 3:
            segments[0] = seg + segments[0]
        else:
            segments.append(seg)
    print(f"  Ternary segments: {segments}")
    for s in segments:
        print(f"    Segment {s}: length {len(s)}")

    # (e) Movement through segments
    print(f"\n(e) Movement pattern through ternary segments:")
    for seg in segments:
        seg_moves = [(i, word_cf[i]) for i in range(len(word_cf)) if word_cf[i] in seg]
        print(f"  Segment {seg}: {len(seg_moves)} firings")
        movers_in_seg = [m for _, m in seg_moves]
        print(f"    Mover sequence: {movers_in_seg}")

    # (f) Triple analysis at each proc
    print(f"\n(f) Triple diversity analysis:")
    mover_triples = defaultdict(set)
    nonmover_triples = defaultdict(set)
    for t in range(len(word_cf)):
        c = cycle_cf[t]
        mover = word_cf[t]
        for j in range(n):
            triple = (c[(j-1)%n], c[j], c[(j+1)%n])
            if j == mover:
                mover_triples[j].add(triple)
            else:
                nonmover_triples[j].add(triple)

    for j in range(n):
        mt = mover_triples[j]
        nmt = nonmover_triples[j]
        total_possible = ms[(j-1)%n] * ms[j] * ms[(j+1)%n]
        print(f"  Proc {j} (m={ms[j]}): mover={len(mt)}, nonmover={len(nmt)}, "
              f"overlap={len(mt&nmt)}, possible={total_possible}, "
              f"used={len(mt|nmt)}/{total_possible}")


# =========================================================================
# TASK 5: Alternative obstructions for gap-(3,3,3)
# =========================================================================

def check_shadow(good, word, n, ms):
    """Check if a shadow cycle exists for this good cycle.
    A shadow cycle is a second set of L distinct configs from the same config space
    that forms a valid cycle with the same mover word, using the same transition,
    and is disjoint from the original."""
    # For shadow cycle: we need to find another starting config that produces
    # a valid distinct disjoint cycle with the same word
    L = len(word)
    # Try all starting configs
    total = prod(ms)
    shadow_found = False

    # Build transition from the good cycle
    # At each step t, mover word[t] changes. The transition is determined.
    # For incrementing: new_val = (old_val + 1) % m
    # A shadow cycle would start from a different config and follow the same word

    for start in iproduct(*(range(m) for m in ms)):
        if list(start) == [0]*n:
            continue
        start_list = list(start)
        configs = [start_list]
        valid = True
        for t in range(L):
            c = list(configs[-1])
            p = word[t]
            c[p] = (c[p] + 1) % ms[p]
            configs.append(c)
        if configs[-1] != configs[0]:
            continue
        cycle_set = set(tuple(c) for c in configs[:L])
        if len(cycle_set) != L:
            continue
        # Check disjoint
        orig_set = set(good)
        if cycle_set & orig_set:
            continue
        shadow_found = True
        break

    return shadow_found


def check_mnu(good, word, n):
    """Check MNU (mover-nonmover uniqueness) for the cycle.
    MNU: for every mover step, the post-move config as seen by the mover is unique
    among all nonmover appearances of that proc with the same context."""
    L = len(word)
    # MNU says: if proc p fires at step t, producing config c',
    # then the triple (c'[p-1], c'[p], c'[p+1]) at p should not appear
    # as a nonmover triple at p in any other step.

    nonmover_triples_by_proc = defaultdict(set)
    for t in range(L):
        c = good[t]
        mover = word[t]
        for j in range(n):
            if j != mover:
                triple = (c[(j-1)%n], c[j], c[(j+1)%n])
                nonmover_triples_by_proc[j].add(triple)

    # Check post-move triples
    mnu_violations = 0
    for t in range(L):
        c = good[t]
        cn = good[(t+1)%L]
        mover = word[t]
        post_triple = (cn[(mover-1)%n], cn[mover], cn[(mover+1)%n])
        if post_triple in nonmover_triples_by_proc[mover]:
            mnu_violations += 1

    return mnu_violations


def task5():
    print("\n" + "=" * 70)
    print("TASK 5: Alternative obstructions for gap-(3,3,3)")
    print("=" * 70)

    n = 9
    ms = [2, 3, 3, 2, 3, 3, 2, 3, 3]
    word_cf = [8, 7, 8, 7, 6, 5, 4, 5, 4, 3, 2, 1, 2, 1, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0]
    cycle_cf = build_cycle_inc(word_cf, ms, n)

    # (a) Shadow cycle check
    print("\n(a) Shadow cycle check:")
    has_shadow = check_shadow(cycle_cf, word_cf, n, ms)
    print(f"  Shadow cycle exists: {has_shadow}")

    # (b) MNU check
    print("\n(b) MNU check:")
    mnu_violations = check_mnu(cycle_cf, word_cf, n)
    print(f"  MNU violations: {mnu_violations}")

    # (c) Check a broader set of CF cycles for shadow/MNU
    print("\n(c) Checking many CF cycles for shadow/MNU:")
    cycles = generate_random_words(ms, n, count=500, max_attempts=20000)
    cf_cycles = []
    for word, cycle in cycles:
        conflicts = check_ec(cycle, word, n)
        if not conflicts:
            cf_cycles.append((word, cycle))

    print(f"  Found {len(cf_cycles)} CF cycles out of {len(cycles)} total")

    shadow_count = 0
    mnu_fail_count = 0
    for i, (word, cycle) in enumerate(cf_cycles[:50]):  # limit for speed
        has_shadow = check_shadow(cycle, word, n, ms)
        mnu_v = check_mnu(cycle, word, n)
        if has_shadow:
            shadow_count += 1
        if mnu_v > 0:
            mnu_fail_count += 1

    checked = min(50, len(cf_cycles))
    print(f"  Checked {checked} CF cycles:")
    print(f"    Shadow cycle exists: {shadow_count}/{checked}")
    print(f"    MNU violations > 0:  {mnu_fail_count}/{checked}")

    # (d) Can we build a COMPLETE self-stabilizing system?
    print("\n(d) System completeness check for the CF cycle:")
    mover_triples = defaultdict(dict)  # proc -> {triple: new_val}
    nonmover_triples = defaultdict(set)
    for t in range(len(word_cf)):
        c = cycle_cf[t]
        cn = cycle_cf[(t+1) % len(word_cf)]
        mover = word_cf[t]
        for j in range(n):
            triple = (c[(j-1)%n], c[j], c[(j+1)%n])
            if j == mover:
                mover_triples[j][triple] = cn[j]
            else:
                nonmover_triples[j].add(triple)

    print(f"  Transition table coverage:")
    for j in range(n):
        total_possible = ms[(j-1)%n] * ms[j] * ms[(j+1)%n]
        covered_mover = len(mover_triples[j])
        covered_nonmover = len(nonmover_triples[j])
        covered_total = len(set(mover_triples[j].keys()) | nonmover_triples[j])
        uncovered = total_possible - covered_total
        print(f"    Proc {j} (m={ms[j]}): {covered_total}/{total_possible} covered "
              f"(mover={covered_mover}, nonmover={covered_nonmover}, uncovered={uncovered})")


# =========================================================================
# TASK 6: Enumerate all gap patterns and check
# =========================================================================

def task6():
    print("\n" + "=" * 70)
    print("TASK 6: All gap patterns at n=9..12")
    print("=" * 70)

    for n in [9, 10, 11, 12]:
        print(f"\n--- n = {n} ---")
        gap_patterns = all_gap_patterns(n, 3)
        threshold = 4 * 3**(n-2)
        for gaps, positions in sorted(gap_patterns.items()):
            ms = gap_pattern_ms(n, positions)
            product = prod(ms)
            sub = product < threshold
            has_sandwiched = any(
                ms[p] == 3 and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2
                for p in range(n)
            )
            min_gap = min(gaps)
            print(f"  Gap {gaps}: positions={positions}, product={product}, "
                  f"sub-thresh={sub}, has_sandwiched={has_sandwiched}, min_gap={min_gap}")


# =========================================================================
# MAIN
# =========================================================================

if __name__ == "__main__":
    ok = task1()
    if not ok:
        print("\nCOUNTEREXAMPLE INVALID - stopping.")
        sys.exit(1)

    task2_results = task2()
    task3()
    task5()
    task6()

    # TASK 4: Synthesize scope
    print("\n" + "=" * 70)
    print("TASK 4: Correct UEC scope synthesis")
    print("=" * 70)

    # Analyze task 2 results
    all_cf_gaps = []
    all_ec_gaps = []
    for (n, gaps), r in sorted(task2_results.items()):
        if r['cf'] > 0:
            all_cf_gaps.append((n, gaps))
        else:
            all_ec_gaps.append((n, gaps))

    print(f"\nGap patterns with CF cycles (UEC FAILS):")
    for n, gaps in all_cf_gaps:
        print(f"  n={n}: gaps={gaps}")

    print(f"\nGap patterns with 100% EC (UEC HOLDS):")
    for n, gaps in all_ec_gaps:
        print(f"  n={n}: gaps={gaps}")

    # Check: is the pattern "has sandwiched ternary"?
    print(f"\nHypothesis check: 'UEC holds iff there exists a sandwiched ternary'")
    for (n, gaps), r in sorted(task2_results.items()):
        positions = r['positions']
        ms = r['ms']
        has_sandwiched = any(
            ms[p] == 3 and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2
            for p in range(n)
        )
        ec_holds = (r['cf'] == 0)
        consistent = (has_sandwiched == ec_holds)
        print(f"  n={n}, gaps={gaps}: sandwiched={has_sandwiched}, "
              f"EC holds={ec_holds}, consistent={consistent}")
