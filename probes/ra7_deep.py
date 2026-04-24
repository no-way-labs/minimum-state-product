#!/usr/bin/env python3
"""
RA7 Deep: Focused investigation on:
1. Better cycle generation for hard-to-find patterns (n=10,11,12)
2. Precise characterization of when CF cycles exist
3. Shadow+MNU analysis of all CF cycles
4. The gap-(3,3,3) bounce structure
"""

import random
import sys
from collections import defaultdict, Counter
from itertools import product as iproduct, combinations
from math import prod

random.seed(123)

# =========================================================================
# Core utilities (from ra7_investigation.py)
# =========================================================================

def build_cycle_inc(word, ms, n):
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

def check_ec(good, word, n):
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

def check_shadow(good, word, n, ms):
    L = len(word)
    orig_set = set(good)
    for start in iproduct(*(range(m) for m in ms)):
        start_list = list(start)
        configs = [start_list]
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
        if cycle_set & orig_set:
            continue
        return True
    return False

def check_mnu(good, word, n):
    L = len(word)
    nonmover_triples_by_proc = defaultdict(set)
    for t in range(L):
        c = good[t]
        mover = word[t]
        for j in range(n):
            if j != mover:
                triple = (c[(j-1)%n], c[j], c[(j+1)%n])
                nonmover_triples_by_proc[j].add(triple)
    violations = 0
    for t in range(L):
        cn = good[(t+1)%L]
        mover = word[t]
        post_triple = (cn[(mover-1)%n], cn[mover], cn[(mover+1)%n])
        if post_triple in nonmover_triples_by_proc[mover]:
            violations += 1
    return violations

def gap_pattern_ms(n, binary_positions):
    ms = [3]*n
    for p in binary_positions:
        ms[p] = 2
    return ms

def gaps_from_positions(positions, n):
    positions = sorted(positions)
    k = len(positions)
    gaps = []
    for i in range(k):
        gap = (positions[(i+1)%k] - positions[i]) % n
        gaps.append(gap)
    return tuple(sorted(gaps))

def all_gap_patterns(n, num_binary=3):
    seen = {}
    for combo in combinations(range(n), num_binary):
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
# Improved cycle generator - multiple strategies
# =========================================================================

def generate_cycles_aggressive(ms, n, count=2000, max_attempts=200000):
    """More aggressive cycle generation with multiple strategies."""
    results = []
    seen_words = set()
    target_fc = list(ms)
    total_fires = sum(target_fc)

    for attempt in range(max_attempts):
        if len(results) >= count:
            break

        fc = [0]*n
        # Strategy 1: random start, biased walk
        # Strategy 2: sweep patterns
        # Strategy 3: bounce patterns
        strategy = random.choice([1, 1, 1, 2, 3])

        if strategy == 1:
            start = random.randint(0, n-1)
            word = [start]
            fc[start] = 1
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

        elif strategy == 2:
            # Sweep: go CW then CCW
            word = []
            fc = [0]*n
            pos = random.randint(0, n-1)
            direction = random.choice([1, -1])
            for step in range(total_fires):
                word.append(pos)
                fc[pos] += 1
                # Decide: continue or reverse
                if random.random() < 0.15:
                    direction = -direction
                next_pos = (pos + direction) % n
                pos = next_pos

        elif strategy == 3:
            # Bounce within segments
            word = []
            fc = [0]*n
            pos = random.randint(0, n-1)
            for step in range(total_fires):
                word.append(pos)
                fc[pos] += 1
                neighbors = [(pos+1)%n, (pos-1)%n]
                # Prefer neighbor that needs more fires
                needs = [(max(0, target_fc[nb] - fc[nb]), nb) for nb in neighbors]
                needs.sort(reverse=True)
                if needs[0][0] > 0:
                    pos = needs[0][1]
                else:
                    pos = random.choice(neighbors)

        if not all(fc[p] >= target_fc[p] and fc[p] % ms[p] == 0 for p in range(n)):
            continue
        if abs(word[-1] - word[0]) % n not in (1, n-1):
            continue

        word_key = tuple(word)
        if word_key in seen_words:
            continue

        cycle = build_cycle_inc(word, ms, n)
        if cycle is None:
            continue
        seen_words.add(word_key)
        results.append((word, cycle))

    return results


# =========================================================================
# PART A: Deep gap pattern scan with aggressive generation
# =========================================================================

def part_a():
    print("=" * 70)
    print("PART A: Deep gap pattern scan (aggressive generation)")
    print("=" * 70)

    results = {}
    for n in [9, 10, 11, 12]:
        print(f"\n--- n = {n} ---")
        gap_patterns = all_gap_patterns(n, 3)
        threshold = 4 * 3**(n-2)

        for gaps, positions in sorted(gap_patterns.items()):
            ms = gap_pattern_ms(n, positions)
            product = prod(ms)
            if product >= threshold:
                continue

            has_sandwiched = any(
                ms[p] == 3 and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2
                for p in range(n)
            )

            cycles = generate_cycles_aggressive(ms, n, count=3000, max_attempts=100000)
            total = len(cycles)
            ec = sum(1 for w, c in cycles if check_ec(c, w, n))
            cf = total - ec

            print(f"  Gap {gaps}: {total} cycles, EC={ec}, CF={cf}, "
                  f"sandwiched={has_sandwiched}")
            results[(n, gaps)] = {'total': total, 'ec': ec, 'cf': cf,
                                  'sandwiched': has_sandwiched, 'positions': positions,
                                  'ms': ms}

    return results


# =========================================================================
# PART B: What structural property distinguishes CF from EC cycles at gap-(3,3,3)?
# =========================================================================

def part_b():
    print("\n" + "=" * 70)
    print("PART B: CF vs EC cycle structure at gap-(3,3,3)")
    print("=" * 70)

    n = 9
    ms = [2, 3, 3, 2, 3, 3, 2, 3, 3]
    binary_pos = [0, 3, 6]

    cycles = generate_cycles_aggressive(ms, n, count=3000, max_attempts=100000)
    cf_cycles = [(w, c) for w, c in cycles if not check_ec(c, w, n)]
    ec_cycles = [(w, c) for w, c in cycles if check_ec(c, w, n)]

    print(f"Total cycles: {len(cycles)}")
    print(f"CF: {len(cf_cycles)}, EC: {len(ec_cycles)}")

    def analyze_word(word, label):
        fc = Counter(word)
        L = len(word)

        # Count oscillations (a,b,a patterns)
        oscillations = sum(1 for i in range(L-2) if word[i] == word[i+2] and word[i] != word[i+1])

        # Count direction changes
        dir_changes = 0
        for i in range(1, L):
            d1 = (word[i] - word[i-1]) % n
            if i < L-1:
                d2 = (word[(i+1)] - word[i]) % n
                if d1 != d2:
                    dir_changes += 1

        # Binary firing pattern
        binary_fc = tuple(fc[p] for p in binary_pos)

        # Max consecutive same-direction
        max_run = 1
        run = 1
        for i in range(2, L):
            d1 = (word[i] - word[i-1]) % n
            d2 = (word[i-1] - word[i-2]) % n
            if d1 == d2:
                run += 1
                max_run = max(max_run, run)
            else:
                run = 1

        return {
            'length': L,
            'oscillations': oscillations,
            'dir_changes': dir_changes,
            'binary_fc': binary_fc,
            'max_run': max_run,
        }

    print("\n--- CF cycle statistics ---")
    cf_stats = [analyze_word(w, 'CF') for w, c in cf_cycles[:500]]
    print(f"  Lengths: {Counter(s['length'] for s in cf_stats).most_common(5)}")
    print(f"  Oscillations: min={min(s['oscillations'] for s in cf_stats)}, "
          f"max={max(s['oscillations'] for s in cf_stats)}, "
          f"mean={sum(s['oscillations'] for s in cf_stats)/len(cf_stats):.1f}")
    print(f"  Dir changes: min={min(s['dir_changes'] for s in cf_stats)}, "
          f"max={max(s['dir_changes'] for s in cf_stats)}, "
          f"mean={sum(s['dir_changes'] for s in cf_stats)/len(cf_stats):.1f}")
    print(f"  Binary fc: {Counter(s['binary_fc'] for s in cf_stats).most_common(5)}")
    print(f"  Max run: {Counter(s['max_run'] for s in cf_stats).most_common(5)}")

    print("\n--- EC cycle statistics ---")
    ec_stats = [analyze_word(w, 'EC') for w, c in ec_cycles[:500]]
    if ec_stats:
        print(f"  Lengths: {Counter(s['length'] for s in ec_stats).most_common(5)}")
        print(f"  Oscillations: min={min(s['oscillations'] for s in ec_stats)}, "
              f"max={max(s['oscillations'] for s in ec_stats)}, "
              f"mean={sum(s['oscillations'] for s in ec_stats)/len(ec_stats):.1f}")
        print(f"  Dir changes: min={min(s['dir_changes'] for s in ec_stats)}, "
              f"max={max(s['dir_changes'] for s in ec_stats)}, "
              f"mean={sum(s['dir_changes'] for s in ec_stats)/len(ec_stats):.1f}")
        print(f"  Binary fc: {Counter(s['binary_fc'] for s in ec_stats).most_common(5)}")
        print(f"  Max run: {Counter(s['max_run'] for s in ec_stats).most_common(5)}")

    # Check: do ALL CF cycles have shadow + MNU violations?
    print("\n--- Shadow + MNU check on CF cycles ---")
    n_check = min(30, len(cf_cycles))
    shadow_count = 0
    mnu_count = 0
    for w, c in cf_cycles[:n_check]:
        if check_shadow(c, w, n, ms):
            shadow_count += 1
        if check_mnu(c, w, n) > 0:
            mnu_count += 1
    print(f"  Of {n_check} CF cycles:")
    print(f"    Shadow exists: {shadow_count}/{n_check}")
    print(f"    MNU violated:  {mnu_count}/{n_check}")

    # Also check EC cycles for shadow + MNU
    print("\n--- Shadow + MNU check on EC cycles ---")
    n_check_ec = min(30, len(ec_cycles))
    shadow_ec = sum(1 for w, c in ec_cycles[:n_check_ec] if check_shadow(c, w, n, ms))
    mnu_ec = sum(1 for w, c in ec_cycles[:n_check_ec] if check_mnu(c, w, n) > 0)
    print(f"  Of {n_check_ec} EC cycles:")
    print(f"    Shadow exists: {shadow_ec}/{n_check_ec}")
    print(f"    MNU violated:  {mnu_ec}/{n_check_ec}")


# =========================================================================
# PART C: Can a system be completed? (key question)
# =========================================================================

def part_c():
    print("\n" + "=" * 70)
    print("PART C: System completion attempt for gap-(3,3,3) CF cycle")
    print("=" * 70)

    n = 9
    ms = [2, 3, 3, 2, 3, 3, 2, 3, 3]
    word = [8, 7, 8, 7, 6, 5, 4, 5, 4, 3, 2, 1, 2, 1, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0]
    cycle = build_cycle_inc(word, ms, n)
    L = len(word)

    # Build partial transition function from the cycle
    trans = {}  # (proc, L, S, R) -> new_val
    for t in range(L):
        c = cycle[t]
        cn = cycle[(t+1)%L]
        mover = word[t]
        for j in range(n):
            ctx = (c[(j-1)%n], c[j], c[(j+1)%n])
            if j == mover:
                trans[(j, *ctx)] = cn[j]
            else:
                # Nonmover: must map to same value
                if (j, *ctx) in trans:
                    assert trans[(j, *ctx)] == c[j], f"Conflict at proc {j}, ctx {ctx}"
                trans[(j, *ctx)] = c[j]

    # Check: how many uncovered contexts exist?
    total_configs = prod(ms)
    good_set = set(cycle)
    bad_configs = [c for c in iproduct(*(range(m) for m in ms)) if c not in good_set]

    print(f"Total configs: {total_configs}")
    print(f"Good configs: {len(good_set)}")
    print(f"Bad configs: {len(bad_configs)}")

    # For each bad config, which procs are privileged?
    # A proc j is privileged iff trans[(j, L, S, R)] != S
    # For uncovered contexts, we choose the transition.
    # For covered mover contexts: trans[...] != S (by construction)
    # For covered nonmover contexts: trans[...] = S (by construction)

    # Count how many bad-config transitions are uncovered (free to choose)
    covered_contexts_per_proc = defaultdict(set)
    for (j, l, s, r), val in trans.items():
        covered_contexts_per_proc[j].add((l, s, r))

    uncovered_per_proc = {}
    for j in range(n):
        total = ms[(j-1)%n] * ms[j] * ms[(j+1)%n]
        covered = len(covered_contexts_per_proc[j])
        uncovered_per_proc[j] = total - covered
        print(f"  Proc {j}: {covered}/{total} covered, {uncovered_per_proc[j]} free")

    # The question: can we set the free transitions so that:
    # 1. Every bad config has at least one privileged proc (liveness)
    # 2. No bad config cycle exists (convergence)

    # Count bad configs where ALL procs have covered nonmover contexts
    # (meaning all procs are forced to be non-privileged -> dead config!)
    dead_count = 0
    forced_priv_count = 0
    free_count = 0
    for bc in bad_configs:
        all_covered_nonmover = True
        has_free = False
        has_forced_priv = False
        for j in range(n):
            ctx = (bc[(j-1)%n], bc[j], bc[(j+1)%n])
            if (j, *ctx) in trans:
                if trans[(j, *ctx)] != bc[j]:
                    has_forced_priv = True
            else:
                has_free = True
                all_covered_nonmover = False

        if all_covered_nonmover and not has_forced_priv:
            dead_count += 1
        elif has_forced_priv:
            forced_priv_count += 1
        elif has_free:
            free_count += 1

    print(f"\nBad config analysis:")
    print(f"  Dead (all forced non-privileged): {dead_count}")
    print(f"  Forced privileged (at least one mover context): {forced_priv_count}")
    print(f"  Free (at least one uncovered context): {free_count}")

    if dead_count > 0:
        print(f"\n  *** {dead_count} DEAD CONFIGS: system CANNOT be completed! ***")
        print(f"  These configs have no privileged processor regardless of free choices.")
        # Show a few
        shown = 0
        for bc in bad_configs:
            if shown >= 3:
                break
            all_nonmover = True
            has_forced_priv = False
            for j in range(n):
                ctx = (bc[(j-1)%n], bc[j], bc[(j+1)%n])
                if (j, *ctx) in trans:
                    if trans[(j, *ctx)] != bc[j]:
                        has_forced_priv = True
                        break
                else:
                    all_nonmover = False
            if all_nonmover and not has_forced_priv:
                print(f"    Dead config: {bc}")
                shown += 1
    else:
        print(f"\n  No dead configs from cycle constraints alone.")
        print(f"  System completion is not immediately blocked by liveness.")
        print(f"  Convergence must be checked separately.")


# =========================================================================
# PART D: Check all non-sandwiched patterns more carefully
# =========================================================================

def part_d():
    print("\n" + "=" * 70)
    print("PART D: Non-sandwiched pattern analysis at n=10..12")
    print("=" * 70)

    # The key question: at n=10, gap-(3,3,4) has no sandwiched ternary.
    # At n=11, gap-(3,3,5) and gap-(3,4,4) have no sandwiched.
    # At n=12, gap-(3,3,6), gap-(3,4,5), gap-(4,4,4) have no sandwiched.
    # Do any of these admit CF cycles?

    for n, gaps_to_check in [(10, [(3,3,4)]),
                              (11, [(3,3,5), (3,4,4)]),
                              (12, [(3,3,6), (3,4,5), (4,4,4)])]:
        print(f"\n--- n = {n} ---")
        gap_patterns = all_gap_patterns(n, 3)

        for target_gaps in gaps_to_check:
            if target_gaps not in gap_patterns:
                print(f"  Gap {target_gaps}: not found")
                continue
            positions = gap_patterns[target_gaps]
            ms = gap_pattern_ms(n, positions)
            product = prod(ms)
            threshold = 4 * 3**(n-2)

            print(f"  Gap {target_gaps}: ms={ms}, product={product}, thresh={threshold}")

            # Very aggressive search
            cycles = generate_cycles_aggressive(ms, n, count=5000, max_attempts=500000)
            total = len(cycles)
            cf = sum(1 for w, c in cycles if not check_ec(c, w, n))

            print(f"    Cycles found: {total}, CF: {cf}")

            if cf > 0:
                # Show a CF example
                for w, c in cycles:
                    if not check_ec(c, w, n):
                        print(f"    CF word: {w}")
                        print(f"    Length: {len(w)}")
                        break


# =========================================================================
# PART E: Minimum gap for CF - is it ONLY equal gaps?
# =========================================================================

def part_e():
    print("\n" + "=" * 70)
    print("PART E: Is gap-(k,k,k) the only CF pattern?")
    print("=" * 70)

    # At n=9, only gap-(3,3,3) is non-sandwiched.
    # At n=12, gap-(4,4,4) is available. Does it have CF cycles?
    # Also: does the CF property depend on ALL gaps being equal, or just all >= 3?

    # Let's check n=12 gap-(4,4,4) more aggressively
    n = 12
    positions = [0, 4, 8]
    ms = gap_pattern_ms(n, positions)
    print(f"n={n}, gap=(4,4,4), ms={ms}, product={prod(ms)}, thresh={4*3**(n-2)}")

    cycles = generate_cycles_aggressive(ms, n, count=5000, max_attempts=500000)
    total = len(cycles)
    cf = sum(1 for w, c in cycles if not check_ec(c, w, n))
    print(f"  Cycles: {total}, CF: {cf}")

    # n=12 gap-(3,3,6): 3 gaps, min gap 3 but not all equal
    positions = [0, 3, 6]
    ms = gap_pattern_ms(n, positions)
    print(f"\nn={n}, gap=(3,3,6), ms={ms}, product={prod(ms)}, thresh={4*3**(n-2)}")
    cycles = generate_cycles_aggressive(ms, n, count=5000, max_attempts=500000)
    total = len(cycles)
    cf = sum(1 for w, c in cycles if not check_ec(c, w, n))
    print(f"  Cycles: {total}, CF: {cf}")

    # n=15 gap-(5,5,5): bigger equal gaps
    n = 15
    positions = [0, 5, 10]
    ms = gap_pattern_ms(n, positions)
    print(f"\nn={n}, gap=(5,5,5), ms={ms}, product={prod(ms)}, thresh={4*3**(n-2)}")
    cycles = generate_cycles_aggressive(ms, n, count=3000, max_attempts=300000)
    total = len(cycles)
    cf = sum(1 for w, c in cycles if not check_ec(c, w, n))
    print(f"  Cycles: {total}, CF: {cf}")


if __name__ == "__main__":
    results_a = part_a()
    part_b()
    part_c()
    part_d()
    part_e()

    # Final summary
    print("\n" + "=" * 70)
    print("FINAL SUMMARY")
    print("=" * 70)

    print("\nGap patterns where CF cycles were found:")
    for (n, gaps), r in sorted(results_a.items()):
        if r['cf'] > 0:
            print(f"  n={n}, gaps={gaps}: {r['cf']}/{r['total']} CF, "
                  f"sandwiched={r['sandwiched']}")

    print("\nGap patterns where ALL cycles have EC:")
    for (n, gaps), r in sorted(results_a.items()):
        if r['cf'] == 0 and r['total'] > 0:
            print(f"  n={n}, gaps={gaps}: {r['total']} all EC, "
                  f"sandwiched={r['sandwiched']}")

    print("\nGap patterns with 0 cycles found:")
    for (n, gaps), r in sorted(results_a.items()):
        if r['total'] == 0:
            print(f"  n={n}, gaps={gaps}: no cycles found, sandwiched={r['sandwiched']}")
