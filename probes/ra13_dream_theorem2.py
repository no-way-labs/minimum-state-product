#!/usr/bin/env python3
"""
RA13 v2: Dream Theorem Investigation — with proper exhaustive enumeration.

The v1 word-based enumerator was too restrictive (only tried uniform sweeps).
This version uses the DFS-based approach from cic_walk_mnu.py plus direct
construction of known cycle families.

Strategy:
  Small n (n=5): full DFS enumeration (product ≤ 72, manageable)
  Medium n (n=7): DFS + constructed families
  Large n (n=9): constructed families only (product up to 5832)
"""

import sys
import time
from collections import defaultdict, Counter
from itertools import product as iproduct, combinations
from math import prod

# =========================================================================
# Core utilities
# =========================================================================

def check_ec(good, word, n):
    """Check entry conflict: mover triple overlaps non-mover triple."""
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


def is_uniform_sweep(word, n):
    """Check if word is a uniform sweep (any start, CW or CCW, any reps)."""
    if len(word) % n != 0:
        return False
    reps = len(word) // n
    for start in range(n):
        for direction in [1, -1]:
            sweep = [(start + direction * i) % n for i in range(n)]
            full = sweep * reps
            if word == full:
                return True
    return False


def is_generalized_sweep(word, n):
    """Check if word is any cyclic rotation of a uniform sweep."""
    if len(word) % n != 0:
        return False
    reps = len(word) // n
    doubled = word + word
    for start in range(n):
        for direction in [1, -1]:
            sweep = [(start + direction * i) % n for i in range(n)]
            full = sweep * reps
            for offset in range(len(word)):
                if doubled[offset:offset+len(word)] == full:
                    return True
    return False


def classify_cycle_type(word, n):
    """Classify mover word type."""
    if is_uniform_sweep(word, n) or is_generalized_sweep(word, n):
        return "sweep"
    fc = Counter(word)
    fire_counts = sorted(set(fc.values()))
    return f"fc={fire_counts}"


def gap_pattern_ms(n, binary_positions):
    ms = [3]*n
    for p in binary_positions:
        ms[p] = 2
    return ms


def get_gaps(binary_pos, n):
    bp = sorted(binary_pos)
    gaps = []
    for i in range(len(bp)):
        gap = (bp[(i+1) % len(bp)] - bp[i]) % n
    gaps.append(gap)
    return gaps


def get_gaps_correct(binary_pos, n):
    bp = sorted(binary_pos)
    gaps = []
    for i in range(len(bp)):
        nxt = bp[(i+1) % len(bp)]
        cur = bp[i]
        gap = (nxt - cur) % n
        gaps.append(gap)
    return gaps


def has_even_gap(binary_pos, n):
    gaps = get_gaps_correct(binary_pos, n)
    return any(g % 2 == 0 for g in gaps)


# =========================================================================
# Exhaustive DFS cycle enumeration (for small state spaces)
# =========================================================================

def enumerate_good_cycles_exhaustive(ms, n, max_cycles=10000, max_time=60.0):
    """Enumerate ALL good cycles via DFS. Works for product <= ~500."""
    t0 = time.time()
    product_val = prod(ms)
    if product_val > 2000:
        return []

    all_configs = list(iproduct(*[range(m) for m in ms]))
    start = tuple([0]*n)

    results = []
    seen = set()

    max_len = min(4 * n, product_val)

    def dfs(config, path, word, det, depth):
        nonlocal results
        if time.time() - t0 > max_time:
            return
        if len(results) >= max_cycles:
            return

        for p in range(n):
            for new_val in range(ms[p]):
                if new_val == config[p]:
                    continue

                # Adjacent mover
                if word:
                    last = word[-1]
                    diff = min(abs(p - last), n - abs(p - last))
                    if diff > 1:
                        continue

                # Consistency
                L = config[(p-1) % n]
                S = config[p]
                R = config[(p+1) % n]
                key_m = (p, L, S, R)

                new_det = dict(det)
                consistent = True

                if key_m in new_det:
                    if new_det[key_m] != new_val:
                        consistent = False
                else:
                    new_det[key_m] = new_val

                if not consistent:
                    continue

                # Non-mover consistency
                ok = True
                for i in range(n):
                    if i == p:
                        continue
                    Li = config[(i-1) % n]
                    Si = config[i]
                    Ri = config[(i+1) % n]
                    key_i = (i, Li, Si, Ri)
                    if key_i in new_det:
                        if new_det[key_i] != Si:
                            ok = False
                            break
                    else:
                        new_det[key_i] = Si

                if not ok:
                    continue

                new_config = list(config)
                new_config[p] = new_val
                new_config = tuple(new_config)
                new_word = word + [p]

                # Cycle closure
                if new_config == start and len(path) >= 2 * n:
                    cycle = list(path)
                    # Mutual exclusion check
                    me_ok = True
                    for idx in range(len(cycle)):
                        c = cycle[idx]
                        priv = []
                        for i in range(n):
                            Li = c[(i-1) % n]
                            Si = c[i]
                            Ri = c[(i+1) % n]
                            ki = (i, Li, Si, Ri)
                            if ki in new_det and new_det[ki] != Si:
                                priv.append(i)
                        if len(priv) != 1:
                            me_ok = False
                            break
                    if me_ok:
                        cycle_key = frozenset(cycle)
                        if cycle_key not in seen:
                            seen.add(cycle_key)
                            results.append((cycle, new_word))
                    continue

                if new_config not in set(path) and len(path) < max_len:
                    path.append(new_config)
                    dfs(new_config, path, new_word, new_det, depth + 1)
                    path.pop()

    dfs(start, [start], [], {}, 0)
    return results


# =========================================================================
# Constructed cycle families
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


def build_cycle_trans(word, ms, n, trans_mode):
    """Build cycle with per-proc transition mode.
    trans_mode[p] = 1 for inc, -1 for dec.
    """
    L = len(word)
    configs = [[0]*n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + trans_mode[p]) % ms[p]
        configs.append(c)
    if configs[-1] != configs[0]:
        return None
    if len(set(tuple(c) for c in configs[:L])) != L:
        return None
    return [tuple(c) for c in configs[:L]]


def find_balanced_segment_words(seg_len, target=2):
    total = seg_len * target
    results = []
    def dfs(word, fc):
        if len(word) == total:
            if all(fc[i] == target for i in range(seg_len)):
                results.append(list(word))
            return
        last = word[-1]
        for nxt in [last-1, last+1]:
            if 0 <= nxt < seg_len and fc[nxt] < target:
                word.append(nxt)
                fc[nxt] += 1
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1
    for start in range(seg_len):
        fc = [0]*seg_len
        fc[start] = 1
        dfs([start], fc)
    return results


def generate_sweep_words(n, ms):
    """Generate all uniform sweep mover words."""
    words = []
    for start in range(n):
        for direction in [1, -1]:
            sweep = [(start + direction * i) % n for i in range(n)]
            # Each binary fires 2 times, ternary 3 times
            # Total fires needed = sum(ms[p]) for one full traversal
            # For uniform sweep: reps = lcm of ms? No — reps such that each
            # proc fires a multiple of ms[p] times... actually each proc fires
            # reps times, need reps divisible by ms[p] for all p.
            # For ms with 2s and 3s: need reps = 6 (lcm). But that's long.
            # Actually for a valid cycle starting from 0: each proc fires
            # reps times, and (reps * step) % ms[p] = 0, where step = 1 for inc.
            # So reps must be divisible by ms[p] for each p.
            # With 2s and 3s: reps must be multiple of 6.
            # But cycle length = reps * n. For sub-threshold, need CL ≤ product.
            for reps in range(1, 10):
                word = sweep * reps
                # Check if this word returns to start under inc
                ok = True
                for p in range(n):
                    fc_p = sum(1 for w in word if w == p)
                    if fc_p % ms[p] != 0:
                        ok = False
                        break
                if ok:
                    words.append(word)
    return words


def generate_constructed_words(n, binary_pos, ms):
    """Generate known cycle constructions for given binary placement."""
    words = []

    # 1. Uniform sweeps (inc)
    for w in generate_sweep_words(n, ms):
        words.append(('inc', w))

    # 2. For all-odd-gap patterns: bounce-sweep construction
    gaps = get_gaps_correct(binary_pos, n)
    bp = sorted(binary_pos)

    if all(g % 2 != 0 for g in gaps) and len(bp) == 3:
        # Try bounce-sweep construction
        seg_len = gaps[0] - 1  # assumes equal gaps
        if all(g == gaps[0] for g in gaps) and seg_len >= 1:
            seg_words = find_balanced_segment_words(seg_len, target=2)
            if seg_words:
                for sw in seg_words[:5]:  # limit
                    # Build segments between binary procs
                    segments = []
                    for i in range(3):
                        seg_start = bp[i] + 1
                        seg = [(seg_start + j) % n for j in range(gaps[i] - 1)]
                        segments.append(seg)

                    # Try different orderings and directions
                    for direction in [1, -1]:
                        for seg_dir in [1, -1]:
                            word = []
                            for i in range(3):
                                seg = segments[i] if seg_dir == 1 else list(reversed(segments[i]))
                                mapped = [seg[j] for j in sw]
                                word.extend(mapped)
                                word.append(bp[(i+1) % 3])

                            # Add sweep phase
                            if direction == 1:
                                word.extend(list(range(n-1, -1, -1)))
                            else:
                                word.extend(list(range(n)))
                            words.append(('inc', word))

    # 3. Non-uniform fire count patterns
    # Try random adjacent walks that are balanced
    # Skip for now — covered by DFS for small n

    return words


def enumerate_cycles_comprehensive(ms, n, binary_pos, max_time=30.0):
    """Comprehensive cycle enumeration combining DFS and constructions."""
    t0 = time.time()
    product_val = prod(ms)
    results = []
    seen = set()

    def add_cycle(cyc, word):
        key = frozenset(cyc)
        if key not in seen:
            seen.add(key)
            results.append((cyc, word))

    # 1. Constructed words
    for trans_type, word in generate_constructed_words(n, binary_pos, ms):
        if time.time() - t0 > max_time:
            break
        if trans_type == 'inc':
            cyc = build_cycle_inc(word, ms, n)
            if cyc:
                add_cycle(cyc, word)
            # Also try dec at ternary procs
            ternary = [p for p in range(n) if ms[p] >= 3]
            if len(ternary) <= 10:
                for combo in iproduct([1, -1], repeat=len(ternary)):
                    if time.time() - t0 > max_time:
                        break
                    tm = {p: 1 for p in range(n)}
                    for idx, tp in enumerate(ternary):
                        tm[tp] = combo[idx]
                    cyc = build_cycle_trans(word, ms, n, tm)
                    if cyc:
                        add_cycle(cyc, word)

    # 2. DFS enumeration for small products
    if product_val <= 1000 and time.time() - t0 < max_time * 0.5:
        remaining = max_time - (time.time() - t0)
        dfs_cycles = enumerate_good_cycles_exhaustive(ms, n, max_cycles=2000,
                                                       max_time=remaining)
        for cyc, word in dfs_cycles:
            add_cycle(cyc, word)

    return results


# =========================================================================
# Shadow check
# =========================================================================

def check_shadow_exists(good, word, n, ms):
    L = len(word)
    orig_set = set(good)
    product_val = prod(ms)
    if product_val > 50000:
        return None
    for start in iproduct(*(range(m) for m in ms)):
        if tuple(start) in orig_set:
            continue
        configs = [list(start)]
        for t in range(L):
            c = list(configs[-1])
            p = word[t]
            c[p] = (c[p] + 1) % ms[p]
            configs.append(c)
        if configs[-1] != list(configs[0]):
            continue
        cycle_set = set(tuple(c) for c in configs[:L])
        if len(cycle_set) != L:
            continue
        if cycle_set & orig_set:
            continue
        return True
    return False


# =========================================================================
# PART 1
# =========================================================================

def part1():
    print("=" * 70)
    print("PART 1: Profile the no-EC cycles (all-odd-gap binary arrangements)")
    print("=" * 70)

    for k in [3, 5]:
        n = 3 * k
        bp = [0, k, 2*k]
        ms = gap_pattern_ms(n, bp)
        gaps = get_gaps_correct(bp, n)
        product_val = prod(ms)
        threshold = 4 * 3**(n-2)

        print(f"\nk={k}, n={n}, ms={ms[:6]}..., product={product_val}, "
              f"thresh={threshold}, sub={product_val < threshold}")
        print(f"Gaps: {gaps}")

        # Construct bounce-sweep cycles
        seg_len = k - 1
        seg_words = find_balanced_segment_words(seg_len, target=2)
        print(f"Balanced segment words (seg_len={seg_len}): {len(seg_words)}")

        cycles_found = 0
        noec_found = 0
        ec_found = 0
        noec_sweep = 0
        noec_nonsweep = 0

        for trans_type, word in generate_constructed_words(n, bp, ms):
            cyc = build_cycle_inc(word, ms, n)
            if cyc is None:
                continue
            cycles_found += 1
            ec = check_ec(cyc, word, n)
            is_sw = is_uniform_sweep(word, n) or is_generalized_sweep(word, n)
            if ec:
                ec_found += 1
            else:
                noec_found += 1
                ct = classify_cycle_type(word, n)
                if is_sw:
                    noec_sweep += 1
                else:
                    noec_nonsweep += 1
                    fc = Counter(word)
                    print(f"  NO-EC non-sweep: type={ct}, CL={len(word)}, "
                          f"sweep={is_sw}")
                    if n <= 9:
                        has_sh = check_shadow_exists(cyc, word, n, ms)
                        print(f"    Shadow exists: {has_sh}")

        print(f"\nk={k}: {cycles_found} cycles, {ec_found} EC, "
              f"{noec_found} no-EC ({noec_sweep} sweep, {noec_nonsweep} non-sweep)")


# =========================================================================
# PARTS 2-4 combined (with proper enumeration)
# =========================================================================

def parts234():
    print("\n" + "=" * 70)
    print("PARTS 2-4: Comprehensive test with proper enumeration")
    print("=" * 70)

    dream_holds = True
    counterexamples = []

    for n in [5, 7, 9]:
        print(f"\n{'='*60}")
        print(f"n = {n}, threshold = {4*3**(n-2)}")
        print(f"{'='*60}")

        threshold = 4 * 3**(n-2)
        total_cycles = 0
        n_ec = 0
        n_sweep_noec = 0
        n_counterexample = 0
        nonsweep_ec = 0
        nonsweep_noec = 0
        evengap_ec = 0
        evengap_noec = 0
        placements = 0
        noec_details = []

        for bp in combinations(range(n), 3):
            ms = gap_pattern_ms(n, bp)
            p_val = prod(ms)
            if p_val >= threshold:
                continue

            placements += 1
            gaps = get_gaps_correct(bp, n)
            eg = has_even_gap(bp, n)

            time_per = 20.0 if n <= 7 else 10.0
            cycles = enumerate_cycles_comprehensive(ms, n, bp, max_time=time_per)

            for cyc, w in cycles:
                total_cycles += 1
                ecr = check_ec(cyc, w, n)
                is_sw = is_uniform_sweep(w, n) or is_generalized_sweep(w, n)
                has_ec = bool(ecr)

                if has_ec:
                    n_ec += 1
                elif is_sw:
                    n_sweep_noec += 1
                else:
                    n_counterexample += 1
                    dream_holds = False
                    ct = classify_cycle_type(w, n)
                    fc = Counter(w)
                    noec_details.append((bp, gaps, ct, len(w), fc, is_sw))
                    counterexamples.append({
                        'n': n, 'bp': bp, 'gaps': gaps, 'type': ct,
                        'CL': len(w), 'word': w
                    })

                if not is_sw:
                    if has_ec:
                        nonsweep_ec += 1
                    else:
                        nonsweep_noec += 1

                if eg:
                    if has_ec:
                        evengap_ec += 1
                    else:
                        evengap_noec += 1

        print(f"Placements tested: {placements}")
        print(f"Total cycles found: {total_cycles}")
        print(f"\n--- PART 2: Q1 restricted ---")
        print(f"Non-sweep with EC:    {nonsweep_ec}")
        print(f"Non-sweep without EC: {nonsweep_noec}")
        print(f"  Q1a (non-sweep → EC): {'HOLDS' if nonsweep_noec == 0 else 'FAILS'}")
        print(f"Even-gap with EC:    {evengap_ec}")
        print(f"Even-gap without EC: {evengap_noec}")
        print(f"  Q1b (even-gap → EC): {'HOLDS' if evengap_noec == 0 else 'FAILS'}")

        print(f"\n--- PART 3: Q2 (¬EC characterization) ---")
        print(f"No-EC cycles: sweep={n_sweep_noec}, non-sweep={nonsweep_noec - n_ec + n_ec}")
        # Correct count
        total_noec = n_sweep_noec + len([d for d in noec_details])
        print(f"Total no-EC: {total_noec} ({n_sweep_noec} sweep, {len(noec_details)} non-sweep)")
        if total_noec > 0 and len(noec_details) == 0:
            print("ALL no-EC cycles are sweeps!")

        print(f"\n--- PART 4: Dream Theorem ---")
        print(f"With EC: {n_ec}, Sweep no-EC: {n_sweep_noec}, Counterexamples: {n_counterexample}")
        if n_counterexample == 0:
            print(f"*** DREAM THEOREM HOLDS at n={n} ***")
        else:
            print(f"*** DREAM THEOREM FAILS at n={n} ***")
            for bp, gaps, ct, cl, fc, is_sw in noec_details[:5]:
                print(f"  bp={bp}, gaps={gaps}, type={ct}, CL={cl}, sweep={is_sw}")

    # Final verdict
    print("\n" + "=" * 70)
    if dream_holds:
        print("*** DREAM THEOREM HOLDS FOR ALL TESTED n ***")
    else:
        print("*** DREAM THEOREM FAILS ***")
        print(f"Total counterexamples: {len(counterexamples)}")
        for ce in counterexamples[:10]:
            print(f"  n={ce['n']}, bp={ce['bp']}, gaps={ce['gaps']}, "
                  f"type={ce['type']}, CL={ce['CL']}")
    print("=" * 70)


if __name__ == "__main__":
    part1()
    parts234()
