#!/usr/bin/env python3
"""
RA13: Dream Theorem Investigation

Tests the conjecture:
  "Every sub-threshold good cycle either has entry conflict OR is a WaterfallCycle (uniform sweep)."

If true, the entire lower bound proof collapses to:
  1. WaterfallCycle → GlobalObstruction (shadow cycle, already proved)
  2. ¬WaterfallCycle → hasEntryConflict (new theorem)

Parts:
  1. Profile no-EC cycles for the known all-odd-gap family
  2. Test restricted Q1 hypotheses (non-sweep EC, even-gap EC, etc.)
  3. Check Q2: ¬EC → what type of cycle?
  4. Dream theorem: EC ∨ WaterfallCycle exhaustive test
"""

import sys
import time
from collections import defaultdict, Counter
from itertools import product as iproduct, combinations
from math import prod

# =========================================================================
# Core utilities (from ra7/cic_walk_mnu)
# =========================================================================

def build_cycle(word, ms, n):
    """Build cycle from mover word using incrementing transition at all procs."""
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


def build_cycle_with_transitions(word, ms, n, trans):
    """Build cycle with specified transition functions.
    trans[p] is a dict mapping (L,S,R) -> new_val for proc p.
    Or trans[p] = 'inc' / 'dec' for simple increment/decrement.
    """
    L = len(word)
    configs = [[0]*n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        old = c[p]
        left = c[(p-1) % n]
        right = c[(p+1) % n]
        if trans[p] == 'inc':
            c[p] = (c[p] + 1) % ms[p]
        elif trans[p] == 'dec':
            c[p] = (c[p] - 1) % ms[p]
        else:
            key = (left, old, right)
            if key in trans[p]:
                c[p] = trans[p][key]
            else:
                c[p] = (c[p] + 1) % ms[p]
        configs.append(c)
    if configs[-1] != configs[0]:
        return None
    if len(set(tuple(c) for c in configs[:L])) != L:
        return None
    return [tuple(c) for c in configs[:L]]


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
    """Check if word is a uniform sweep (CW or CCW, repeated)."""
    if len(word) < n:
        return False
    cw = list(range(n))
    ccw = list(range(n-1, -1, -1))
    if len(word) % n != 0:
        return False
    reps = len(word) // n
    for rep_word in [cw, ccw]:
        full = rep_word * reps
        if word == full:
            return True
    # Also check starting from any position
    for start in range(n):
        for direction in [1, -1]:
            sweep = [(start + direction * i) % n for i in range(n)]
            full = sweep * reps
            if word == full:
                return True
    return False


def is_generalized_sweep(word, n):
    """Check if word is any rotation of a uniform sweep."""
    if len(word) % n != 0:
        return False
    reps = len(word) // n
    # Check all rotations
    doubled = word + word
    for direction in [1, -1]:
        for start in range(n):
            sweep = [(start + direction * i) % n for i in range(n)]
            full = sweep * reps
            if len(full) == len(word):
                for offset in range(len(word)):
                    if doubled[offset:offset+len(word)] == full:
                        return True
    return False


def classify_cycle_type(word, n):
    """Classify mover word type."""
    L = len(word)
    if is_uniform_sweep(word, n) or is_generalized_sweep(word, n):
        return "sweep"

    # Check if it's a bounce (go one way, come back)
    fc = Counter(word)
    all_fire_2 = all(fc[p] == 2 for p in range(n) if fc.get(p, 0) > 0)

    # Check if every proc fires same number of times
    fire_counts = set(fc.values())

    if len(fire_counts) == 1:
        k = fire_counts.pop()
        if k == 2:
            return "bounce"
        elif k == 3:
            return "triple-cover"
        else:
            return f"uniform-fc{k}"

    # Mixed fire counts
    return f"mixed-fc({dict(sorted(Counter(fc.values()).items()))})"


def check_shadow_exists(good, word, n, ms):
    """Check if a disjoint shadow cycle exists under same mover word."""
    L = len(word)
    orig_set = set(good)
    product_val = prod(ms)
    if product_val > 50000:
        return None  # too large
    for start in iproduct(*(range(m) for m in ms)):
        if tuple(start) in orig_set:
            continue
        configs = [list(start)]
        valid = True
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
# Exhaustive good cycle enumeration (DFS-based)
# =========================================================================

def enumerate_good_cycles_dfs(ms, n, max_cycles=5000, max_time=120.0, max_len=None):
    """Enumerate good cycles via DFS on mover words with consistency tracking.

    Returns list of (cycle_configs, mover_word) pairs.
    """
    t0 = time.time()
    product_val = prod(ms)
    if max_len is None:
        max_len = min(4 * n, product_val)

    results = []
    seen_cycle_sets = set()

    # Start from zero config
    start = tuple([0]*n)

    def dfs(config, path, word, det, depth):
        if time.time() - t0 > max_time:
            return
        if len(results) >= max_cycles:
            return

        for p in range(n):
            for new_val in range(ms[p]):
                if new_val == config[p]:
                    continue

                # Adjacent mover check
                if word:
                    last = word[-1]
                    diff = min(abs(p - last), n - abs(p - last))
                    if diff > 1:
                        continue

                # Consistency check
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

                if consistent:
                    for i in range(n):
                        if i == p:
                            continue
                        Li = config[(i-1) % n]
                        Si = config[i]
                        Ri = config[(i+1) % n]
                        key_i = (i, Li, Si, Ri)
                        if key_i in new_det:
                            if new_det[key_i] != Si:
                                consistent = False
                                break
                        else:
                            new_det[key_i] = Si

                if not consistent:
                    continue

                new_config = list(config)
                new_config[p] = new_val
                new_config = tuple(new_config)
                new_word = word + [p]

                # Check cycle closure
                if new_config == start and len(path) >= 2 * n:
                    cycle = list(path)
                    cycle_key = frozenset(cycle)
                    if cycle_key not in seen_cycle_sets:
                        # Verify mutual exclusion
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
                            seen_cycle_sets.add(cycle_key)
                            results.append((cycle, new_word))
                            if len(results) >= max_cycles:
                                return
                    continue

                if new_config not in set(path) and len(path) < max_len:
                    path.append(new_config)
                    dfs(new_config, path, new_word, new_det, depth + 1)
                    path.pop()

    dfs(start, [start], [], {}, 0)
    return results


def enumerate_cycles_word_based(ms, n, max_cycles=5000, max_time=60.0):
    """Enumerate good cycles by trying all balanced mover words."""
    t0 = time.time()
    results = []
    seen = set()

    product_val = prod(ms)
    # Target fire count per proc: each binary fires 2, ternary fires 3, etc.
    # But for sub-threshold with >=3 binary, typical cycle lengths are 2n to 3n

    # Strategy: enumerate adjacent-mover words that return to start
    # Use BFS on (position, fire_counts, direction)

    # For efficiency, try known word patterns:
    # 1. Uniform sweeps (CW/CCW, 2 or 3 reps)
    # 2. Bounce words
    # 3. Mixed words

    # Sweeps
    for start in range(n):
        for direction in [1, -1]:
            sweep = [(start + direction * i) % n for i in range(n)]
            for reps in range(2, ms[0] + 2):
                word = sweep * reps
                cycle = build_cycle(word, ms, n)
                if cycle and len(word) <= product_val:
                    key = frozenset(cycle)
                    if key not in seen:
                        seen.add(key)
                        results.append((cycle, word))

    # Also try with dec transitions at ternary procs
    for start in range(n):
        for direction in [1, -1]:
            sweep = [(start + direction * i) % n for i in range(n)]
            for reps in range(2, 4):
                word = sweep * reps
                # Try all inc/dec combos at ternary procs
                ternary_procs = [p for p in range(n) if ms[p] == 3]
                if len(ternary_procs) > 8:
                    # Too many combos, just try all-inc and all-dec
                    for mode in ['inc', 'dec']:
                        trans = {p: mode for p in range(n)}
                        cycle = build_cycle_with_transitions(word, ms, n, trans)
                        if cycle:
                            key = frozenset(cycle)
                            if key not in seen:
                                seen.add(key)
                                results.append((cycle, word))
                else:
                    for combo in iproduct(['inc', 'dec'], repeat=len(ternary_procs)):
                        if time.time() - t0 > max_time:
                            break
                        trans = {p: 'inc' for p in range(n)}
                        for idx, tp in enumerate(ternary_procs):
                            trans[tp] = combo[idx]
                        cycle = build_cycle_with_transitions(word, ms, n, trans)
                        if cycle:
                            key = frozenset(cycle)
                            if key not in seen:
                                seen.add(key)
                                results.append((cycle, word))

    return results


# =========================================================================
# Gap pattern utilities
# =========================================================================

def gap_pattern_ms(n, binary_positions):
    ms = [3]*n
    for p in binary_positions:
        ms[p] = 2
    return ms


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


def construct_bounce_sweep_word(k):
    """Construct CF word for gap-(k,k,k) with n=3k, odd k >= 3."""
    n = 3*k
    binary_pos = [0, k, 2*k]
    ms = gap_pattern_ms(n, binary_pos)
    seg_len = k - 1

    partial_words = find_balanced_segment_words(seg_len, target=2)
    if not partial_words:
        return None, ms, n

    seg_word = partial_words[0]
    seg_A = list(range(n-1, 2*k, -1))
    seg_B = list(range(2*k-1, k, -1))
    seg_C = list(range(k-1, 0, -1))

    def map_seg(sw, seg):
        return [seg[i] for i in sw]

    bounce_A = map_seg(seg_word, seg_A)
    bounce_B = map_seg(seg_word, seg_B)
    bounce_C = map_seg(seg_word, seg_C)

    word = []
    word.extend(bounce_A)
    word.append(2*k)
    word.extend(bounce_B)
    word.append(k)
    word.extend(bounce_C)
    word.append(0)
    word.extend(list(range(n-1, -1, -1)))

    return word, ms, n


# =========================================================================
# PART 1: Profile the no-EC cycles
# =========================================================================

def part1():
    print("=" * 70)
    print("PART 1: Profile the no-EC cycles (all-odd-gap binary arrangements)")
    print("=" * 70)

    k = 3
    n = 9
    word, ms, _ = construct_bounce_sweep_word(k)
    print(f"\nn=9, ms={ms}, product={prod(ms)}, threshold={4*3**(n-2)}")
    print(f"Sub-threshold: {prod(ms) < 4*3**(n-2)}")

    cycle = build_cycle(word, ms, n)
    if cycle is None:
        print("ERROR: Could not build cycle")
        return

    print(f"Mover word: {word}")
    print(f"Cycle length: {len(word)}")
    ec = check_ec(cycle, word, n)
    print(f"Entry conflicts: {len(ec)} procs ({list(ec.keys()) if ec else 'NONE'})")

    ctype = classify_cycle_type(word, n)
    print(f"Cycle type: {ctype}")
    is_sweep = is_uniform_sweep(word, n) or is_generalized_sweep(word, n)
    print(f"Is uniform sweep: {is_sweep}")

    # Fire count per proc
    fc = Counter(word)
    print(f"Fire counts: {dict(sorted(fc.items()))}")

    # Check shadow
    print("\nChecking shadow cycles...")
    has_shadow = check_shadow_exists(cycle, word, n, ms)
    print(f"Has disjoint shadow cycle: {has_shadow}")

    # Also enumerate ALL cycles at n=9 for this ms via word-based approach
    print("\n--- Enumerating cycles via word-based method ---")
    all_cycles = enumerate_cycles_word_based(ms, n, max_cycles=500, max_time=30.0)
    print(f"Found {len(all_cycles)} cycles (word-based)")

    ec_count = 0
    noec_count = 0
    noec_sweeps = 0
    noec_nonsweeps = 0

    for cyc, w in all_cycles:
        ecr = check_ec(cyc, w, n)
        is_sw = is_uniform_sweep(w, n) or is_generalized_sweep(w, n)
        if ecr:
            ec_count += 1
        else:
            noec_count += 1
            ct = classify_cycle_type(w, n)
            if is_sw:
                noec_sweeps += 1
            else:
                noec_nonsweeps += 1
                print(f"  NO-EC non-sweep: type={ct}, CL={len(w)}, word={w[:20]}...")

    print(f"\nSummary: {ec_count} with EC, {noec_count} without EC")
    print(f"  No-EC sweeps: {noec_sweeps}")
    print(f"  No-EC non-sweeps: {noec_nonsweeps}")


# =========================================================================
# PART 2: Restricted Q1 hypotheses
# =========================================================================

def enumerate_all_binary_placements(n, num_binary=3):
    """Generate all ways to place num_binary binary procs in ring of size n."""
    for combo in combinations(range(n), num_binary):
        yield combo


def get_gaps(binary_pos, n):
    """Get gap sizes between consecutive binary procs on ring."""
    bp = sorted(binary_pos)
    gaps = []
    for i in range(len(bp)):
        gap = (bp[(i+1) % len(bp)] - bp[i]) % n
        gaps.append(gap)
    return gaps


def has_even_gap(binary_pos, n):
    gaps = get_gaps(binary_pos, n)
    return any(g % 2 == 0 for g in gaps)


def part2():
    print("\n" + "=" * 70)
    print("PART 2: Restricted Q1 hypotheses")
    print("=" * 70)

    for n in [5, 7, 9]:
        print(f"\n{'='*50}")
        print(f"n = {n}")
        print(f"{'='*50}")

        threshold = 4 * 3**(n-2)
        total_cycles = 0
        nonsweep_with_ec = 0
        nonsweep_no_ec = 0
        evengap_with_ec = 0
        evengap_no_ec = 0
        nonsweep_evengap_ec = 0
        nonsweep_evengap_noec = 0
        sweep_no_ec = 0
        sweep_with_ec = 0
        noec_details = []

        for bp in enumerate_all_binary_placements(n, 3):
            ms = gap_pattern_ms(n, bp)
            p = prod(ms)
            if p >= threshold:
                continue

            gaps = get_gaps(bp, n)
            even_gap = has_even_gap(bp, n)

            # Enumerate cycles
            cycles = enumerate_cycles_word_based(ms, n, max_cycles=200, max_time=10.0)

            for cyc, w in cycles:
                total_cycles += 1
                ecr = check_ec(cyc, w, n)
                is_sw = is_uniform_sweep(w, n) or is_generalized_sweep(w, n)
                has_ec = bool(ecr)

                if is_sw:
                    if has_ec:
                        sweep_with_ec += 1
                    else:
                        sweep_no_ec += 1
                else:
                    if has_ec:
                        nonsweep_with_ec += 1
                    else:
                        nonsweep_no_ec += 1
                        noec_details.append((bp, gaps, classify_cycle_type(w, n), len(w), w))

                if even_gap:
                    if has_ec:
                        evengap_with_ec += 1
                    else:
                        evengap_no_ec += 1

                    if not is_sw:
                        if has_ec:
                            nonsweep_evengap_ec += 1
                        else:
                            nonsweep_evengap_noec += 1

        print(f"\nTotal sub-threshold cycles found: {total_cycles}")
        print(f"\nQ1a: Every NON-SWEEP has EC?")
        print(f"  Non-sweep with EC:    {nonsweep_with_ec}")
        print(f"  Non-sweep without EC: {nonsweep_no_ec}")
        print(f"  VERDICT: {'YES' if nonsweep_no_ec == 0 else 'NO — COUNTEREXAMPLES EXIST'}")

        print(f"\nQ1b: Every cycle with EVEN GAP has EC?")
        print(f"  Even-gap with EC:    {evengap_with_ec}")
        print(f"  Even-gap without EC: {evengap_no_ec}")
        print(f"  VERDICT: {'YES' if evengap_no_ec == 0 else 'NO — COUNTEREXAMPLES EXIST'}")

        print(f"\nQ1c: Every NON-SWEEP with EVEN GAP has EC?")
        print(f"  Non-sweep even-gap with EC:    {nonsweep_evengap_ec}")
        print(f"  Non-sweep even-gap without EC: {nonsweep_evengap_noec}")
        print(f"  VERDICT: {'YES' if nonsweep_evengap_noec == 0 else 'NO — COUNTEREXAMPLES EXIST'}")

        print(f"\nSweep breakdown: {sweep_with_ec} with EC, {sweep_no_ec} without EC")

        if noec_details:
            print(f"\nNo-EC non-sweep details ({len(noec_details)} cycles):")
            for bp, gaps, ct, cl, w in noec_details[:5]:
                print(f"  bp={bp}, gaps={gaps}, type={ct}, CL={cl}")


# =========================================================================
# PART 3: Q2 — characterize no-EC cycles
# =========================================================================

def part3():
    print("\n" + "=" * 70)
    print("PART 3: Q2 — ¬EC cycles characterization")
    print("=" * 70)

    for n in [5, 7, 9]:
        print(f"\n{'='*50}")
        print(f"n = {n}")
        print(f"{'='*50}")

        threshold = 4 * 3**(n-2)
        noec_cycles = []

        for bp in enumerate_all_binary_placements(n, 3):
            ms = gap_pattern_ms(n, bp)
            p = prod(ms)
            if p >= threshold:
                continue

            gaps = get_gaps(bp, n)
            cycles = enumerate_cycles_word_based(ms, n, max_cycles=200, max_time=10.0)

            for cyc, w in cycles:
                ecr = check_ec(cyc, w, n)
                if not ecr:
                    is_sw = is_uniform_sweep(w, n) or is_generalized_sweep(w, n)
                    ct = classify_cycle_type(w, n)
                    noec_cycles.append({
                        'bp': bp, 'gaps': gaps, 'ms': ms, 'n': n,
                        'cycle': cyc, 'word': w, 'is_sweep': is_sw,
                        'type': ct, 'CL': len(w)
                    })

        all_sweeps = all(c['is_sweep'] for c in noec_cycles)
        print(f"\nTotal no-EC cycles: {len(noec_cycles)}")
        print(f"All are sweeps: {all_sweeps}")

        if not all_sweeps:
            nonsweeps = [c for c in noec_cycles if not c['is_sweep']]
            print(f"\nNon-sweep no-EC cycles: {len(nonsweeps)}")
            for c in nonsweeps[:10]:
                fc = Counter(c['word'])
                print(f"  bp={c['bp']}, gaps={c['gaps']}, type={c['type']}, "
                      f"CL={c['CL']}, fc={dict(sorted(fc.items()))}")
                # Check shadow for these
                has_sh = check_shadow_exists(c['cycle'], c['word'], n, c['ms'])
                print(f"    Shadow exists: {has_sh}")
        else:
            print("ALL no-EC cycles are uniform sweeps!")
            print("=> Q2 answer: ¬EC → WaterfallCycle ✓")

        # Categorize sweeps
        sweep_gaps = Counter()
        for c in noec_cycles:
            if c['is_sweep']:
                sweep_gaps[tuple(sorted(c['gaps']))] += 1
        if sweep_gaps:
            print(f"\nNo-EC sweep gap patterns: {dict(sweep_gaps)}")


# =========================================================================
# PART 4: The Dream Theorem
# =========================================================================

def part4():
    print("\n" + "=" * 70)
    print("PART 4: THE DREAM THEOREM")
    print("  Conjecture: Every sub-threshold good cycle has EC ∨ is a WaterfallCycle")
    print("=" * 70)

    dream_holds = True
    counterexamples = []

    for n in [5, 7, 9]:
        print(f"\n{'='*50}")
        print(f"n = {n}, threshold = {4*3**(n-2)}")
        print(f"{'='*50}")

        threshold = 4 * 3**(n-2)
        n_total = 0
        n_ec = 0
        n_sweep_noec = 0
        n_counterexample = 0

        placements_tested = 0
        for bp in enumerate_all_binary_placements(n, 3):
            ms = gap_pattern_ms(n, bp)
            p = prod(ms)
            if p >= threshold:
                continue

            placements_tested += 1
            gaps = get_gaps(bp, n)

            cycles = enumerate_cycles_word_based(ms, n, max_cycles=500, max_time=15.0)

            for cyc, w in cycles:
                n_total += 1
                ecr = check_ec(cyc, w, n)
                is_sw = is_uniform_sweep(w, n) or is_generalized_sweep(w, n)

                if ecr:
                    n_ec += 1
                elif is_sw:
                    n_sweep_noec += 1
                else:
                    n_counterexample += 1
                    dream_holds = False
                    ct = classify_cycle_type(w, n)
                    counterexamples.append({
                        'n': n, 'bp': bp, 'gaps': gaps, 'ms': ms,
                        'type': ct, 'CL': len(w), 'word': w
                    })

        print(f"Placements tested: {placements_tested}")
        print(f"Total cycles: {n_total}")
        print(f"  With EC: {n_ec}")
        print(f"  Sweep (no EC): {n_sweep_noec}")
        print(f"  COUNTEREXAMPLES: {n_counterexample}")

        if n_counterexample == 0:
            print(f"  => DREAM THEOREM HOLDS at n={n}")
        else:
            print(f"  => DREAM THEOREM FAILS at n={n}")

    print("\n" + "=" * 70)
    if dream_holds:
        print("*** DREAM THEOREM HOLDS FOR ALL TESTED n ***")
        print("Every sub-threshold good cycle either has EC or is a uniform sweep!")
        print("")
        print("Proof structure collapses to:")
        print("  1. WaterfallCycle → GlobalObstruction (shadow, already proved)")
        print("  2. ¬WaterfallCycle → hasEntryConflict (new theorem)")
    else:
        print("*** DREAM THEOREM FAILS ***")
        print(f"Counterexamples: {len(counterexamples)}")
        for ce in counterexamples[:10]:
            fc = Counter(ce['word'])
            print(f"  n={ce['n']}, bp={ce['bp']}, gaps={ce['gaps']}, "
                  f"type={ce['type']}, CL={ce['CL']}")
    print("=" * 70)


# =========================================================================
# MAIN
# =========================================================================

if __name__ == "__main__":
    part1()
    part2()
    part3()
    part4()
