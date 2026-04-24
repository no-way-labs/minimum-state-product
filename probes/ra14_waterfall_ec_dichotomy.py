#!/usr/bin/env python3
"""
RA14: Decisive test — does every non-WaterfallCycle sub-threshold good cycle
with n>=9 and >=3 binary have entry conflict?

WaterfallCycle = uniform sweep (CL=2n, waterfall form).
Entry conflict = same (L,S,R) triple at proc i appears at both mover and non-mover step.

Strategy:
  1. Enumerate all sub-threshold multisets with >=3 binary at n=9.
  2. For each, find good cycles via:
     a) Constructed sweep words (uniform sweeps with various transition modes)
     b) Constructed bounce/wiggle words
     c) DFS for small products
  3. Classify each cycle as WaterfallCycle or not.
  4. For non-WaterfallCycle: check entry conflict.
  5. For non-EC non-WaterfallCycle: check shadow existence.
"""

import sys
import time
from collections import Counter, defaultdict
from itertools import product as iproduct, combinations, combinations_with_replacement
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
    for j in range(n):
        overlap = mover_triples[j] & nonmover_triples[j]
        if overlap:
            return True
    return False


def is_uniform_sweep(word, n):
    """Check if word is a uniform sweep (any start, CW or CCW, any rotation)."""
    L = len(word)
    if L % n != 0:
        return False
    reps = L // n
    doubled = word + word
    for start in range(n):
        for direction in [1, -1]:
            sweep = [(start + direction * i) % n for i in range(n)]
            full = sweep * reps
            for offset in range(L):
                if doubled[offset:offset+L] == full:
                    return True
    return False


def is_waterfall_cycle(good, word, n, ms):
    """Check if cycle is a WaterfallCycle: uniform sweep with CL=2n."""
    L = len(word)
    # WaterfallCycle: CL = 2n, uniform sweep structure
    if L != 2 * n:
        return False
    if not is_uniform_sweep(word, n):
        return False
    # Additional check: each proc fires exactly 2 times
    fc = Counter(word)
    for p in range(n):
        if fc.get(p, 0) != 2:
            return False
    return True


def fire_counts(word, n):
    fc = Counter(word)
    return tuple(fc.get(p, 0) for p in range(n))


# =========================================================================
# Cycle construction
# =========================================================================

def build_cycle_trans(word, ms, n, trans_mode):
    """Build cycle with per-proc transition mode.
    trans_mode[p] = delta for proc p when it fires.
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
    config_set = set(tuple(c) for c in configs[:L])
    if len(config_set) != L:
        return None
    return [tuple(c) for c in configs[:L]]


def build_cycle_inc(word, ms, n):
    trans = {p: 1 for p in range(n)}
    return build_cycle_trans(word, ms, n, trans)


def generate_all_sweep_words(n, reps_range=range(1, 8)):
    """Generate uniform sweep words of various repetitions."""
    words = []
    for start in range(n):
        for direction in [1, -1]:
            sweep = [(start + direction * i) % n for i in range(n)]
            for reps in reps_range:
                words.append(sweep * reps)
    return words


def generate_bounce_words(n, max_bounces=4):
    """Generate bounce words: CW then CCW (or vice versa)."""
    words = []
    # Standard bounce: 0,1,...,n-1,n-2,...,1
    bounce_cw = list(range(n)) + list(range(n-2, 0, -1))
    bounce_ccw = list(range(n-1, -1, -1)) + list(range(1, n-1))
    for b in [bounce_cw, bounce_ccw]:
        for reps in range(1, max_bounces + 1):
            words.append(b * reps)
    # Also try starting from different positions
    for start in range(n):
        for direction in [1, -1]:
            fwd = [(start + direction * i) % n for i in range(n)]
            bwd = list(reversed(fwd[1:-1]))
            bounce = fwd + bwd
            for reps in range(1, max_bounces + 1):
                words.append(bounce * reps)
    return words


def generate_wiggle_words(n):
    """Generate single-wiggle words."""
    words = []
    for start in range(n):
        for direction in [1, -1]:
            # Sweep most of the way, then reverse for 1 step, then continue
            for wiggle_pos in range(2, n-1):
                fwd = [(start + direction * i) % n for i in range(wiggle_pos)]
                back = [(start + direction * (wiggle_pos - 1)) % n]
                rest = [(start + direction * i) % n for i in range(wiggle_pos - 1, n)]
                word = fwd + back + rest
                words.append(word)
    return words


def try_all_trans_modes(word, ms, n, max_combos=512):
    """Try all transition modes for a word. Return list of (configs, word) pairs."""
    results = []
    # Only vary ternary+ procs
    non_binary = [p for p in range(n) if ms[p] > 2]
    binary = [p for p in range(n) if ms[p] == 2]

    if len(non_binary) > 9:
        # Too many combos, just try inc and dec
        combos = [(1,)*len(non_binary), (-1,)*len(non_binary)]
    else:
        combos = list(iproduct([1, -1], repeat=len(non_binary)))

    for combo in combos[:max_combos]:
        tm = {}
        for p in binary:
            tm[p] = 1  # binary always +1
        for idx, p in enumerate(non_binary):
            tm[p] = combo[idx]
        cyc = build_cycle_trans(word, ms, n, tm)
        if cyc:
            results.append(cyc)
    return results


# =========================================================================
# DFS cycle enumeration (for small products)
# =========================================================================

def enumerate_good_cycles_dfs(ms, n, max_cycles=5000, max_time=30.0):
    """Enumerate good cycles via DFS from all-zero config."""
    t0 = time.time()
    product_val = prod(ms)
    if product_val > 3000:
        return []

    start = tuple([0]*n)
    results = []
    seen = set()
    max_len = min(4 * n, product_val)

    def dfs(config, path, word, det, depth):
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
                L_val = config[(p-1) % n]
                S_val = config[p]
                R_val = config[(p+1) % n]
                key_m = (p, L_val, S_val, R_val)
                new_det = dict(det)
                if key_m in new_det:
                    if new_det[key_m] != new_val:
                        continue
                else:
                    new_det[key_m] = new_val
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
                    # Check all procs fire at least once
                    fc = Counter(new_word)
                    if len(fc) == n:
                        # Check mutual exclusion
                        cycle = list(path)
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
# Shadow check
# =========================================================================

def check_shadow_exists(good, word, n, ms):
    """Check if a shadow cycle exists (disjoint cycle with same mover word)."""
    L = len(word)
    orig_set = set(good)
    product_val = prod(ms)
    if product_val > 10000:
        return None  # too large

    for start in iproduct(*(range(m) for m in ms)):
        start = tuple(start)
        if start in orig_set:
            continue
        configs = [list(start)]
        valid = True
        for t in range(L):
            c = list(configs[-1])
            p = word[t]
            c[p] = (c[p] + 1) % ms[p]  # inc transition
            configs.append(c)
        if configs[-1] != list(configs[0]):
            continue
        cycle_set = set(tuple(c) for c in configs[:L])
        if len(cycle_set) != L:
            continue
        if cycle_set & orig_set:
            continue
        return True

    # Also try dec transitions
    for start in iproduct(*(range(m) for m in ms)):
        start = tuple(start)
        if start in orig_set:
            continue
        configs = [list(start)]
        for t in range(L):
            c = list(configs[-1])
            p = word[t]
            c[p] = (c[p] - 1) % ms[p]
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
# Enumerate sub-threshold multisets
# =========================================================================

def sub_threshold_multisets(n, min_binary=3):
    """Enumerate all sub-threshold multisets with >=min_binary binary procs.
    Sub-threshold: product < 4 * 3^(n-2).
    """
    threshold = 4 * 3**(n-2)
    results = []

    # Enumerate number of binary procs: min_binary to n
    for num_binary in range(min_binary, n+1):
        num_non_binary = n - num_binary
        binary_product = 2**num_binary
        remaining_budget = threshold // binary_product  # product of non-binary must be < this

        if num_non_binary == 0:
            if binary_product < threshold:
                results.append(tuple([2]*n))
            continue

        # Enumerate non-binary state counts (each >= 3)
        # Product of num_non_binary values each >= 3, total < remaining_budget
        def enum_nb(k, budget, current):
            if k == 0:
                if current:
                    results.append(current)
                return
            for m in range(3, min(budget+1, 20)):  # cap at reasonable value
                if m**k > budget:
                    break
                enum_nb(k-1, budget // m, current + (m,))

        if remaining_budget >= 3**num_non_binary:
            enum_nb(num_non_binary, remaining_budget - 1, tuple([2]*num_binary))

    return results


def all_placements(ms_sorted, n):
    """Generate all distinct ring placements of a sorted multiset."""
    from itertools import permutations
    seen = set()
    results = []
    for perm in permutations(ms_sorted):
        # Ring equivalence: rotation and reflection
        canonical = min(
            tuple(perm[i:] + perm[:i]) for i in range(n)
        )
        canonical2 = min(
            tuple(perm[::-1][i:] + perm[::-1][:i]) for i in range(n)
        )
        canon = min(canonical, canonical2)
        if canon not in seen:
            seen.add(canon)
            results.append(list(perm))
    return results


# =========================================================================
# Main tests
# =========================================================================

def test_n9():
    n = 9
    threshold = 4 * 3**(n-2)
    print(f"n={n}, threshold={threshold}")
    print(f"WaterfallCycle: uniform sweep with CL=2n={2*n}")
    print()

    # Get sub-threshold multisets
    multisets = sub_threshold_multisets(n, min_binary=3)
    print(f"Sub-threshold multiset types (sorted): {len(multisets)}")

    total_cycles = 0
    total_waterfall = 0
    total_nonwf_ec = 0
    total_nonwf_noec = 0
    counterexamples = []

    for ms_sorted in multisets:
        p_val = prod(ms_sorted)
        # Get all distinct placements
        placements = all_placements(ms_sorted, n)

        for ms in placements:
            binary_pos = [i for i in range(n) if ms[i] == 2]
            if len(binary_pos) < 3:
                continue

            # Generate candidate words
            all_words = []

            # Sweeps
            for w in generate_all_sweep_words(n, reps_range=range(1, 8)):
                fc = Counter(w)
                # Check fire counts compatible with ms
                ok = True
                for p in range(n):
                    if fc.get(p, 0) % ms[p] != 0:
                        ok = False
                        break
                    if fc.get(p, 0) == 0:
                        ok = False
                        break
                if ok:
                    all_words.append(w)

            # Bounces
            for w in generate_bounce_words(n, max_bounces=3):
                fc = Counter(w)
                ok = True
                for p in range(n):
                    if fc.get(p, 0) % ms[p] != 0:
                        ok = False
                        break
                    if fc.get(p, 0) == 0:
                        ok = False
                        break
                if ok and len(w) <= 4 * n:
                    all_words.append(w)

            # Wiggles
            for w in generate_wiggle_words(n):
                fc = Counter(w)
                ok = True
                for p in range(n):
                    if fc.get(p, 0) % ms[p] != 0:
                        ok = False
                        break
                    if fc.get(p, 0) == 0:
                        ok = False
                        break
                if ok and len(w) <= 4 * n:
                    all_words.append(w)

            # Deduplicate words
            unique_words = list(set(tuple(w) for w in all_words))

            cycles_this = []
            seen_configs = set()

            for w in unique_words:
                w = list(w)
                for cyc in try_all_trans_modes(w, ms, n, max_combos=512):
                    key = frozenset(cyc)
                    if key not in seen_configs:
                        seen_configs.add(key)
                        cycles_this.append((cyc, w))

            # DFS for small products
            if p_val <= 2500:
                dfs_cycles = enumerate_good_cycles_dfs(ms, n, max_cycles=2000, max_time=15.0)
                for cyc, w in dfs_cycles:
                    key = frozenset(cyc)
                    if key not in seen_configs:
                        seen_configs.add(key)
                        cycles_this.append((cyc, w))

            wf_count = 0
            nonwf_ec_count = 0
            nonwf_noec_count = 0

            for cyc, w in cycles_this:
                total_cycles += 1
                is_wf = is_waterfall_cycle(cyc, w, n, ms)

                if is_wf:
                    wf_count += 1
                    total_waterfall += 1
                else:
                    has_ec = check_ec(cyc, w, n)
                    if has_ec:
                        nonwf_ec_count += 1
                        total_nonwf_ec += 1
                    else:
                        nonwf_noec_count += 1
                        total_nonwf_noec += 1
                        fc_tuple = fire_counts(w, n)
                        ct = "sweep" if is_uniform_sweep(w, n) else f"CL={len(w)},fc={fc_tuple}"
                        counterexamples.append({
                            'ms': list(ms),
                            'binary_pos': binary_pos,
                            'type': ct,
                            'CL': len(w),
                            'fc': fc_tuple,
                            'word': w[:30],
                            'cycle': cyc,
                            'full_word': w,
                        })

            if cycles_this:
                gaps = []
                bp_s = sorted(binary_pos)
                for i in range(len(bp_s)):
                    nxt = bp_s[(i+1) % len(bp_s)]
                    cur = bp_s[i]
                    gaps.append((nxt - cur) % n)

                print(f"ms={ms}, product={p_val}, binary={binary_pos}, gaps={gaps}")
                print(f"  Cycles: {len(cycles_this)} (WF={wf_count}, nonWF_EC={nonwf_ec_count}, nonWF_noEC={nonwf_noec_count})")

    print()
    print("=" * 70)
    print("SUMMARY FOR n=9")
    print("=" * 70)
    print(f"Total cycles found: {total_cycles}")
    print(f"  WaterfallCycles: {total_waterfall}")
    print(f"  Non-WF with EC: {total_nonwf_ec}")
    print(f"  Non-WF without EC: {total_nonwf_noec}")
    print()

    if counterexamples:
        print(f"COUNTEREXAMPLES ({len(counterexamples)}):")
        for cx in counterexamples[:20]:
            print(f"  ms={cx['ms']}, binary={cx['binary_pos']}, type={cx['type']}, CL={cx['CL']}")
            print(f"    fc={cx['fc']}, word_prefix={cx['word']}")

        # Check shadow for counterexamples
        print()
        print("Shadow check for counterexamples:")
        for i, cx in enumerate(counterexamples[:10]):
            ms_cx = cx['ms']
            p_val = prod(ms_cx)
            has_sh = check_shadow_exists(cx['cycle'], cx['full_word'], n, ms_cx)
            print(f"  [{i}] ms={ms_cx}, product={p_val}, CL={cx['CL']}: shadow={has_sh}")
    else:
        print("NO COUNTEREXAMPLES — every non-WaterfallCycle has entry conflict!")

    print()
    if total_nonwf_noec == 0:
        print("THE ANSWER: YES — every non-WaterfallCycle sub-threshold good cycle at n=9 has entry conflict.")
    else:
        print("THE ANSWER: NO — there exist non-WaterfallCycle sub-threshold good cycles at n=9 without entry conflict.")

    return counterexamples


def test_small_n():
    """Calibration at n=5 and n=7."""
    for n in [5, 7]:
        threshold = 4 * 3**(n-2)
        print(f"\n{'='*70}")
        print(f"CALIBRATION: n={n}, threshold={threshold}")
        print(f"{'='*70}")

        multisets = sub_threshold_multisets(n, min_binary=3)
        print(f"Multiset types: {len(multisets)}")

        total_cycles = 0
        total_wf = 0
        total_nonwf_ec = 0
        total_nonwf_noec = 0

        for ms_sorted in multisets:
            p_val = prod(ms_sorted)
            placements = all_placements(ms_sorted, n)

            for ms in placements:
                binary_pos = [i for i in range(n) if ms[i] == 2]
                if len(binary_pos) < 3:
                    continue

                # Generate words
                all_words = []
                for w in generate_all_sweep_words(n):
                    fc = Counter(w)
                    ok = all(fc.get(p, 0) % ms[p] == 0 and fc.get(p, 0) > 0 for p in range(n))
                    if ok:
                        all_words.append(w)

                for w in generate_bounce_words(n, max_bounces=3):
                    fc = Counter(w)
                    ok = all(fc.get(p, 0) % ms[p] == 0 and fc.get(p, 0) > 0 for p in range(n))
                    if ok and len(w) <= 4*n:
                        all_words.append(w)

                unique_words = list(set(tuple(w) for w in all_words))

                cycles_this = []
                seen = set()

                for w in unique_words:
                    w = list(w)
                    for cyc in try_all_trans_modes(w, ms, n, max_combos=256):
                        key = frozenset(cyc)
                        if key not in seen:
                            seen.add(key)
                            cycles_this.append((cyc, w))

                # DFS
                dfs_cycles = enumerate_good_cycles_dfs(ms, n, max_cycles=3000, max_time=20.0)
                for cyc, w in dfs_cycles:
                    key = frozenset(cyc)
                    if key not in seen:
                        seen.add(key)
                        cycles_this.append((cyc, w))

                for cyc, w in cycles_this:
                    total_cycles += 1
                    is_wf = is_waterfall_cycle(cyc, w, n, ms)
                    if is_wf:
                        total_wf += 1
                    else:
                        if check_ec(cyc, w, n):
                            total_nonwf_ec += 1
                        else:
                            total_nonwf_noec += 1
                            fc_t = fire_counts(w, n)
                            print(f"  NO-EC non-WF: ms={ms}, CL={len(w)}, fc={fc_t}")

        print(f"\nn={n} totals: {total_cycles} cycles, WF={total_wf}, nonWF_EC={total_nonwf_ec}, nonWF_noEC={total_nonwf_noec}")
        if total_nonwf_noec == 0:
            print(f"  -> Every non-WF cycle at n={n} has EC.")
        else:
            print(f"  -> {total_nonwf_noec} non-WF cycles WITHOUT EC at n={n}.")


if __name__ == '__main__':
    print("RA14: WaterfallCycle vs EntryConflict Dichotomy Test")
    print("=" * 70)

    # First calibrate at small n
    test_small_n()

    # Then the decisive test at n=9
    print("\n" + "=" * 70)
    print("DECISIVE TEST: n=9")
    print("=" * 70)
    counterexamples = test_n9()
