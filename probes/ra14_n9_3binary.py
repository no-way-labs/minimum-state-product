#!/usr/bin/env python3
"""
RA14 v5: Focus specifically on 3-binary multisets at n=9.

The counting lemma says: at n=9, product < 8748 with <=2 binary implies product >= 8748.
So >=3 binary is required. But the MAIN case is exactly 3 binary (the hardest case).

Question: for 3-binary at n=9, does every non-sweep cycle have EC?
Previous result: YES for pure {2,3} with 3 binary.
Now check: also for 3 binary with non-{2,3} multisets (e.g., {2^3, 3^5, 4}).
"""

import sys
import time
from collections import Counter, defaultdict
from itertools import product as iproduct, permutations
from math import prod

def check_ec(good, word, n):
    L = len(word)
    mt = defaultdict(set)
    nt = defaultdict(set)
    for t in range(L):
        c = good[t]
        m = word[t]
        for j in range(n):
            triple = (c[(j-1)%n], c[j], c[(j+1)%n])
            if j == m:
                mt[j].add(triple)
            else:
                nt[j].add(triple)
    for j in range(n):
        if mt[j] & nt[j]:
            return True
    return False

def is_uniform_sweep(word, n):
    L = len(word)
    if L % n != 0:
        return False
    reps = L // n
    doubled = word + word
    for start in range(n):
        for d in [1, -1]:
            sweep = [(start + d * i) % n for i in range(n)]
            full = sweep * reps
            for off in range(L):
                if doubled[off:off+L] == full:
                    return True
    return False

def build_cycle_trans(word, ms, n, trans_mode):
    L = len(word)
    configs = [[0]*n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + trans_mode[p]) % ms[p]
        configs.append(c)
    if configs[-1] != configs[0]:
        return None
    cs = set(tuple(c) for c in configs[:L])
    if len(cs) != L:
        return None
    return [tuple(c) for c in configs[:L]]

def try_trans(word, ms, n, max_combos=512):
    results = []
    nb = [p for p in range(n) if ms[p] > 2]
    bp = [p for p in range(n) if ms[p] == 2]
    combos = list(iproduct([1, -1], repeat=len(nb)))[:max_combos]
    for combo in combos:
        tm = {p: 1 for p in bp}
        for idx, p in enumerate(nb):
            tm[p] = combo[idx]
        fc = Counter(word)
        ok = all(fc.get(p, 0) > 0 and (fc.get(p, 0) * tm[p]) % ms[p] == 0 for p in range(n))
        if not ok:
            continue
        cyc = build_cycle_trans(word, ms, n, tm)
        if cyc:
            results.append(cyc)
    return results

def generate_words(n, ms):
    words = set()
    for start in range(n):
        for d in [1, -1]:
            sweep = [(start + d * i) % n for i in range(n)]
            for reps in range(2, 7):
                w = tuple(sweep * reps)
                fc = Counter(w)
                if all(fc.get(p, 0) > 0 for p in range(n)):
                    words.add(w)
            fwd = [(start + d * i) % n for i in range(n)]
            bwd = list(reversed(fwd[1:-1]))
            bounce = fwd + bwd
            for reps in range(1, 4):
                w = tuple(bounce * reps)
                fc = Counter(w)
                if all(fc.get(p, 0) > 0 for p in range(n)) and len(w) <= 5*n:
                    words.add(w)
            w = tuple(sweep + list(reversed(sweep)))
            fc = Counter(w)
            if all(fc.get(p, 0) > 0 for p in range(n)):
                words.add(w)
    return list(words)

def all_placements_fast(ms_sorted, n):
    seen = set()
    results = []
    for perm in set(permutations(ms_sorted)):
        canonical = min(
            min(tuple(perm[i:] + perm[:i]) for i in range(n)),
            min(tuple(perm[::-1][i:] + perm[::-1][:i]) for i in range(n))
        )
        if canonical not in seen:
            seen.add(canonical)
            results.append(list(perm))
    return results

def sub_threshold_3binary(n):
    """All sorted multisets with exactly 3 binary, product < threshold."""
    threshold = 4 * 3**(n-2)
    results = set()
    nn = n - 3  # number of non-binary
    bp = 2**3  # = 8
    budget = threshold // bp  # non-binary product must be < budget

    def gen(k, bud, cur, lo):
        if k == 0:
            ms = tuple(sorted([2]*3 + list(cur)))
            if prod(ms) < threshold:
                results.add(ms)
            return
        for m in range(lo, min(bud+1, 30)):
            if m**k > bud:
                break
            gen(k-1, bud // m, cur + (m,), m)

    gen(nn, budget - 1, (), 3)
    return sorted(results)


if __name__ == '__main__':
    n = 9
    threshold = 4 * 3**(n-2)
    print(f"RA14 v5: 3-binary focus at n={n}")
    print(f"Threshold: {threshold}")
    print()

    multisets = sub_threshold_3binary(n)
    print(f"3-binary sub-threshold multiset types: {len(multisets)}")
    for ms in multisets[:20]:
        print(f"  {list(ms)}, product={prod(ms)}")
    if len(multisets) > 20:
        print(f"  ... ({len(multisets) - 20} more)")
    print()

    total_cycles = 0
    total_sweep = 0
    total_nonsweep_ec = 0
    total_nonsweep_noec = 0
    counterexamples = []

    t0 = time.time()

    for ms_sorted in multisets:
        p_val = prod(ms_sorted)
        placements = all_placements_fast(tuple(ms_sorted), n)

        ms_sw = 0
        ms_nec = 0
        ms_nnoec = 0
        ms_cx = []

        for ms in placements:
            bp = [i for i in range(n) if ms[i] == 2]
            if len(bp) != 3:
                continue

            words = generate_words(n, ms)
            cycles_this = []
            seen = set()

            for w_tuple in words:
                w = list(w_tuple)
                for cyc in try_trans(w, ms, n):
                    key = frozenset(cyc)
                    if key not in seen:
                        seen.add(key)
                        cycles_this.append((cyc, w))

            for cyc, w in cycles_this:
                total_cycles += 1
                if is_uniform_sweep(w, n):
                    total_sweep += 1
                    ms_sw += 1
                else:
                    if check_ec(cyc, w, n):
                        total_nonsweep_ec += 1
                        ms_nec += 1
                    else:
                        total_nonsweep_noec += 1
                        ms_nnoec += 1
                        fc = Counter(w)
                        bp_s = sorted(bp)
                        gaps = [(bp_s[(i+1)%3] - bp_s[i]) % n for i in range(3)]
                        ms_cx.append({
                            'ms': list(ms), 'gaps': gaps,
                            'CL': len(w), 'fc': tuple(fc.get(p,0) for p in range(n)),
                            'word': w, 'cycle': cyc,
                        })

        if ms_sw + ms_nec + ms_nnoec > 0:
            print(f"ms={list(ms_sorted)}, p={p_val}: sweep={ms_sw}, nswp_EC={ms_nec}, nswp_noEC={ms_nnoec}")

        counterexamples.extend(ms_cx)

    elapsed = time.time() - t0
    print()
    print("=" * 70)
    print(f"3-BINARY SUMMARY (n={n}, {elapsed:.1f}s)")
    print("=" * 70)
    print(f"Total cycles: {total_cycles}")
    print(f"  Sweep: {total_sweep}")
    print(f"  Non-sweep with EC: {total_nonsweep_ec}")
    print(f"  Non-sweep WITHOUT EC: {total_nonsweep_noec}")

    if counterexamples:
        print(f"\nCOUNTEREXAMPLES ({len(counterexamples)}):")
        for cx in counterexamples[:10]:
            print(f"  ms={cx['ms']}, CL={cx['CL']}, fc={cx['fc']}, gaps={cx['gaps']}")
    else:
        print(f"\nNO COUNTEREXAMPLES! Every non-sweep 3-binary cycle at n=9 has EC.")

    # Now also check 4-binary and 5-binary
    for num_b in [4, 5, 6]:
        print(f"\n--- Checking {num_b}-binary ---")
        # Quick check: enumerate multisets
        results = set()
        nn = n - num_b
        bp_val = 2**num_b
        budget = threshold // bp_val

        def gen2(k, bud, cur, lo):
            if k == 0:
                ms = tuple(sorted([2]*num_b + list(cur)))
                if prod(ms) < threshold:
                    results.add(ms)
                return
            for m in range(lo, min(bud+1, 30)):
                if m**k > bud:
                    break
                gen2(k-1, bud // m, cur + (m,), m)
        gen2(nn, budget - 1, (), 3)

        nb_cycles = 0
        nb_sweep = 0
        nb_nec = 0
        nb_nnoec = 0

        for ms_sorted in sorted(results):
            p_val = prod(ms_sorted)
            placements = all_placements_fast(tuple(ms_sorted), n)
            for ms in placements:
                bp = [i for i in range(n) if ms[i] == 2]
                if len(bp) != num_b:
                    continue
                words = generate_words(n, ms)
                seen = set()
                for w_tuple in words:
                    w = list(w_tuple)
                    for cyc in try_trans(w, ms, n):
                        key = frozenset(cyc)
                        if key not in seen:
                            seen.add(key)
                            nb_cycles += 1
                            if is_uniform_sweep(w, n):
                                nb_sweep += 1
                            elif check_ec(cyc, w, n):
                                nb_nec += 1
                            else:
                                nb_nnoec += 1

        print(f"  {num_b}-binary: {nb_cycles} cycles, sweep={nb_sweep}, nswp_EC={nb_nec}, nswp_noEC={nb_nnoec}")

    print()
    print("KEY FINDING:")
    if total_nonsweep_noec == 0:
        print("For 3-binary at n=9: EVERY non-sweep cycle has EC.")
        print("The WaterfallCycle/EC dichotomy HOLDS for the relevant case (>=3 binary means >=3,")
        print("but the counting lemma only guarantees >=3, not exactly 3).")
        print("Need to check at what binary count the dichotomy breaks.")
    else:
        print(f"For 3-binary at n=9: {total_nonsweep_noec} non-sweep non-EC cycles exist.")
