#!/usr/bin/env python3
"""
RA14 v3: Refined n=9 analysis.

Classifies cycles into:
  1. Uniform sweep (any rep count, CW or CCW) — includes WaterfallCycle (CL=2n)
  2. Non-uniform-sweep with EC
  3. Non-uniform-sweep WITHOUT EC (the true counterexamples)

For class 3: characterize structure + check shadow.
"""

import sys
import time
from collections import Counter, defaultdict
from itertools import product as iproduct, permutations
from math import prod

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
    for j in range(n):
        if mover_triples[j] & nonmover_triples[j]:
            return True
    return False


def is_uniform_sweep(word, n):
    """Check if word is ANY cyclic rotation of a uniform k-rep sweep."""
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


def classify_word(word, n):
    """Classify mover word."""
    if is_uniform_sweep(word, n):
        reps = len(word) // n
        return f"sweep_{reps}rep"

    # Check if it's a bounce
    fc = Counter(word)
    fcs = sorted(set(fc.values()))

    # Detect direction changes
    dirs = []
    for i in range(len(word) - 1):
        d = (word[i+1] - word[i]) % n
        if d == 1:
            dirs.append('+')
        elif d == n - 1:
            dirs.append('-')
        else:
            dirs.append('?')
    dir_str = ''.join(dirs)

    changes = sum(1 for i in range(len(dirs)-1) if dirs[i] != dirs[i+1])

    return f"CL={len(word)}_fc={fcs}_chg={changes}"


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
    config_set = set(tuple(c) for c in configs[:L])
    if len(config_set) != L:
        return None
    return [tuple(c) for c in configs[:L]]


def try_trans(word, ms, n, max_combos=256):
    results = []
    non_binary = [p for p in range(n) if ms[p] > 2]
    binary = [p for p in range(n) if ms[p] == 2]
    combos = list(iproduct([1, -1], repeat=len(non_binary)))[:max_combos]
    for combo in combos:
        tm = {p: 1 for p in binary}
        for idx, p in enumerate(non_binary):
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
    """Generate candidate mover words."""
    words = set()
    # Sweeps (2..6 reps)
    for start in range(n):
        for d in [1, -1]:
            sweep = [(start + d * i) % n for i in range(n)]
            for reps in range(2, 7):
                w = tuple(sweep * reps)
                fc = Counter(w)
                if all(fc.get(p, 0) > 0 for p in range(n)):
                    words.add(w)

    # Bounces
    for start in range(n):
        for d in [1, -1]:
            fwd = [(start + d * i) % n for i in range(n)]
            bwd = list(reversed(fwd[1:-1]))
            bounce = fwd + bwd
            for reps in range(1, 4):
                w = tuple(bounce * reps)
                fc = Counter(w)
                if all(fc.get(p, 0) > 0 for p in range(n)) and len(w) <= 5*n:
                    words.add(w)

    # Mixed sweep+reverse
    for start in range(n):
        for d in [1, -1]:
            sweep = [(start + d * i) % n for i in range(n)]
            w = tuple(sweep + list(reversed(sweep)))
            fc = Counter(w)
            if all(fc.get(p, 0) > 0 for p in range(n)):
                words.add(w)

    return list(words)


def enumerate_dfs(ms, n, max_cycles=2000, max_time=15.0):
    t0 = time.time()
    if prod(ms) > 2000:
        return []
    start = tuple([0]*n)
    results = []
    seen = set()
    max_len = min(4*n, prod(ms))

    def dfs(config, path, word, det):
        if time.time() - t0 > max_time or len(results) >= max_cycles:
            return
        for p in range(n):
            for nv in range(ms[p]):
                if nv == config[p]:
                    continue
                if word:
                    last = word[-1]
                    diff = min(abs(p - last), n - abs(p - last))
                    if diff > 1:
                        continue
                Lv = config[(p-1) % n]
                Sv = config[p]
                Rv = config[(p+1) % n]
                km = (p, Lv, Sv, Rv)
                nd = dict(det)
                if km in nd:
                    if nd[km] != nv:
                        continue
                else:
                    nd[km] = nv
                ok = True
                for i in range(n):
                    if i == p:
                        continue
                    ki = (i, config[(i-1)%n], config[i], config[(i+1)%n])
                    if ki in nd:
                        if nd[ki] != config[i]:
                            ok = False
                            break
                    else:
                        nd[ki] = config[i]
                if not ok:
                    continue
                nc = list(config)
                nc[p] = nv
                nc = tuple(nc)
                nw = word + [p]
                if nc == start and len(path) >= 2*n:
                    fc = Counter(nw)
                    if len(fc) == n:
                        ck = frozenset(path)
                        if ck not in seen:
                            seen.add(ck)
                            results.append((list(path), nw))
                    continue
                if nc not in set(path) and len(path) < max_len:
                    path.append(nc)
                    dfs(nc, path, nw, nd)
                    path.pop()
    dfs(start, [start], [], {})
    return results


def check_shadow(good, word, n, ms):
    L = len(word)
    orig_set = set(good)
    p_val = prod(ms)
    if p_val > 10000:
        return None
    for s in iproduct(*(range(m) for m in ms)):
        s = tuple(s)
        if s in orig_set:
            continue
        configs = [list(s)]
        for t in range(L):
            c = list(configs[-1])
            p = word[t]
            c[p] = (c[p] + 1) % ms[p]
            configs.append(c)
        if configs[-1] != list(configs[0]):
            continue
        cs = set(tuple(c) for c in configs[:L])
        if len(cs) != L or cs & orig_set:
            continue
        return True
    return False


def sub_threshold_multisets_n9():
    n = 9
    threshold = 8748
    results = set()
    for nb in range(3, 10):
        nn = n - nb
        bp = 2**nb
        if bp >= threshold:
            continue
        if nn == 0:
            results.add(tuple(sorted([2]*9)))
            continue
        budget = threshold // bp
        def gen(k, bud, cur, lo):
            if k == 0:
                ms = tuple(sorted([2]*nb + list(cur)))
                if prod(ms) < threshold:
                    results.add(ms)
                return
            for m in range(lo, min(bud+1, 20)):
                if m**k > bud:
                    break
                gen(k-1, bud // m, cur + (m,), m)
        gen(nn, budget - 1, (), 3)
    return sorted(results)


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


if __name__ == '__main__':
    n = 9
    threshold = 4 * 3**(n-2)
    print(f"RA14 v3: Refined n={n} analysis")
    print(f"Threshold: {threshold}")
    print()

    multisets = sub_threshold_multisets_n9()
    print(f"Sub-threshold multiset types: {len(multisets)}")

    # Focus on pure {2,3} multisets first (most relevant for the theorem)
    pure_23 = [ms for ms in multisets if all(m in [2,3] for m in ms)]
    print(f"Pure {{2,3}} multisets: {len(pure_23)}")
    for ms in pure_23:
        print(f"  {list(ms)}, product={prod(ms)}")
    print()

    total_cycles = 0
    sweep_cycles = 0
    nonsweep_ec = 0
    nonsweep_noec = 0
    counterexamples = []

    t0 = time.time()

    # Test ALL multisets but report details
    for ms_sorted in multisets:
        p_val = prod(ms_sorted)
        placements = all_placements_fast(tuple(ms_sorted), n)

        ms_sweep = 0
        ms_nswp_ec = 0
        ms_nswp_noec = 0
        ms_cx = []

        for ms in placements:
            binary_pos = [i for i in range(n) if ms[i] == 2]
            if len(binary_pos) < 3:
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

            if p_val <= 1500:
                dfs_res = enumerate_dfs(ms, n, max_cycles=2000, max_time=10.0)
                for cyc, w in dfs_res:
                    key = frozenset(tuple(c) for c in cyc)
                    if key not in seen:
                        seen.add(key)
                        cycles_this.append((cyc, w))

            for cyc, w in cycles_this:
                total_cycles += 1
                if is_uniform_sweep(w, n):
                    sweep_cycles += 1
                    ms_sweep += 1
                else:
                    if check_ec(cyc, w, n):
                        nonsweep_ec += 1
                        ms_nswp_ec += 1
                    else:
                        nonsweep_noec += 1
                        ms_nswp_noec += 1
                        fc = Counter(w)
                        bp_s = sorted(binary_pos)
                        gaps = [(bp_s[(i+1) % len(bp_s)] - bp_s[i]) % n for i in range(len(bp_s))]
                        ms_cx.append({
                            'ms': list(ms),
                            'binary_pos': binary_pos,
                            'gaps': gaps,
                            'CL': len(w),
                            'fc': tuple(fc.get(p, 0) for p in range(n)),
                            'word': w,
                            'cycle': cyc,
                            'type': classify_word(w, n),
                        })

        if ms_sweep + ms_nswp_ec + ms_nswp_noec > 0:
            pure23 = all(m in [2,3] for m in ms_sorted)
            tag = " [PURE 2,3]" if pure23 else ""
            print(f"ms={list(ms_sorted)}, p={p_val}{tag}: sweep={ms_sweep}, nswp_EC={ms_nswp_ec}, nswp_noEC={ms_nswp_noec}")

        counterexamples.extend(ms_cx)

    elapsed = time.time() - t0
    print()
    print("=" * 70)
    print(f"SUMMARY (n={n}, {elapsed:.1f}s)")
    print("=" * 70)
    print(f"Total cycles: {total_cycles}")
    print(f"  Uniform sweep (any rep): {sweep_cycles}")
    print(f"  Non-sweep with EC: {nonsweep_ec}")
    print(f"  Non-sweep WITHOUT EC: {nonsweep_noec}")
    print()

    if counterexamples:
        # Analyze counterexamples
        pure23_cx = [cx for cx in counterexamples if all(m in [2,3] for m in cx['ms'])]
        print(f"Counterexamples from pure {{2,3}} multisets: {len(pure23_cx)}")

        # Group by CL and type
        by_type = defaultdict(int)
        for cx in counterexamples:
            by_type[cx['type']] += 1
        print(f"\nCounterexample types:")
        for t, cnt in sorted(by_type.items(), key=lambda x: -x[1]):
            print(f"  {t}: {cnt}")

        # Gap analysis
        all_odd = sum(1 for cx in counterexamples if all(g % 2 == 1 for g in cx['gaps']))
        has_even = len(counterexamples) - all_odd
        print(f"\nGap parity: all-odd={all_odd}, has-even={has_even}")

        # Pure 2,3 details
        if pure23_cx:
            print(f"\nPure {{2,3}} counterexamples ({len(pure23_cx)}):")
            for cx in pure23_cx[:10]:
                print(f"  ms={cx['ms']}, CL={cx['CL']}, fc={cx['fc']}, type={cx['type']}")
                print(f"    gaps={cx['gaps']}, all_odd={all(g%2==1 for g in cx['gaps'])}")

            # Shadow check for pure {2,3}
            print(f"\nShadow check for pure {{2,3}} counterexamples:")
            for i, cx in enumerate(pure23_cx[:15]):
                sh = check_shadow(cx['cycle'], cx['word'], n, cx['ms'])
                print(f"  [{i}] ms={cx['ms']}, CL={cx['CL']}: shadow={sh}")

        # Sample non-pure counterexamples
        non_pure_cx = [cx for cx in counterexamples if not all(m in [2,3] for m in cx['ms'])]
        if non_pure_cx:
            print(f"\nNon-pure counterexamples: {len(non_pure_cx)}")
            # Shadow check
            print("Shadow check (sample):")
            checked = 0
            sh_yes = 0
            for cx in non_pure_cx[:20]:
                sh = check_shadow(cx['cycle'], cx['word'], n, cx['ms'])
                if sh is not None:
                    checked += 1
                    if sh:
                        sh_yes += 1
                    if checked <= 5:
                        print(f"  ms={cx['ms']}, CL={cx['CL']}: shadow={sh}")
            print(f"  Shadow: {sh_yes}/{checked} YES")

    else:
        print("NO counterexamples — every non-sweep cycle has EC!")

    print()
    if nonsweep_noec == 0:
        print("THE ANSWER: YES — every non-uniform-sweep has EC at n=9.")
    else:
        print(f"THE ANSWER: NO — {nonsweep_noec} non-sweep non-EC cycles at n=9.")
