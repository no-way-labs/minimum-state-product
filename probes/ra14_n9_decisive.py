#!/usr/bin/env python3
"""
RA14 v2: Decisive n=9 test ONLY.

Does every non-WaterfallCycle sub-threshold good cycle with n=9 and >=3 binary
have entry conflict?

Key multisets at n=9 (threshold = 4*3^7 = 8748):
  Pure {2,3}: 3 binary = product 2916, 4 binary = 1944, 5 binary = 1296,
              6 binary = 864, 7 binary = 576, 8 binary = 384, 9 binary = 512 (all binary)
  Mixed with 4: e.g. {2^3, 3^5, 4} = 7776, {2^4, 3^4, 4} = 5184, etc.

Strategy: construct cycles via word+transition enumeration, then DFS for small products.
"""

import sys
import time
from collections import Counter, defaultdict
from itertools import product as iproduct, combinations, permutations
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


def is_waterfall_cycle(word, n):
    """WaterfallCycle: CL=2n, uniform sweep, each proc fires exactly 2."""
    L = len(word)
    if L != 2 * n:
        return False
    fc = Counter(word)
    if any(fc.get(p, 0) != 2 for p in range(n)):
        return False
    return is_uniform_sweep(word, n)


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


def try_trans_modes(word, ms, n, max_combos=256):
    """Try transition modes. Return list of valid (configs, word)."""
    results = []
    non_binary = [p for p in range(n) if ms[p] > 2]
    binary = [p for p in range(n) if ms[p] == 2]

    if len(non_binary) > 8:
        combos = list(iproduct([1, -1], repeat=len(non_binary)))[:max_combos]
    else:
        combos = list(iproduct([1, -1], repeat=len(non_binary)))

    for combo in combos:
        tm = {p: 1 for p in binary}
        for idx, p in enumerate(non_binary):
            tm[p] = combo[idx]
        # Check fire count compatibility
        ok = True
        fc = Counter(word)
        for p in range(n):
            fires = fc.get(p, 0)
            if fires == 0:
                ok = False
                break
            if (fires * tm[p]) % ms[p] != 0:
                ok = False
                break
        if not ok:
            continue
        cyc = build_cycle_trans(word, ms, n, tm)
        if cyc:
            results.append(cyc)
    return results


def generate_sweep_words_n9(n):
    """Generate all uniform sweep mover words that could close."""
    words = []
    for start in range(n):
        for direction in [1, -1]:
            sweep = [(start + direction * i) % n for i in range(n)]
            for reps in range(2, 7):  # reps=2 is CL=2n WaterfallCycle candidate
                words.append(sweep * reps)
    return words


def generate_bounce_words_n9(n):
    """Bounce: fwd then back."""
    words = []
    for start in range(n):
        for direction in [1, -1]:
            fwd = [(start + direction * i) % n for i in range(n)]
            bwd = list(reversed(fwd[1:-1]))
            bounce = fwd + bwd
            for reps in range(1, 4):
                w = bounce * reps
                if len(w) <= 5 * n:
                    words.append(w)
    return words


def generate_mixed_sweep_bounce(n):
    """Mixed: one sweep then partial bounce."""
    words = []
    for start in range(n):
        for d in [1, -1]:
            sweep = [(start + d * i) % n for i in range(n)]
            # Sweep + reverse sweep
            w = sweep + list(reversed(sweep))
            words.append(w)
            # 1.5 sweeps (3n)
            w15 = sweep + sweep + list(reversed(sweep[1:-1]))
            if len(w15) <= 5 * n:
                words.append(w15)
    return words


def enumerate_dfs(ms, n, max_cycles=2000, max_time=20.0):
    """DFS enumeration from all-zero."""
    t0 = time.time()
    p = prod(ms)
    if p > 2000:
        return []

    start = tuple([0]*n)
    results = []
    seen = set()
    max_len = min(4 * n, p)

    def dfs(config, path, word, det):
        if time.time() - t0 > max_time or len(results) >= max_cycles:
            return
        for p_idx in range(n):
            for nv in range(ms[p_idx]):
                if nv == config[p_idx]:
                    continue
                if word:
                    last = word[-1]
                    diff = min(abs(p_idx - last), n - abs(p_idx - last))
                    if diff > 1:
                        continue
                L_v = config[(p_idx-1) % n]
                S_v = config[p_idx]
                R_v = config[(p_idx+1) % n]
                km = (p_idx, L_v, S_v, R_v)
                nd = dict(det)
                if km in nd:
                    if nd[km] != nv:
                        continue
                else:
                    nd[km] = nv
                ok = True
                for i in range(n):
                    if i == p_idx:
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
                nc[p_idx] = nv
                nc = tuple(nc)
                nw = word + [p_idx]
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


def check_shadow(good, word, n, ms, max_starts=5000):
    """Check shadow existence by sampling starts."""
    L = len(word)
    orig_set = set(good)
    p_val = prod(ms)

    if p_val <= 10000:
        # Exhaustive
        starts = list(iproduct(*(range(m) for m in ms)))
    else:
        import random
        random.seed(42)
        starts = [tuple(random.randint(0, ms[i]-1) for i in range(n)) for _ in range(max_starts)]

    for s in starts:
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
    """All sorted multisets with >=3 binary, product < 8748, n=9."""
    n = 9
    threshold = 8748
    results = []

    for nb in range(3, 10):  # number of binary
        nn = n - nb
        bp = 2**nb
        if bp >= threshold:
            continue
        budget = threshold // bp  # non-binary product must be < budget

        if nn == 0:
            results.append(tuple(sorted([2]*9)))
            continue

        # Enumerate non-binary values (each >= 3)
        def gen(k, bud, cur):
            if k == 0:
                ms = sorted([2]*nb + list(cur))
                if prod(ms) < threshold:
                    results.append(tuple(ms))
                return
            lo = cur[-1] if cur else 3
            for m in range(lo, min(bud+1, 20)):
                if m**k > bud:
                    break
                gen(k-1, bud // m, cur + [m])

        gen(nn, budget - 1, [])

    # Deduplicate
    return sorted(set(results))


def all_placements_fast(ms_sorted, n):
    """All distinct ring placements (up to rotation+reflection)."""
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


# =========================================================================
# MAIN
# =========================================================================

if __name__ == '__main__':
    n = 9
    threshold = 4 * 3**(n-2)
    print(f"RA14 v2: Decisive n={n} test")
    print(f"Threshold: {threshold}")
    print()

    multisets = sub_threshold_multisets_n9()
    print(f"Sub-threshold multiset types: {len(multisets)}")
    for ms_s in multisets:
        print(f"  {list(ms_s)}, product={prod(ms_s)}")
    print()

    total_cycles = 0
    total_wf = 0
    total_nonwf_ec = 0
    total_nonwf_noec = 0
    counterexamples = []

    t0_global = time.time()

    for ms_sorted in multisets:
        p_val = prod(ms_sorted)
        placements = all_placements_fast(tuple(ms_sorted), n)
        print(f"\nMultiset {list(ms_sorted)}, product={p_val}, placements={len(placements)}")

        for ms in placements:
            binary_pos = [i for i in range(n) if ms[i] == 2]
            gaps = []
            bp_s = sorted(binary_pos)
            for i in range(len(bp_s)):
                nxt = bp_s[(i+1) % len(bp_s)]
                cur = bp_s[i]
                gaps.append((nxt - cur) % n)

            # Generate words
            all_words = set()

            # Sweeps
            for w in generate_sweep_words_n9(n):
                fc = Counter(w)
                ok = all(fc.get(p, 0) > 0 for p in range(n))
                if ok:
                    all_words.add(tuple(w))

            # Bounces
            for w in generate_bounce_words_n9(n):
                fc = Counter(w)
                ok = all(fc.get(p, 0) > 0 for p in range(n))
                if ok:
                    all_words.add(tuple(w))

            # Mixed
            for w in generate_mixed_sweep_bounce(n):
                fc = Counter(w)
                ok = all(fc.get(p, 0) > 0 for p in range(n))
                if ok and len(w) <= 5*n:
                    all_words.add(tuple(w))

            cycles_this = []
            seen = set()

            for w_tuple in all_words:
                w = list(w_tuple)
                for cyc in try_trans_modes(w, ms, n, max_combos=256):
                    key = frozenset(cyc)
                    if key not in seen:
                        seen.add(key)
                        cycles_this.append((cyc, w))

            # DFS for small products
            if p_val <= 1500:
                dfs_t = 15.0
                dfs_res = enumerate_dfs(ms, n, max_cycles=2000, max_time=dfs_t)
                for cyc, w in dfs_res:
                    key = frozenset(tuple(c) for c in cyc)
                    if key not in seen:
                        seen.add(key)
                        cycles_this.append((cyc, w))

            wf = 0
            nwf_ec = 0
            nwf_noec = 0

            for cyc, w in cycles_this:
                total_cycles += 1
                if is_waterfall_cycle(w, n):
                    wf += 1
                    total_wf += 1
                else:
                    if check_ec(cyc, w, n):
                        nwf_ec += 1
                        total_nonwf_ec += 1
                    else:
                        nwf_noec += 1
                        total_nonwf_noec += 1
                        fc = Counter(w)
                        fc_tuple = tuple(fc.get(p, 0) for p in range(n))
                        counterexamples.append({
                            'ms': list(ms),
                            'binary_pos': binary_pos,
                            'gaps': gaps,
                            'CL': len(w),
                            'fc': fc_tuple,
                            'word': w,
                            'cycle': cyc,
                        })

            if cycles_this:
                print(f"  ms={ms}, gaps={gaps}: {len(cycles_this)} cycles (WF={wf}, nwf_EC={nwf_ec}, nwf_noEC={nwf_noec})")

    elapsed = time.time() - t0_global
    print()
    print("=" * 70)
    print(f"SUMMARY n={n} (elapsed {elapsed:.1f}s)")
    print("=" * 70)
    print(f"Total cycles: {total_cycles}")
    print(f"  WaterfallCycles: {total_wf}")
    print(f"  Non-WF with EC: {total_nonwf_ec}")
    print(f"  Non-WF without EC: {total_nonwf_noec}")
    print()

    if counterexamples:
        print(f"COUNTEREXAMPLES: {len(counterexamples)}")
        # Group by type
        by_type = defaultdict(list)
        for cx in counterexamples:
            key = (tuple(sorted(cx['ms'])), tuple(sorted(cx['gaps'])))
            by_type[key].append(cx)

        for (ms_key, gaps_key), cxs in sorted(by_type.items()):
            print(f"\n  Multiset {list(ms_key)}, gap pattern {list(gaps_key)}: {len(cxs)} cycles")
            for cx in cxs[:3]:
                print(f"    ms={cx['ms']}, CL={cx['CL']}, fc={cx['fc']}")
                # Check all gaps odd
                all_odd = all(g % 2 == 1 for g in cx['gaps'])
                print(f"    gaps={cx['gaps']}, all_odd={all_odd}")

        # Shadow check on counterexamples
        print()
        print("Shadow check on counterexamples:")
        shadow_yes = 0
        shadow_no = 0
        shadow_unk = 0
        for i, cx in enumerate(counterexamples[:30]):
            sh = check_shadow(cx['cycle'], cx['word'], n, cx['ms'])
            status = "YES" if sh else "NO/unknown"
            if sh:
                shadow_yes += 1
            else:
                shadow_no += 1
            if i < 10:
                print(f"  [{i}] ms={cx['ms']}, CL={cx['CL']}, shadow={status}")
        print(f"\n  Shadow: YES={shadow_yes}, NO={shadow_no} (of {min(30, len(counterexamples))} checked)")
    else:
        print("NO COUNTEREXAMPLES!")

    print()
    if total_nonwf_noec == 0:
        print("THE ANSWER: YES — every non-WaterfallCycle has EC at n=9.")
    else:
        print("THE ANSWER: NO — there exist non-WaterfallCycle non-EC cycles at n=9.")
        print(f"  Count: {total_nonwf_noec}")
        # Characterize
        all_odd_count = sum(1 for cx in counterexamples if all(g % 2 == 1 for g in cx['gaps']))
        print(f"  All-odd-gap: {all_odd_count}/{len(counterexamples)}")
        even_gap_count = len(counterexamples) - all_odd_count
        print(f"  Has-even-gap: {even_gap_count}/{len(counterexamples)}")
