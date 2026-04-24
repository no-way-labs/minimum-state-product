#!/usr/bin/env python3
"""
RA14 v4: Deep analysis of non-sweep non-EC cycles at n=9.

Key questions:
1. Which pure {2,3} multisets produce non-sweep non-EC cycles?
2. What is the shadow status of ALL such cycles (exhaustive)?
3. Is there a broader classification that captures ALL non-EC cycles?
4. For non-EC non-shadow cycles: what blocks them? (entry conflict at system level?)
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


def count_ec_procs(good, word, n):
    """Return set of procs with entry conflict."""
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
    ec_procs = set()
    for j in range(n):
        if mover_triples[j] & nonmover_triples[j]:
            ec_procs.add(j)
    return ec_procs


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
            results.append((cyc, tm))
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


def enumerate_dfs(ms, n, max_cycles=5000, max_time=30.0):
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


def check_shadow_exhaustive(good, word, n, ms):
    """Exhaustive shadow check with both inc and dec."""
    L = len(word)
    orig_set = set(good)
    p_val = prod(ms)
    if p_val > 10000:
        return None

    for delta in [1, -1]:
        for s in iproduct(*(range(m) for m in ms)):
            s = tuple(s)
            if s in orig_set:
                continue
            configs = [list(s)]
            for t in range(L):
                c = list(configs[-1])
                p = word[t]
                c[p] = (c[p] + delta) % ms[p]
                configs.append(c)
            if configs[-1] != list(configs[0]):
                continue
            cs = set(tuple(c) for c in configs[:L])
            if len(cs) != L or cs & orig_set:
                continue
            return True
    return False


def check_shadow_any_trans(good, word, n, ms):
    """Shadow check trying all transition modes for shadow."""
    L = len(word)
    orig_set = set(good)
    p_val = prod(ms)
    if p_val > 10000:
        return None

    non_binary = [p for p in range(n) if ms[p] > 2]
    binary = [p for p in range(n) if ms[p] == 2]

    # For shadow, try different trans modes
    if len(non_binary) <= 6:
        combos = list(iproduct([1, -1], repeat=len(non_binary)))
    else:
        combos = [(1,)*len(non_binary), (-1,)*len(non_binary)]

    for combo in combos:
        tm = {}
        for p in binary:
            tm[p] = 1
        for idx, p in enumerate(non_binary):
            tm[p] = combo[idx]

        for s in iproduct(*(range(m) for m in ms)):
            s = tuple(s)
            if s in orig_set:
                continue
            configs = [list(s)]
            for t in range(L):
                c = list(configs[-1])
                p = word[t]
                c[p] = (c[p] + tm[p]) % ms[p]
                configs.append(c)
            if configs[-1] != list(configs[0]):
                continue
            cs = set(tuple(c) for c in configs[:L])
            if len(cs) != L or cs & orig_set:
                continue
            return True
    return False


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
    print(f"RA14 v4: Deep analysis of non-sweep non-EC cycles")
    print(f"n={n}, threshold={threshold}")
    print()

    # Focus on pure {2,3} multisets
    pure23 = []
    for nb in range(3, 10):
        nn = n - nb
        ms = tuple(sorted([2]*nb + [3]*nn))
        if prod(ms) < threshold:
            pure23.append(ms)

    print("Pure {2,3} multisets:")
    for ms in pure23:
        print(f"  {list(ms)}, product={prod(ms)}, binary={ms.count(2)}")
    print()

    all_noec_nonsweep = []

    for ms_sorted in pure23:
        p_val = prod(ms_sorted)
        placements = all_placements_fast(tuple(ms_sorted), n)
        print(f"\n--- Multiset {list(ms_sorted)}, product={p_val}, {len(placements)} placements ---")

        for ms in placements:
            binary_pos = [i for i in range(n) if ms[i] == 2]
            bp_s = sorted(binary_pos)
            gaps = [(bp_s[(i+1) % len(bp_s)] - bp_s[i]) % n for i in range(len(bp_s))]

            words = generate_words(n, ms)
            cycles_this = []
            seen = set()

            for w_tuple in words:
                w = list(w_tuple)
                for cyc, tm in try_trans(w, ms, n):
                    key = frozenset(cyc)
                    if key not in seen:
                        seen.add(key)
                        cycles_this.append((cyc, w, tm))

            if p_val <= 1500:
                dfs_res = enumerate_dfs(ms, n, max_cycles=5000, max_time=30.0)
                for cyc, w in dfs_res:
                    key = frozenset(tuple(c) for c in cyc)
                    if key not in seen:
                        seen.add(key)
                        cycles_this.append((cyc, w, None))

            sweep_count = 0
            nonsweep_ec = 0
            nonsweep_noec = 0
            noec_list = []

            for cyc, w, tm in cycles_this:
                if is_uniform_sweep(w, n):
                    sweep_count += 1
                else:
                    if check_ec(cyc, w, n):
                        nonsweep_ec += 1
                    else:
                        nonsweep_noec += 1
                        fc = Counter(w)
                        noec_list.append({
                            'ms': list(ms),
                            'binary_pos': binary_pos,
                            'gaps': gaps,
                            'CL': len(w),
                            'fc': tuple(fc.get(p, 0) for p in range(n)),
                            'word': w,
                            'cycle': cyc,
                            'tm': tm,
                        })

            if cycles_this:
                print(f"  ms={ms}, gaps={gaps}: sweep={sweep_count}, nswp_EC={nonsweep_ec}, nswp_noEC={nonsweep_noec}")

            all_noec_nonsweep.extend(noec_list)

    print()
    print("=" * 70)
    print(f"PURE {{2,3}} NON-SWEEP NON-EC CYCLES: {len(all_noec_nonsweep)}")
    print("=" * 70)

    if not all_noec_nonsweep:
        print("NONE! Every non-sweep cycle in pure {2,3} has EC.")
        sys.exit(0)

    # Group by multiset
    by_ms = defaultdict(list)
    for cx in all_noec_nonsweep:
        by_ms[tuple(sorted(cx['ms']))].append(cx)

    for ms_key, cxs in sorted(by_ms.items()):
        print(f"\n  Multiset {list(ms_key)}: {len(cxs)} non-EC non-sweep cycles")

        # Group by gap pattern
        by_gap = defaultdict(list)
        for cx in cxs:
            by_gap[tuple(sorted(cx['gaps']))].append(cx)

        for gp, gcxs in sorted(by_gap.items()):
            all_odd = all(g % 2 == 1 for g in gp)
            print(f"    Gaps (sorted) {list(gp)}: {len(gcxs)} cycles, all_odd={all_odd}")

    # Exhaustive shadow check
    print()
    print("EXHAUSTIVE SHADOW CHECK:")
    shadow_yes = 0
    shadow_no = 0
    shadow_unk = 0

    for i, cx in enumerate(all_noec_nonsweep):
        sh = check_shadow_any_trans(cx['cycle'], cx['word'], n, cx['ms'])
        if sh is True:
            shadow_yes += 1
        elif sh is False:
            shadow_no += 1
        else:
            shadow_unk += 1

        if i < 20 or (sh is False and shadow_no <= 10):
            print(f"  [{i}] ms={cx['ms']}, CL={cx['CL']}, fc={cx['fc'][:5]}..., shadow={sh}")

    print()
    print(f"Shadow results: YES={shadow_yes}, NO={shadow_no}, unknown={shadow_unk}")
    print(f"  (of {len(all_noec_nonsweep)} total)")

    if shadow_no > 0:
        print()
        print("NON-EC NON-SHADOW CYCLES (most dangerous):")
        for i, cx in enumerate(all_noec_nonsweep):
            sh = check_shadow_any_trans(cx['cycle'], cx['word'], n, cx['ms'])
            if sh is False:
                ec_procs = count_ec_procs(cx['cycle'], cx['word'], n)
                print(f"  ms={cx['ms']}, CL={cx['CL']}, fc={cx['fc']}, gaps={cx['gaps']}")
                print(f"    EC procs: {ec_procs} ({len(ec_procs)} of {n})")
                if i > 20:
                    break
