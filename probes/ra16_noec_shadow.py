#!/usr/bin/env python3
"""
RA16b: For sweep non-consecutive cycles WITHOUT entry conflict,
investigate shadow cycle obstruction.

From RA16a: n=7 has 64 no-EC cycles (ms=[2,2,3,3,2,3,3]),
            n=9 has 1536 no-EC cycles.

Key questions:
1. Do these cycles have shadow cycles (MNU + disjointness)?
2. What structural property prevents EC? (What makes them different from
   the alternating-ring cycles that DO have EC?)
3. Can we prove the shifted-config-is-non-good WITHOUT H-1 Uniqueness?
"""
from itertools import combinations
from collections import Counter, defaultdict
import time


def total_displacement(word, n):
    disp = 0
    L = len(word)
    for i in range(L):
        nxt = word[(i + 1) % L]
        cur = word[i]
        diff = (nxt - cur) % n
        if diff == 1:
            disp += 1
        elif diff == n - 1:
            disp -= 1
        else:
            return None
    return disp


def has_3_consecutive_binary(ms):
    n = len(ms)
    for i in range(n):
        if ms[i] == 2 and ms[(i+1)%n] == 2 and ms[(i+2)%n] == 2:
            return True
    return False


def enumerate_words_dfs(n, ms, max_len, max_results=50000, timeout=120):
    target_cl = sum(ms)
    results = []
    t0 = time.time()
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

    def dfs(word, fc):
        if time.time() - t0 > timeout:
            return
        if len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == ms[p] for p in range(n)):
                diff = (word[0] - word[-1]) % n
                if diff in (1, n-1):
                    results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            if fc[nxt] < ms[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1

    for start in range(n):
        if time.time() - t0 > timeout or len(results) >= max_results:
            break
        fc = [0]*n
        fc[start] = 1
        if fc[start] <= ms[start]:
            dfs([start], fc)

    return results


def canonicalize(word):
    L = len(word)
    best = word
    for i in range(L):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


def build_configs_all_trans(word, ms, n):
    L = len(word)
    wl = list(word)
    bins = {p for p in range(n) if ms[p] == 2}
    ternary = [p for p in range(n) if ms[p] == 3]
    n_tern = len(ternary)
    results = []
    for trans_bits in range(1 << n_tern):
        trans_dir = {}
        for p in bins:
            trans_dir[p] = 1
        for idx, p in enumerate(ternary):
            trans_dir[p] = 1 if not ((trans_bits >> idx) & 1) else -1
        configs = [[0]*n]
        for t in range(L):
            c = list(configs[-1])
            p = wl[t]
            c[p] = (c[p] + trans_dir[p]) % ms[p]
            configs.append(c)
        if configs[-1] != configs[0]:
            continue
        config_set = set(tuple(c) for c in configs[:L])
        if len(config_set) != L:
            continue
        results.append((trans_dir.copy(), [tuple(c) for c in configs[:L]]))
    return results


def find_ec_at_proc(word, configs, n, j):
    L = len(word)
    mt = set()
    nmt = set()
    for t in range(L):
        c = configs[t]
        triple = (c[(j-1)%n], c[j], c[(j+1)%n])
        if word[t] == j:
            mt.add(triple)
        else:
            nmt.add(triple)
    return mt & nmt


def has_any_ec(word, configs, ms, n):
    for j in range(n):
        if find_ec_at_proc(word, configs, n, j):
            return True
    return False


def check_mnu(word, configs, ms, n):
    """Check MNU: no config appears as both mover and non-mover at same proc
    with same neighbor values but different self values.

    Actually MNU = Mover Non-mover Uniqueness: for each proc p, the set of
    (L,S,R) triples seen when p is mover is disjoint from when p is non-mover
    AND S changes. But actually EC IS exactly mover/non-mover overlap.

    Let me check the broader MNU concept: does any shifted version of the
    config sequence yield a config that's NOT in the good cycle?
    """
    config_set = set(configs)
    L = len(word)

    # For each binary proc b, try shifting its value
    bins = [p for p in range(n) if ms[p] == 2]

    shadow_info = {}
    for b in bins:
        shifted_configs = []
        for c in configs:
            sc = list(c)
            sc[b] = (sc[b] + 1) % ms[b]  # flip binary
            shifted_configs.append(tuple(sc))

        # How many shifted configs are NOT in the good cycle?
        not_in_cycle = sum(1 for sc in shifted_configs if sc not in config_set)
        in_cycle = sum(1 for sc in shifted_configs if sc in config_set)

        shadow_info[b] = {
            'not_in_cycle': not_in_cycle,
            'in_cycle': in_cycle,
            'total': L,
        }

    return shadow_info


def check_shadow_cycle(word, configs, ms, n):
    """Check if the shadow cycle construction works.

    Shadow: for each config c in the cycle, define c' by flipping a binary proc.
    If c' is NEVER in the good cycle, then c' is a "shadow" config.
    The shadow cycle = {c' : c in good cycle} should be disjoint from good cycle
    and form its own cycle (under the same transition functions).
    """
    config_set = set(configs)
    L = len(word)
    bins = [p for p in range(n) if ms[p] == 2]

    results = {}
    for b in bins:
        # Shadow configs
        shadow = []
        for c in configs:
            sc = list(c)
            sc[b] = (sc[b] + 1) % ms[b]
            shadow.append(tuple(sc))

        shadow_set = set(shadow)

        # Disjointness: shadow ∩ good = empty?
        disjoint = len(shadow_set & config_set) == 0

        # Distinctness: all shadow configs distinct?
        distinct = len(shadow_set) == L

        # Do shadow configs form their own cycle under the same movers?
        # At step t: mover is word[t], config is shadow[t]
        # After mover fires: shadow[t+1] should equal shifted version of configs[t+1]
        # This is automatic if the transition only depends on (L,S,R) and the
        # flip is at a proc that doesn't affect the mover's context.

        results[b] = {
            'disjoint': disjoint,
            'distinct': distinct,
            'shadow_size': len(shadow_set),
            'overlap_count': len(shadow_set & config_set),
        }

    return results


def analyze_no_ec_structure(word, configs, ms, n):
    """Deep structural analysis of a no-EC cycle."""
    L = len(word)
    fc = Counter(word)
    bins = [p for p in range(n) if ms[p] == 2]
    terns = [p for p in range(n) if ms[p] == 3]

    # For each proc, show the mover/non-mover triple sets
    info = {}
    for j in range(n):
        mt = set()
        nmt = set()
        for t in range(L):
            c = configs[t]
            triple = (c[(j-1)%n], c[j], c[(j+1)%n])
            if word[t] == j:
                mt.add(triple)
            else:
                nmt.add(triple)
        info[j] = {
            'mover_triples': mt,
            'nonmover_triples': nmt,
            'overlap': mt & nmt,
            'type': 'binary' if ms[j] == 2 else 'ternary',
            'fc': fc[j],
        }
    return info


def examine_word_structure(word, ms, n):
    """Analyze mover word structure for sweep."""
    L = len(word)
    fc = Counter(word)
    disp = total_displacement(list(word), n)

    # Check: does it have the 2-pass sweep structure?
    # CW pass: procs fire in order 0,1,...,n-1
    # CCW pass: procs fire in reverse order n-1,...,1,0
    # With possible stutters

    # Find direction of each step
    directions = []
    for i in range(L):
        nxt = word[(i+1)%L]
        cur = word[i]
        diff = (nxt - cur) % n
        if diff == 1:
            directions.append(+1)
        elif diff == n-1:
            directions.append(-1)
        else:
            directions.append(0)

    # Find turnaround points
    turnarounds = []
    for i in range(L):
        if directions[i] != directions[(i+1)%L]:
            turnarounds.append(i)

    return {
        'displacement': disp,
        'fc': dict(fc),
        'turnarounds': turnarounds,
        'n_turnarounds': len(turnarounds),
    }


def main():
    print("RA16b: Shadow Analysis for No-EC Sweep Cycles")
    print("="*70)

    for n in [7, 9]:
        threshold = 4 * (3 ** (n - 2))
        print(f"\n{'='*70}")
        print(f"n = {n}, threshold = {threshold}")
        print(f"{'='*70}")

        # Find all sub-threshold multisets
        seen = set()
        all_cases = []
        for nb in range(3, n+1):
            nt = n - nb
            prod = (2**nb) * (3**nt)
            if prod >= threshold:
                continue
            for bin_combo in combinations(range(n), nb):
                bins_set = set(bin_combo)
                ms = [2 if p in bins_set else 3 for p in range(n)]
                if has_3_consecutive_binary(ms):
                    continue
                product = 1
                for m in ms:
                    product *= m
                if product >= threshold:
                    continue
                ms_rotations = [tuple(ms[(r+i)%n] for i in range(n)) for r in range(n)]
                canon_ms = min(ms_rotations)
                if canon_ms not in seen:
                    seen.add(canon_ms)
                    all_cases.append((canon_ms, ms))

        no_ec_total = 0
        shadow_works_total = 0
        shadow_fails_total = 0

        for canon_ms, ms in all_cases:
            max_len = sum(ms)
            words = enumerate_words_dfs(n, ms, max_len, max_results=50000, timeout=90)
            unique_words = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique_words:
                    unique_words[c] = w

            sweep_words = [w for w in unique_words.values()
                           if total_displacement(list(w), n) is not None
                           and abs(total_displacement(list(w), n)) >= 2*n]

            if not sweep_words:
                continue

            print(f"\n--- ms={list(ms)} ---")
            bins = [p for p in range(n) if ms[p] == 2]

            for w_idx, w in enumerate(sweep_words):
                for trans_dir, configs in build_configs_all_trans(w, ms, n):
                    if has_any_ec(w, configs, ms, n):
                        continue

                    no_ec_total += 1

                    # Shadow analysis
                    shadow = check_shadow_cycle(w, configs, ms, n)
                    mnu = check_mnu(w, configs, ms, n)

                    any_shadow_works = False
                    for b in bins:
                        if shadow[b]['disjoint'] and shadow[b]['distinct']:
                            any_shadow_works = True

                    if any_shadow_works:
                        shadow_works_total += 1
                    else:
                        shadow_fails_total += 1

                    # Print first few detailed examples
                    if no_ec_total <= 3:
                        print(f"\n  Example {no_ec_total}: word={list(w)}")
                        wstruct = examine_word_structure(w, ms, n)
                        print(f"    displacement={wstruct['displacement']}, "
                              f"turnarounds={wstruct['n_turnarounds']}")
                        print(f"    fc={wstruct['fc']}")
                        print(f"    trans_dir={trans_dir}")

                        print(f"    Shadow analysis (flip each binary):")
                        for b in bins:
                            s = shadow[b]
                            m = mnu[b]
                            print(f"      binary {b}: disjoint={s['disjoint']}, "
                                  f"distinct={s['distinct']}, "
                                  f"not_in_cycle={m['not_in_cycle']}/{m['total']}")

                        # Show per-proc triple analysis
                        info = analyze_no_ec_structure(w, configs, ms, n)
                        print(f"    Per-proc triple analysis:")
                        for j in range(n):
                            pi = info[j]
                            print(f"      proc {j} ({pi['type']}, fc={pi['fc']}): "
                                  f"|mover|={len(pi['mover_triples'])}, "
                                  f"|nonmover|={len(pi['nonmover_triples'])}, "
                                  f"|overlap|={len(pi['overlap'])}")
                            if len(pi['mover_triples']) <= 4:
                                print(f"        mover triples: {sorted(pi['mover_triples'])}")
                            if len(pi['nonmover_triples']) <= 6:
                                print(f"        nonmover triples: {sorted(pi['nonmover_triples'])}")

        print(f"\n{'='*70}")
        print(f"SHADOW SUMMARY for n={n}")
        print(f"{'='*70}")
        print(f"Total no-EC sweep cycles: {no_ec_total}")
        print(f"  Shadow works (disjoint+distinct at some binary): {shadow_works_total}")
        print(f"  Shadow fails: {shadow_fails_total}")
        if shadow_fails_total > 0:
            print(f"  *** WARNING: Shadow obstruction is NOT universal ***")
        elif no_ec_total > 0 and shadow_fails_total == 0:
            print(f"  *** Shadow obstruction IS universal for no-EC cycles ***")


if __name__ == '__main__':
    main()
