#!/usr/bin/env python3
"""
ra13_flip_failures.py — Script 3: Diagnose WHY binary flip fails
for odd-winding non-uniform cycles (if it does).

For each failure:
1. Which validity check breaks? (mover, distinctness, transition)
2. What structure do failures have?
3. Is there a pattern (e.g., specific adjacency, specific fc, specific winding direction)?

Also tests: does it fail only for ADJACENT binary pairs but work for NON-ADJACENT?
"""
import random
import time
from itertools import combinations
from collections import defaultdict

random.seed(42)


def total_displacement(word, n):
    W = 0
    L = len(word)
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 0:
            pass
        elif diff <= n // 2:
            W += diff
        else:
            W -= (n - diff)
    return W


def step_directions(word, n):
    L = len(word)
    dirs = []
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 0:
            dirs.append(0)
        elif diff == 1:
            dirs.append(1)
        elif diff == n - 1:
            dirs.append(-1)
        else:
            dirs.append(diff if diff <= n // 2 else diff - n)
    return dirs


def is_odd_winding(word, n):
    return abs(total_displacement(word, n)) == n


def is_uniform_direction(word, n):
    dirs = step_directions(word, n)
    non_stay = [d for d in dirs if d != 0]
    if not non_stay:
        return True
    return all(d == non_stay[0] for d in non_stay)


def has_no_triple(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


def fire_count(word, n):
    fc = [0] * n
    for m in word:
        fc[m] += 1
    return fc


def generate_words_dfs(n, ms, max_results=3000, timeout=15):
    target_cl = sum(ms)
    results = []
    t0 = time.time()

    def dfs(word, fc):
        if time.time() - t0 > timeout or len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == ms[p] for p in range(n)):
                results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in [(last + 1) % n, (last - 1) % n]:
            if fc[nxt] < ms[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1

    for start in range(n):
        if time.time() - t0 > timeout or len(results) >= max_results:
            break
        fc = [0] * n
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


def build_configs(word, n, ms, trans_dir):
    L = len(word)
    configs = [[0] * n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + trans_dir[p]) % ms[p]
        configs.append(c)
    if configs[-1] != configs[0]:
        return None
    config_set = set(tuple(c) for c in configs[:L])
    if len(config_set) != L:
        return None
    return [tuple(c) for c in configs[:L]]


def are_non_adjacent(b1, b2, n):
    return abs(b1 - b2) % n > 1 and abs(b2 - b1) % n > 1


def detailed_flip_check(word, n, ms, configs, bins_to_flip):
    """Detailed check with breakdown of which property fails."""
    L = len(word)
    wl = list(word)

    companion = []
    for t in range(L):
        sc = list(configs[t])
        for p in bins_to_flip:
            sc[p] = 1 - sc[p]
        companion.append(tuple(sc))

    # Property 1: Distinctness
    comp_set = set(companion)
    if len(comp_set) != L:
        dupes = L - len(comp_set)
        return 'distinctness', f"{dupes} duplicate configs in companion"

    # Property 2: Disjointness
    orig_set = set(configs)
    overlap = orig_set & comp_set
    if overlap:
        return 'disjointness', f"{len(overlap)} shared configs"

    # Property 3: Mover fires
    for t in range(L):
        mover = wl[t]
        if companion[(t + 1) % L][mover] == companion[t][mover]:
            return 'mover_no_fire', f"mover {mover} doesn't fire at step {t}"

    # Property 4: Non-movers stable
    for t in range(L):
        mover = wl[t]
        for p in range(n):
            if p != mover:
                if companion[(t + 1) % L][p] != companion[t][p]:
                    return 'nonmover_change', f"non-mover {p} changes at step {t}"

    # Property 5: Transition consistency (same f for same context)
    # Build combined table from both cycles
    trans = {}
    for t in range(L):
        mover = wl[t]
        for p in range(n):
            lp = (p - 1) % n
            rp = (p + 1) % n
            # Original
            ctx_o = (p, configs[t][lp], configs[t][p], configs[t][rp])
            val_o = configs[(t + 1) % L][p]
            if ctx_o in trans:
                if trans[ctx_o] != val_o:
                    return 'orig_inconsistent', f"original has inconsistent trans at p={p}, t={t}"
            else:
                trans[ctx_o] = val_o

            # Companion
            ctx_c = (p, companion[t][lp], companion[t][p], companion[t][rp])
            val_c = companion[(t + 1) % L][p]
            if ctx_c in trans:
                if trans[ctx_c] != val_c:
                    # This is the KEY failure: same (L,S,R) seen in both cycles
                    # with different required output
                    is_mover = (p == mover)
                    return 'trans_conflict', (
                        f"p={p}, t={t}, ctx=({ctx_c[1]},{ctx_c[2]},{ctx_c[3]}), "
                        f"existing={trans[ctx_c]}, need={val_c}, is_mover={is_mover}"
                    )
            else:
                trans[ctx_c] = val_c

    return 'pass', 'OK'


def main():
    print("RA13 Script 3: Diagnose Binary Flip Failures")
    print("=" * 70)

    failure_types = defaultdict(int)
    pass_count = 0
    total_count = 0

    adj_pass = 0
    adj_fail = 0
    nonadj_pass = 0
    nonadj_fail = 0

    detailed_failures = []

    for n in [7, 9]:
        threshold = 4 * (3 ** (n - 2))
        print(f"\n--- n={n} ---")

        for bins in combinations(range(n), 3):
            bins_set = set(bins)
            ms = [2 if p in bins_set else 3 for p in range(n)]
            if not has_no_triple(ms, n):
                continue
            prod = 1
            for m in ms:
                prod *= m
            if prod >= threshold:
                continue

            binary_procs = sorted(bins_set)
            ternary = [p for p in range(n) if ms[p] == 3]
            n_tern = len(ternary)

            words = generate_words_dfs(n, ms, max_results=2000, timeout=8)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            for w in unique.values():
                wl = list(w)
                if not is_odd_winding(wl, n) or is_uniform_direction(wl, n):
                    continue

                for trans_bits in range(1 << n_tern):
                    trans_dir = {}
                    for p in range(n):
                        if ms[p] == 2:
                            trans_dir[p] = 1
                        else:
                            idx = ternary.index(p)
                            trans_dir[p] = 1 if not ((trans_bits >> idx) & 1) else -1

                    configs = build_configs(wl, n, ms, trans_dir)
                    if configs is None:
                        continue

                    for pair in combinations(binary_procs, 2):
                        is_adj = not are_non_adjacent(pair[0], pair[1], n)
                        ftype, detail = detailed_flip_check(wl, n, ms, configs, list(pair))
                        total_count += 1

                        if ftype == 'pass':
                            pass_count += 1
                            if is_adj:
                                adj_pass += 1
                            else:
                                nonadj_pass += 1
                        else:
                            failure_types[ftype] += 1
                            if is_adj:
                                adj_fail += 1
                            else:
                                nonadj_fail += 1
                            if len(detailed_failures) < 10:
                                detailed_failures.append({
                                    'n': n,
                                    'ms': list(ms),
                                    'word': wl,
                                    'pair': pair,
                                    'is_adj': is_adj,
                                    'ftype': ftype,
                                    'detail': detail,
                                    'fc': fire_count(wl, n),
                                    'W': total_displacement(wl, n),
                                })

        print(f"  Running total: {pass_count}/{total_count} pass")

    print(f"\n{'='*70}")
    print("RESULTS")
    print(f"  Total tested: {total_count}")
    print(f"  Pass: {pass_count}")
    print(f"  Fail: {total_count - pass_count}")
    if total_count > 0:
        print(f"  Pass rate: {100.0*pass_count/total_count:.2f}%")
    print()
    print("By adjacency:")
    print(f"  Adjacent pairs:     {adj_pass} pass, {adj_fail} fail")
    print(f"  Non-adjacent pairs: {nonadj_pass} pass, {nonadj_fail} fail")
    print()

    if failure_types:
        print("Failure type breakdown:")
        for ft, cnt in sorted(failure_types.items(), key=lambda x: -x[1]):
            print(f"  {ft}: {cnt}")
        print()

    if detailed_failures:
        print("Detailed failure examples:")
        for i, f in enumerate(detailed_failures[:5]):
            print(f"\n  [{i+1}] n={f['n']}, ms={f['ms']}, pair={f['pair']}, adj={f['is_adj']}")
            print(f"      word={f['word'][:20]}{'...' if len(f['word'])>20 else ''}")
            print(f"      fc={f['fc']}, W={f['W']}")
            print(f"      failure={f['ftype']}: {f['detail']}")

    if total_count - pass_count == 0 and total_count > 0:
        print("\n>>> ALL PASS: Binary flip works for ALL odd-winding non-uniform cycles! <<<")
    elif nonadj_fail == 0 and nonadj_pass > 0:
        print("\n>>> NON-ADJACENT pairs ALL PASS. Only adjacent-pair failures. <<<")
        print("    Since we need >=3 non-consecutive binary, we always have non-adjacent pairs.")
        print("    So binary flip on non-adjacent pairs closes the case!")


if __name__ == '__main__':
    main()
