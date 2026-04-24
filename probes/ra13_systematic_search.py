#!/usr/bin/env python3
"""
ra13_systematic_search.py — Exhaustive search for odd-winding non-uniform
good cycles that are transition-consistent, at n=5.

For each mover word that is odd-winding + non-uniform:
1. Try ALL possible config sequences (DFS over new values at each step)
2. Check: all configs distinct, returns to start, transition-consistent
3. If found: test binary flip

This is the DEFINITIVE test of whether such cycles even exist.
"""
import time
from itertools import combinations, product as iproduct
from collections import defaultdict


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


def has_no_triple(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


def generate_words_dfs(n, ms, max_results=5000, timeout=30):
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


def are_non_adjacent(b1, b2, n):
    return (b1 - b2) % n > 1 and (b2 - b1) % n > 1


def is_trans_consistent(word, n, configs):
    L = len(word)
    trans = {}
    for t in range(L):
        for p in range(n):
            lp, rp = (p - 1) % n, (p + 1) % n
            ctx = (p, configs[t][lp], configs[t][p], configs[t][rp])
            val = configs[(t + 1) % L][p]
            if ctx in trans:
                if trans[ctx] != val:
                    return False
            trans[ctx] = val
    return True


def check_binary_flip(word, n, ms, configs, bins_to_flip):
    L = len(word)
    companion = []
    for t in range(L):
        sc = list(configs[t])
        for p in bins_to_flip:
            sc[p] = 1 - sc[p]
        companion.append(tuple(sc))
    orig_set = set(configs)
    comp_set = set(companion)
    if len(comp_set) != L:
        return False, "not_distinct"
    if len(orig_set & comp_set) > 0:
        return False, "not_disjoint"
    for t in range(L):
        mover = word[t]
        for p in range(n):
            if p == mover:
                if companion[(t + 1) % L][p] == companion[t][p]:
                    return False, f"mover_no_fire"
            else:
                if companion[(t + 1) % L][p] != companion[t][p]:
                    return False, f"nonmover_change"
    # Trans consistency
    trans = {}
    for cycle_cfgs in [configs, companion]:
        for t in range(L):
            for p in range(n):
                lp, rp = (p - 1) % n, (p + 1) % n
                ctx = (p, cycle_cfgs[t][lp], cycle_cfgs[t][p], cycle_cfgs[t][rp])
                val = cycle_cfgs[(t + 1) % L][p]
                if ctx in trans:
                    if trans[ctx] != val:
                        return False, f"trans_conflict"
                trans[ctx] = val
    return True, "OK"


def find_consistent_cycles_exhaustive(word, n, ms, max_cycles=10, timeout=5):
    """
    Exhaustive DFS: for a given mover word, find ALL transition-consistent
    config sequences by trying all possible new values at each firing step.

    At each step t, the mover is word[t]. The mover must change to some new value.
    All non-movers stay the same. We try each possible new value for the mover,
    and enforce transition consistency along the way.
    """
    L = len(word)
    results = []
    t0 = time.time()

    # Try all starting configs
    for start in iproduct(*[range(m) for m in ms]):
        if time.time() - t0 > timeout or len(results) >= max_cycles:
            break

        # DFS through config choices
        # State: partially built config sequence
        # At step t, we choose the new value for word[t]

        def dfs(t, configs, trans):
            """Build config at step t+1 from step t."""
            if time.time() - t0 > timeout or len(results) >= max_cycles:
                return

            if t == L:
                # Check: does it return to start?
                if configs[L] == start:
                    # Check all distinct
                    config_set = set(configs[:L])
                    if len(config_set) == L:
                        results.append([tuple(c) for c in configs[:L]])
                return

            mover = word[t]
            cur = configs[t]
            old_val = cur[mover]

            for new_val in range(ms[mover]):
                if new_val == old_val:
                    continue  # mover must change

                # Build next config
                nxt = list(cur)
                nxt[mover] = new_val

                # Check transition consistency
                consistent = True
                new_trans = dict(trans)

                for p in range(n):
                    lp, rp = (p - 1) % n, (p + 1) % n
                    ctx = (p, cur[lp], cur[p], cur[rp])

                    if p == mover:
                        val = new_val
                    else:
                        val = cur[p]  # non-mover stays

                    if ctx in new_trans:
                        if new_trans[ctx] != val:
                            consistent = False
                            break
                    else:
                        new_trans[ctx] = val

                if not consistent:
                    continue

                # Check config not already seen (for distinctness)
                nxt_t = tuple(nxt)
                if t + 1 < L and nxt_t in set(tuple(c) for c in configs[:t+1]):
                    continue  # would create duplicate

                configs.append(nxt)
                dfs(t + 1, configs, new_trans)
                configs.pop()

        configs_list = [list(start)]
        dfs(0, configs_list, {})

    return results


def main():
    print("RA13 Systematic Search: Exhaustive good cycle enumeration")
    print("=" * 70)

    t_start = time.time()

    for n in [5, 7]:
        threshold = 4 * (3 ** (n - 2))
        print(f"\n{'='*70}")
        print(f"n={n}, threshold={threshold}")
        print("=" * 70)

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
            nonadj_pairs = [pair for pair in combinations(binary_procs, 2)
                            if are_non_adjacent(pair[0], pair[1], n)]
            if not nonadj_pairs:
                continue

            print(f"\n  ms={ms} (bins={binary_procs}, prod={prod})")

            words = generate_words_dfs(n, ms, max_results=500, timeout=10)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w
            print(f"    Total unique words: {len(unique)}")

            ow_nu_words = []
            for w in unique.values():
                wl = list(w)
                W = total_displacement(wl, n)
                if abs(W) != n:
                    continue
                dirs = step_directions(wl, n)
                ns = [d for d in dirs if d != 0]
                if not ns or all(d == ns[0] for d in ns):
                    continue
                ow_nu_words.append(wl)

            print(f"    Odd-winding non-uniform words: {len(ow_nu_words)}")

            n_cycles_found = 0
            n_flip_pass = 0
            n_flip_fail = 0

            for w_idx, wl in enumerate(ow_nu_words):
                if time.time() - t_start > 120:  # 2 min total budget
                    print(f"    Time limit reached after {w_idx} words")
                    break

                cycles = find_consistent_cycles_exhaustive(
                    wl, n, ms, max_cycles=5, timeout=2)
                n_cycles_found += len(cycles)

                for configs in cycles:
                    for pair in nonadj_pairs:
                        ok, reason = check_binary_flip(wl, n, ms, configs, list(pair))
                        if ok:
                            n_flip_pass += 1
                        else:
                            n_flip_fail += 1

                    if cycles and w_idx == 0:
                        print(f"    First cycle found!")
                        print(f"      word={wl}")
                        print(f"      W={total_displacement(wl, n)}")
                        print(f"      configs[0]={configs[0]}")

            print(f"    Consistent cycles found: {n_cycles_found}")
            if n_cycles_found > 0:
                print(f"    Flip tests: {n_flip_pass} pass, {n_flip_fail} fail")
            else:
                print(f"    NO consistent cycles exist for these words!")

    elapsed = time.time() - t_start
    print(f"\n{'='*70}")
    print(f"Done in {elapsed:.1f}s")
    print("=" * 70)


if __name__ == '__main__':
    main()
