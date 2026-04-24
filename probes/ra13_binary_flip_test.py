#!/usr/bin/env python3
"""
ra13_binary_flip_test.py — Script 2 (FIXED): Test binary flip disjointness on
odd-winding non-uniform cycles with >=3 non-consecutive binary.

Key fix: only test cycles that are transition-consistent (the original cycle
must have no transition conflicts before we test the flip).

For each qualifying cycle:
1. Find all non-adjacent pairs of binary procs
2. Flip c[b1] and c[b2] in every config
3. Check: valid good cycle? Disjoint from original? Transition-consistent with original?
4. Report success rate.
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


def has_isolated_firings(word, p):
    L = len(word)
    for i in range(L):
        if word[i] == p and word[(i + 1) % L] == p:
            return False
    return True


def min_gap(word, p):
    fire_steps = [i for i, m in enumerate(word) if m == p]
    if len(fire_steps) < 2:
        return None
    L = len(word)
    best = L + 1
    for idx in range(len(fire_steps)):
        a = fire_steps[idx]
        b = fire_steps[(idx + 1) % len(fire_steps)]
        gap = (b - a) % L
        if gap < best:
            best = gap
    return best


def generate_words_dfs(n, ms, max_results=3000, timeout=15):
    """Generate mover words as proper ring walks (steps of +-1)."""
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
    """Build config sequence. Returns configs or None if invalid."""
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


def is_transition_consistent(word, n, configs):
    """Check that the original cycle is consistent with SOME transition function.
    Same (proc, L, S, R) must always map to the same output S'."""
    L = len(word)
    trans = {}
    for t in range(L):
        for p in range(n):
            lp = (p - 1) % n
            rp = (p + 1) % n
            ctx = (p, configs[t][lp], configs[t][p], configs[t][rp])
            val = configs[(t + 1) % L][p]
            if ctx in trans:
                if trans[ctx] != val:
                    return False
            else:
                trans[ctx] = val
    return True


def are_non_adjacent(b1, b2, n):
    return (b1 - b2) % n > 1 and (b2 - b1) % n > 1


def check_binary_flip(word, n, ms, configs, bins_to_flip):
    """Check if flipping binary procs gives valid disjoint companion.
    Assumes original cycle is already transition-consistent.
    """
    L = len(word)
    wl = list(word)

    companion = []
    for t in range(L):
        sc = list(configs[t])
        for p in bins_to_flip:
            sc[p] = 1 - sc[p]
        companion.append(tuple(sc))

    # Distinctness
    comp_set = set(companion)
    if len(comp_set) != L:
        return False, "not_distinct"

    # Disjointness
    orig_set = set(configs)
    if len(orig_set & comp_set) > 0:
        return False, "not_disjoint"

    # Mover fires / non-mover stable
    for t in range(L):
        mover = wl[t]
        for p in range(n):
            if p == mover:
                if companion[(t + 1) % L][p] == companion[t][p]:
                    return False, f"mover_no_fire(p={p},t={t})"
            else:
                if companion[(t + 1) % L][p] != companion[t][p]:
                    return False, f"nonmover_change(p={p},t={t})"

    # Transition consistency: original + companion must be compatible with SOME f
    trans = {}
    # Add original transitions
    for t in range(L):
        for p in range(n):
            lp = (p - 1) % n
            rp = (p + 1) % n
            ctx = (p, configs[t][lp], configs[t][p], configs[t][rp])
            val = configs[(t + 1) % L][p]
            trans[ctx] = val

    # Check companion transitions against same table
    for t in range(L):
        for p in range(n):
            lp = (p - 1) % n
            rp = (p + 1) % n
            ctx = (p, companion[t][lp], companion[t][p], companion[t][rp])
            val = companion[(t + 1) % L][p]
            if ctx in trans:
                if trans[ctx] != val:
                    return False, f"trans_conflict(p={p},t={t},ctx={ctx[1:]},need={trans[ctx]},got={val})"
            else:
                trans[ctx] = val

    return True, "OK"


def main():
    print("RA13 Script 2 (FIXED): Binary Flip Test on Odd-Winding Non-Uniform")
    print("=" * 70)

    grand_tested = 0
    grand_pass = 0
    grand_fail = 0
    n_trans_inconsistent = 0
    n_consistent_cycles = 0
    failure_reasons = defaultdict(int)
    all_failures = []

    for n in [7, 9]:
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
            ternary = [p for p in range(n) if ms[p] == 3]
            n_tern = len(ternary)

            nonadj_pairs = [pair for pair in combinations(binary_procs, 2)
                            if are_non_adjacent(pair[0], pair[1], n)]
            if not nonadj_pairs:
                continue

            # Generate only proper ring walk words via DFS
            words = generate_words_dfs(n, ms, max_results=3000, timeout=10)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            # Filter odd-winding non-uniform
            ow_nu_words = []
            for w in unique.values():
                wl = list(w)
                if is_odd_winding(wl, n) and not is_uniform_direction(wl, n):
                    ow_nu_words.append(wl)

            if not ow_nu_words:
                continue

            ms_tested = 0
            ms_pass = 0
            ms_fail = 0
            ms_incons = 0
            ms_cons = 0
            local_failures = []

            for wl in ow_nu_words:
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

                    # KEY FIX: check transition consistency of original cycle
                    if not is_transition_consistent(wl, n, configs):
                        ms_incons += 1
                        continue

                    ms_cons += 1

                    # Test all non-adjacent pairs
                    for pair in nonadj_pairs:
                        ok, reason = check_binary_flip(wl, n, ms, configs, list(pair))
                        ms_tested += 1
                        if ok:
                            ms_pass += 1
                        else:
                            ms_fail += 1
                            failure_reasons[reason.split('(')[0]] += 1
                            if len(local_failures) < 3:
                                local_failures.append({
                                    'word': wl,
                                    'pair': pair,
                                    'reason': reason,
                                    'ms': list(ms),
                                })

                    # Also test flipping all 3 binary
                    ok, reason = check_binary_flip(wl, n, ms, configs, binary_procs)
                    ms_tested += 1
                    if ok:
                        ms_pass += 1
                    else:
                        ms_fail += 1
                        failure_reasons[reason.split('(')[0]] += 1

            grand_tested += ms_tested
            grand_pass += ms_pass
            grand_fail += ms_fail
            n_trans_inconsistent += ms_incons
            n_consistent_cycles += ms_cons
            all_failures.extend(local_failures)

            if ms_tested > 0 or ms_incons > 0:
                pct = 100.0 * ms_pass / ms_tested if ms_tested else 0
                status = "ALL PASS" if ms_fail == 0 else f"{ms_fail} FAIL"
                print(f"  ms={ms} bins={binary_procs}: {ms_cons} consistent cycles, "
                      f"{ms_tested} flip tests, {ms_pass} pass ({pct:.1f}%), {status}"
                      f"  [inconsistent: {ms_incons}]")
                for f in local_failures[:2]:
                    print(f"    FAIL: pair={f['pair']}, reason={f['reason']}")

    print(f"\n{'='*70}")
    print("GRAND TOTALS")
    print(f"  Trans-inconsistent (filtered out): {n_trans_inconsistent}")
    print(f"  Trans-consistent cycles: {n_consistent_cycles}")
    print(f"  Flip tests: {grand_tested}")
    print(f"  Pass:   {grand_pass}")
    print(f"  Fail:   {grand_fail}")
    if grand_tested > 0:
        print(f"  Rate:   {100.0*grand_pass/grand_tested:.2f}%")
    print("=" * 70)

    if failure_reasons:
        print("\nFailure breakdown:")
        for reason, count in sorted(failure_reasons.items(), key=lambda x: -x[1]):
            print(f"  {reason}: {count}")

    if grand_fail == 0 and grand_tested > 0:
        print("""
>>> BINARY FLIP DISJOINTNESS WORKS FOR ODD-WINDING NON-UNIFORM! <<<

Same argument as sweep: flip any non-adjacent binary pair => disjoint companion.
Two disjoint good cycles => not converges => False.
""")
    elif grand_tested == 0:
        print("\nNO transition-consistent odd-winding non-uniform cycles found.")
        print("This may mean such cycles don't exist with single-direction transitions.")
        print("Need to test with context-dependent transitions (all possible config sequences).")
    else:
        print(f"\n{grand_fail} failures. Binary flip does NOT universally work.")
        for f in all_failures[:5]:
            print(f"\n  ms={f['ms']}, pair={f['pair']}")
            print(f"  word={f['word']}")
            print(f"  reason={f['reason']}")


if __name__ == '__main__':
    main()
