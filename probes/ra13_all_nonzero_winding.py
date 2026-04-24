#!/usr/bin/env python3
"""
ra13_all_nonzero_winding.py — Script 4: Test binary flip on ALL non-zero-winding
cycle types. If it works universally, we get a single theorem closing both
sweep and odd-winding non-consecutive cases.

Cycle types tested:
A. Sweep (|disp| = 2n, uniform)     — already verified by RA10
B. Sweep (|disp| = 2n, non-uniform) — wiggly sweeps
C. Odd-winding uniform  (|disp| = n, uniform)
D. Odd-winding non-uniform (|disp| = n, non-uniform)  — the target
E. Higher winding (|disp| > 2n)
F. Any non-zero winding

For each: test binary flip on all non-adjacent pairs of binary procs.
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


def classify_winding(word, n):
    W = total_displacement(word, n)
    absW = abs(W)
    dirs = step_directions(word, n)
    non_stay = [d for d in dirs if d != 0]
    uniform = not non_stay or all(d == non_stay[0] for d in non_stay)

    if absW == 0:
        return 'zero_winding'
    elif absW == n:
        return 'odd_uniform' if uniform else 'odd_nonuniform'
    elif absW == 2 * n:
        return 'sweep_uniform' if uniform else 'sweep_nonuniform'
    elif absW > 2 * n:
        return 'higher_winding'
    else:
        return f'winding_{absW}'


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
    return (b1 - b2) % n > 1 and (b2 - b1) % n > 1


def check_binary_flip(word, n, ms, configs, bins_to_flip):
    L = len(word)
    wl = list(word)
    companion = []
    for t in range(L):
        sc = list(configs[t])
        for p in bins_to_flip:
            sc[p] = 1 - sc[p]
        companion.append(tuple(sc))

    orig_set = set(configs)
    comp_set = set(companion)
    if len(orig_set & comp_set) > 0:
        return False, "not_disjoint"
    if len(comp_set) != L:
        return False, "not_distinct"

    for t in range(L):
        mover = wl[t]
        for p in range(n):
            if p == mover:
                if companion[(t + 1) % L][p] == companion[t][p]:
                    return False, "mover_no_fire"
            else:
                if companion[(t + 1) % L][p] != companion[t][p]:
                    return False, "nonmover_change"

    # Transition consistency
    trans = {}
    for cycle_configs in [configs, companion]:
        for t in range(L):
            for p in range(n):
                lp = (p - 1) % n
                rp = (p + 1) % n
                ctx = (p, cycle_configs[t][lp], cycle_configs[t][p], cycle_configs[t][rp])
                val = cycle_configs[(t + 1) % L][p]
                if ctx in trans:
                    if trans[ctx] != val:
                        return False, "trans_conflict"
                else:
                    trans[ctx] = val

    return True, "OK"


def main():
    print("RA13 Script 4: Binary Flip on ALL Non-Zero-Winding Types")
    print("=" * 70)

    # Results by winding type
    results_by_type = defaultdict(lambda: {'tested': 0, 'pass': 0, 'fail': 0})

    for n in [7, 9]:
        threshold = 4 * (3 ** (n - 2))
        print(f"\n{'='*70}")
        print(f"n={n}, threshold={threshold}")

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

            # Get non-adjacent binary pairs
            nonadj_pairs = [pair for pair in combinations(binary_procs, 2)
                            if are_non_adjacent(pair[0], pair[1], n)]
            if not nonadj_pairs:
                continue

            words = generate_words_dfs(n, ms, max_results=3000, timeout=10)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            for w in unique.values():
                wl = list(w)
                W = total_displacement(wl, n)
                if W == 0:
                    continue  # skip zero winding

                wtype = classify_winding(wl, n)

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

                    for pair in nonadj_pairs:
                        ok, reason = check_binary_flip(wl, n, ms, configs, list(pair))
                        results_by_type[wtype]['tested'] += 1
                        if ok:
                            results_by_type[wtype]['pass'] += 1
                        else:
                            results_by_type[wtype]['fail'] += 1

        # Print intermediate results
        print(f"\n  Results so far (n={n}):")
        for wtype in sorted(results_by_type.keys()):
            r = results_by_type[wtype]
            pct = 100.0 * r['pass'] / r['tested'] if r['tested'] else 0
            status = "ALL PASS" if r['fail'] == 0 else f"{r['fail']} FAIL"
            print(f"    {wtype:25s}: {r['tested']:6d} tested, {r['pass']:6d} pass ({pct:5.1f}%), {status}")

    print(f"\n{'='*70}")
    print("FINAL RESULTS BY WINDING TYPE")
    print("=" * 70)

    all_pass = True
    total_tested = 0
    total_pass = 0

    for wtype in sorted(results_by_type.keys()):
        r = results_by_type[wtype]
        total_tested += r['tested']
        total_pass += r['pass']
        pct = 100.0 * r['pass'] / r['tested'] if r['tested'] else 0
        status = "ALL PASS" if r['fail'] == 0 else f"{r['fail']} FAIL"
        if r['fail'] > 0:
            all_pass = False
        print(f"  {wtype:25s}: {r['tested']:6d} tested, {r['pass']:6d} pass ({pct:5.1f}%), {status}")

    print(f"\n  TOTAL: {total_tested} tested, {total_pass} pass, {total_tested - total_pass} fail")

    if all_pass and total_tested > 0:
        print("""
>>> BINARY FLIP WORKS FOR ALL NON-ZERO-WINDING TYPES! <<<

THEOREM: For any non-zero-winding good cycle with >=3 non-consecutive binary
at sub-threshold product, flipping any non-adjacent pair of binary proc values
produces a valid disjoint companion good cycle.

COROLLARY: non-zero-winding + >=3 non-consecutive binary + sub-threshold
+ converges => False.

This single theorem closes BOTH:
  - WP4 (sweep non-consecutive)
  - WP5 (odd-winding non-consecutive isolated)

The only remaining case is zero-winding, handled by palindromic EC.
""")
    else:
        print("\nNot all pass. Need type-specific arguments.")

        # Show which types fail
        failing_types = [wt for wt, r in results_by_type.items() if r['fail'] > 0]
        passing_types = [wt for wt, r in results_by_type.items() if r['fail'] == 0 and r['tested'] > 0]
        print(f"\n  Passing types: {passing_types}")
        print(f"  Failing types: {failing_types}")


if __name__ == '__main__':
    main()
