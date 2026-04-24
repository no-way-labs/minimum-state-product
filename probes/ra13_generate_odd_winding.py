#!/usr/bin/env python3
"""
ra13_generate_odd_winding.py — Script 1: Generate odd-winding non-uniform cycles
with >=3 non-consecutive binary at sub-threshold product.

Approach: For each multiset, enumerate mover words by random shuffling and
DFS, then build configs under all transition combos. Filter for:
  - isOddWinding: |totalDisplacement| = n
  - not uniformDirection: mixed CW/CCW steps
  - >=3 non-consecutive binary
  - sub-threshold product
  - (optional) has a binary proc with isolated firings and gap >= 2
"""
import random
import time
from itertools import combinations, product as iproduct
from collections import defaultdict

random.seed(42)


def total_displacement(word, n):
    """Net displacement of mover walk on Z_n ring."""
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


def has_no_triple_consecutive_binary(ms, n):
    """Check no 3 consecutive binary procs exist."""
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
    """All firings of p are isolated (no consecutive p, p)."""
    L = len(word)
    for i in range(L):
        if word[i] == p and word[(i + 1) % L] == p:
            return False
    return True


def min_gap(word, p):
    """Min gap between consecutive firings of p. Returns gap or None."""
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


def build_configs(word, n, ms, trans_dir):
    """Build config sequence from mover word and transition directions.
    trans_dir[p] = +1 or -1 (for ternary) or +1 (for binary, always inc).
    Returns configs list or None if invalid.
    """
    L = len(word)
    configs = [[0] * n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + trans_dir[p]) % ms[p]
        configs.append(c)

    # Must return to start
    if configs[-1] != configs[0]:
        return None

    # All configs distinct
    config_set = set(tuple(c) for c in configs[:L])
    if len(config_set) != L:
        return None

    return [tuple(c) for c in configs[:L]]


def enumerate_multisets(n, min_binary=3):
    """Generate multisets with >=min_binary binary procs, no 3 consecutive, sub-threshold."""
    threshold = 4 * (3 ** (n - 2))
    results = []
    for bins in combinations(range(n), min_binary):
        bins_set = set(bins)
        ms = [2 if p in bins_set else 3 for p in range(n)]
        if not has_no_triple_consecutive_binary(ms, n):
            continue
        prod = 1
        for m in ms:
            prod *= m
        if prod >= threshold:
            continue
        results.append(ms)
    return results


def generate_words_by_shuffle(n, ms, num_trials=5000, max_fc_mult=1):
    """Generate mover words by random shuffling of fire-count vectors.
    max_fc_mult: max multiplier for fire counts (1 = exactly ms[p] fires each).
    """
    words = set()

    for mult in range(1, max_fc_mult + 1):
        fc = [ms[p] * mult for p in range(n)]
        template = []
        for p in range(n):
            template.extend([p] * fc[p])

        for _ in range(num_trials):
            word = list(template)
            random.shuffle(word)
            words.add(tuple(word))

    return list(words)


def generate_words_dfs(n, ms, max_results=2000, timeout=15):
    """Generate mover words by DFS on the ring walk."""
    target_cl = sum(ms)
    results = []
    t0 = time.time()

    def dfs(word, fc):
        if time.time() - t0 > timeout or len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == ms[p] for p in range(n)):
                diff = (word[0] - word[-1]) % n
                if diff in (1, n - 1) or diff == 0:
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


def main():
    print("RA13 Script 1: Generate Odd-Winding Non-Uniform Cycles")
    print("=" * 70)

    grand_total = 0
    grand_odd_winding_nonuniform = 0
    grand_with_isolated = 0

    for n in [7, 9]:
        threshold = 4 * (3 ** (n - 2))
        print(f"\n{'='*70}")
        print(f"n={n}, threshold={threshold}")
        print("=" * 70)

        multisets = enumerate_multisets(n, min_binary=3)
        print(f"Multisets with >=3 non-consecutive binary, sub-threshold: {len(multisets)}")

        for ms in multisets:
            binary_procs = [p for p in range(n) if ms[p] == 2]
            prod = 1
            for m in ms:
                prod *= m

            # Generate words via DFS (only ±1 steps)
            words_dfs = generate_words_dfs(n, ms, max_results=3000, timeout=10)
            # Also shuffle
            words_shuf = generate_words_by_shuffle(n, ms, num_trials=3000)
            all_words_raw = set(words_dfs) | set(words_shuf)

            # Canonicalize
            unique = {}
            for w in all_words_raw:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w
            all_words = list(unique.values())

            # Classify
            ternary = [p for p in range(n) if ms[p] == 3]
            n_tern = len(ternary)

            n_total = 0
            n_ow_nu = 0
            n_ow_nu_isolated = 0
            example_cycles = []

            for w in all_words:
                wl = list(w)

                if not is_odd_winding(wl, n):
                    continue

                if is_uniform_direction(wl, n):
                    continue

                # Try all transition combos
                for trans_bits in range(1 << n_tern):
                    trans_dir = {}
                    for p in range(n):
                        if ms[p] == 2:
                            trans_dir[p] = 1  # binary always +1
                        else:
                            idx = ternary.index(p)
                            trans_dir[p] = 1 if not ((trans_bits >> idx) & 1) else -1

                    configs = build_configs(wl, n, ms, trans_dir)
                    if configs is None:
                        continue

                    n_total += 1
                    n_ow_nu += 1

                    # Check isolated binary firing with gap >= 2
                    has_iso = False
                    iso_procs = []
                    for p in binary_procs:
                        fc_w = fire_count(wl, n)
                        if fc_w[p] >= 2 and has_isolated_firings(wl, p):
                            g = min_gap(wl, p)
                            if g is not None and g >= 2:
                                has_iso = True
                                iso_procs.append(p)

                    if has_iso:
                        n_ow_nu_isolated += 1
                        if len(example_cycles) < 3:
                            fc_w = fire_count(wl, n)
                            W = total_displacement(wl, n)
                            dirs = step_directions(wl, n)
                            example_cycles.append({
                                'word': wl,
                                'configs': configs,
                                'fc': fc_w,
                                'W': W,
                                'dirs': dirs,
                                'iso_procs': iso_procs,
                                'trans_dir': dict(trans_dir),
                                'ms': list(ms),
                            })

            grand_total += n_total
            grand_odd_winding_nonuniform += n_ow_nu
            grand_with_isolated += n_ow_nu_isolated

            if n_ow_nu > 0:
                print(f"\n  ms={ms} (prod={prod}, bins={binary_procs})")
                print(f"    Total valid cycles: {n_total}")
                print(f"    Odd-winding non-uniform: {n_ow_nu}")
                print(f"    ... with isolated binary (gap>=2): {n_ow_nu_isolated}")

                for ex in example_cycles[:2]:
                    print(f"    Example: word={ex['word'][:20]}{'...' if len(ex['word'])>20 else ''}")
                    print(f"      fc={ex['fc']}, W={ex['W']}, iso_procs={ex['iso_procs']}")
                    cw = sum(1 for d in ex['dirs'] if d > 0)
                    ccw = sum(1 for d in ex['dirs'] if d < 0)
                    print(f"      CW steps={cw}, CCW steps={ccw}")

    print(f"\n{'='*70}")
    print(f"GRAND TOTALS:")
    print(f"  Total valid good cycles examined: {grand_total}")
    print(f"  Odd-winding non-uniform: {grand_odd_winding_nonuniform}")
    print(f"  ... with isolated binary (gap>=2): {grand_with_isolated}")
    print("=" * 70)


if __name__ == '__main__':
    main()
