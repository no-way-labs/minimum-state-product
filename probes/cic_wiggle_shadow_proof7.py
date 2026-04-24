#!/usr/bin/env python3
"""
CIC Exploration 13g: Generalize shadow to ALL wiggle word forms.

The {1,2}-wiggle CCW canonical form is proved. Now check:
1. Other wiggle positions (same binary placement)
2. CW direction
3. Different binary placements
4. Higher state counts (m=4, m=5)

Key question: do ALL wiggle words have a shadow cycle with the SAME
structure (σ/Δ/offset can differ per word form, but all 5 properties hold)?
"""

from itertools import product as iproduct
from collections import Counter
import sys


def generate_wiggle_words(n, binary_positions):
    binary_set = set(binary_positions)
    words = set()
    for direction in [+1, -1]:
        base = [(i * direction) % n for i in range(2 * n)]
        for insert_pos in range(2 * n):
            p = base[insert_pos]
            next_p = base[(insert_pos + 1) % (2 * n)]
            step = (next_p - p) % n
            if step == 1:
                bounce = (p - 1) % n
            elif step == n - 1:
                bounce = (p + 1) % n
            else:
                continue
            if p in binary_set or bounce in binary_set:
                continue
            word = (list(base[:insert_pos + 1]) + [bounce, p]
                    + list(base[insert_pos + 1:]))
            L = len(word)
            valid = True
            for i in range(L):
                diff = abs(word[i] - word[(i + 1) % L])
                if diff != 1 and diff != n - 1:
                    valid = False
                    break
            if not valid:
                continue
            mc = Counter(word)
            if not all(mc.get(q, 0) >= 2 for q in range(n)):
                continue
            if not all(mc.get(b, 0) % 2 == 0 for b in binary_positions):
                continue
            min_idx = word.index(min(word))
            rotated = word[min_idx:] + word[:min_idx]
            words.add(tuple(rotated))
    return [list(w) for w in sorted(words)]


def get_fire_counts(word, n):
    fc = [0] * n
    for p in word:
        fc[p] += 1
    return fc


def enumerate_state_sequences(n, ms, fire_counts):
    proc_sequences = {}
    for p in range(n):
        m = ms[p]
        k = fire_counts[p]
        seqs = []

        def dfs_seq(seq, remaining, m_val=m):
            if remaining == 0:
                if seq[-1] == 0:
                    seqs.append(list(seq))
                return
            current = seq[-1]
            for next_val in range(m_val):
                if next_val != current:
                    if remaining == 1 and next_val != 0:
                        continue
                    seq.append(next_val)
                    dfs_seq(seq, remaining - 1, m_val)
                    seq.pop()

        dfs_seq([0], k)
        proc_sequences[p] = seqs
    return proc_sequences


def compute_waterfall(word, n):
    L = len(word)
    g = [[0] * (L + 1) for _ in range(n)]
    for t in range(L):
        for j in range(n):
            g[j][t + 1] = g[j][t]
        g[word[t]][t + 1] = g[word[t]][t] + 1
    return g


def extract_shadow_and_check(word, n, ms, ss, fc, g):
    """Extract shadow via SCC trace, check 5 properties."""
    L = len(word)

    fcc = [0] * n
    configs = [tuple(ss[p][0] for p in range(n))]
    for t in range(L):
        fcc[word[t]] += 1
        configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:L])) != L:
        return None

    good = configs[:L]
    good_set = set(good)

    me = {}
    for t in range(L):
        c = good[t]
        cn = good[(t + 1) % L]
        m = word[t]
        key = (m, c[(m - 1) % n], c[m], c[(m + 1) % n])
        me[key] = cn[m]

    # SCC trace
    all_cfgs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_cfgs if c not in good_set]

    for start in non_good:
        config = start
        path = [config]
        visited = {config: 0}
        movers = []

        for step in range(L + 50):
            forced = []
            for j in range(n):
                key = (j, config[(j - 1) % n], config[j],
                       config[(j + 1) % n])
                if key in me and me[key] != config[j]:
                    forced.append((j, me[key], key))
            if not forced:
                break

            moved = False
            for proc, new_val, key in forced:
                nc = list(config)
                nc[proc] = new_val
                nc = tuple(nc)
                if nc not in good_set:
                    movers.append(proc)
                    config = nc
                    path.append(config)
                    if config in visited:
                        cs = visited[config]
                        if len(movers[cs:]) == L:
                            shadow = path[cs:-1]
                            shadow_movers = movers[cs:]

                            # Check 5 properties
                            p3 = len(set(shadow)) == L
                            p4 = len(set(shadow) & good_set) == 0

                            p5 = True
                            for tt in range(L):
                                sc = shadow[tt]
                                for jj in range(n):
                                    kk = (jj, sc[(jj - 1) % n],
                                          sc[jj], sc[(jj + 1) % n])
                                    if kk in me and me[kk] != sc[jj]:
                                        ncc = list(sc)
                                        ncc[jj] = me[kk]
                                        if tuple(ncc) in good_set:
                                            p5 = False

                            return p3 and p4 and p5
                    visited[config] = step + 1
                    moved = True
                    break
            if not moved:
                break

    return False


def main():
    print("CIC Exploration 13g: Generalize to All Wiggle Word Forms")
    print("=" * 70)

    # PART 1: All wiggle words at n=7,8,9 with ternary states
    print("\nPART 1: All Wiggle Words (ternary, n=7..9)")
    print("-" * 70)

    test_configs = [
        (7, [0, 2, 4]),
        (8, [0, 3, 6]),
        (8, [0, 2, 5]),
        (9, [0, 3, 6]),
        (9, [0, 2, 5]),
    ]

    for n, bp in test_configs:
        bs = set(bp)
        ms = [2 if i in bs else 3 for i in range(n)]
        words = generate_wiggle_words(n, bp)

        total_valid = 0
        total_shadow = 0

        for w in words:
            fc = get_fire_counts(w, n)
            g = compute_waterfall(w, n)
            proc_seqs = enumerate_state_sequences(n, ms, fc)
            sl = [proc_seqs[p] for p in range(n)]

            for combo in iproduct(*sl):
                ss = {p: combo[p] for p in range(n)}
                result = extract_shadow_and_check(w, n, ms, ss, fc, g)
                if result is None:
                    continue
                total_valid += 1
                if result:
                    total_shadow += 1

        tag = '✓' if total_shadow == total_valid and total_valid > 0 else '✗'
        print(f"  n={n} bp={bp}: {total_shadow}/{total_valid} "
              f"({len(words)} words) {tag}")

    # PART 2: Quaternary states
    print("\n\nPART 2: Quaternary States (m=4)")
    print("-" * 70)

    for n, bp in [(7, [0, 2, 4]), (8, [0, 3, 6])]:
        bs = set(bp)
        ms = [2 if i in bs else 4 for i in range(n)]
        words = generate_wiggle_words(n, bp)

        total_valid = 0
        total_shadow = 0

        for w in words[:2]:  # first 2 words only (combinatorial explosion)
            fc = get_fire_counts(w, n)
            g = compute_waterfall(w, n)
            proc_seqs = enumerate_state_sequences(n, ms, fc)
            sl = [proc_seqs[p] for p in range(n)]

            for combo in iproduct(*sl):
                ss = {p: combo[p] for p in range(n)}
                result = extract_shadow_and_check(w, n, ms, ss, fc, g)
                if result is None:
                    continue
                total_valid += 1
                if result:
                    total_shadow += 1

        tag = '✓' if total_shadow == total_valid and total_valid > 0 else '✗'
        print(f"  n={n} bp={bp} m=4: {total_shadow}/{total_valid} {tag}")

    # PART 3: Larger n (first word only, first combo only)
    print("\n\nPART 3: Larger n (ternary, first word/combo)")
    print("-" * 70)

    large_configs = [
        (10, [0, 4, 7]),
        (11, [0, 4, 8]),
        (12, [0, 4, 8]),
        (13, [0, 5, 9]),
        (14, [0, 5, 10]),
        (15, [0, 5, 10]),
    ]

    for n, bp in large_configs:
        bs = set(bp)
        ms = [2 if i in bs else 3 for i in range(n)]
        words = generate_wiggle_words(n, bp)
        if not words:
            continue

        total_valid = 0
        total_shadow = 0

        for w in words[:4]:  # first 4 words
            fc = get_fire_counts(w, n)
            g = compute_waterfall(w, n)
            proc_seqs = enumerate_state_sequences(n, ms, fc)
            sl = [proc_seqs[p] for p in range(n)]

            for combo in iproduct(*sl):
                ss = {p: combo[p] for p in range(n)}
                result = extract_shadow_and_check(w, n, ms, ss, fc, g)
                if result is None:
                    continue
                total_valid += 1
                if result:
                    total_shadow += 1
                break  # first valid combo only

        tag = '✓' if total_shadow == total_valid and total_valid > 0 else '✗'
        print(f"  n={n} bp={bp}: {total_shadow}/{total_valid} "
              f"(first combos) {tag}")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
