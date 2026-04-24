#!/usr/bin/env python3
"""
ra14_ec_anatomy.py — Analyze WHERE structural entry conflicts occur.

For each EC found: which processor p? Is p binary or ternary?
What are the neighbor types? What are the residue values?
What is the cycle length vs residue space size?

Goal: find the pattern that leads to a proof.
"""
import time
from itertools import combinations
from collections import Counter, defaultdict


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


def gen_words(n, fc_target, max_results=500, timeout_s=15):
    target_cl = sum(fc_target)
    results = []
    t0 = time.time()

    def dfs(word, fc):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == fc_target[p] for p in range(n)):
                results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, fc_target[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in [(last + 1) % n, (last - 1) % n]:
            if fc[nxt] < fc_target[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1

    for start in range(n):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            break
        fc = [0] * n
        fc[start] = 1
        if fc[start] <= fc_target[start]:
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


def has_no_triple(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


def analyze_ec(word, n, ms):
    """
    Find ALL entry conflicts and return detailed info about each.
    """
    L = len(word)
    results = []

    for p in range(n):
        lp = (p - 1) % n
        rp = (p + 1) % n

        pfc_lp = [0] * (L + 1)
        pfc_p = [0] * (L + 1)
        pfc_rp = [0] * (L + 1)
        for t in range(L):
            pfc_lp[t + 1] = pfc_lp[t] + (1 if word[t] == lp else 0)
            pfc_p[t + 1] = pfc_p[t] + (1 if word[t] == p else 0)
            pfc_rp[t + 1] = pfc_rp[t] + (1 if word[t] == rp else 0)

        mover_steps = [t for t in range(L) if word[t] == p]
        nonmover_steps = [t for t in range(L) if word[t] != p]

        for s1 in mover_steps:
            for s2 in nonmover_steps:
                if (pfc_lp[s1] % ms[lp] == pfc_lp[s2] % ms[lp] and
                    pfc_p[s1] % ms[p] == pfc_p[s2] % ms[p] and
                    pfc_rp[s1] % ms[rp] == pfc_rp[s2] % ms[rp]):
                    res_triple = (pfc_lp[s1] % ms[lp], pfc_p[s1] % ms[p], pfc_rp[s1] % ms[rp])
                    results.append({
                        'p': p,
                        'p_type': 'B' if ms[p] == 2 else 'T',
                        'lp_type': 'B' if ms[lp] == 2 else 'T',
                        'rp_type': 'B' if ms[rp] == 2 else 'T',
                        'neighbor_sig': f"{'B' if ms[lp]==2 else 'T'}-{'B' if ms[p]==2 else 'T'}-{'B' if ms[rp]==2 else 'T'}",
                        's1': s1, 's2': s2,
                        'res_triple': res_triple,
                        'space_size': ms[lp] * ms[p] * ms[rp],
                        'fc_p': sum(1 for t in range(L) if word[t] == p),
                        'mover_at_s2': word[s2],
                        'dist_s1_s2': (s2 - s1) % L,
                    })
    return results


def main():
    print("RA14: Entry Conflict Anatomy")
    print("=" * 70)

    # Counters
    ec_by_proc_type = Counter()
    ec_by_neighbor_sig = Counter()
    ec_by_space_size = Counter()
    ec_at_binary = 0
    ec_at_ternary = 0
    words_with_binary_ec = 0
    words_with_ternary_only_ec = 0
    total_words = 0

    # Track: for each word, what's the MINIMUM space-size EC?
    min_space_sizes = []

    # Track: is there always an EC at a binary proc?
    always_binary_ec = True

    # Detailed per-word analysis for small n
    for n in [5, 7]:
        threshold = 4 * (3 ** (n - 2))
        print(f"\nn={n}, threshold={threshold}")
        print("-" * 50)

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

            fc_target = list(ms)  # minimum fc
            words = gen_words(n, fc_target, max_results=300, timeout_s=8)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            for w in unique.values():
                wl = list(w)
                W = total_displacement(wl, n)
                if abs(W) != n:
                    continue
                dirs = step_directions(wl, n)
                ns = [d for d in dirs if d != 0]
                if not ns or all(d == ns[0] for d in ns):
                    continue

                total_words += 1
                ecs = analyze_ec(wl, n, ms)
                if not ecs:
                    print(f"  NO EC! ms={ms}, word={wl}")
                    always_binary_ec = False
                    continue

                has_binary = False
                has_ternary_only = True
                min_space = 999
                for ec in ecs:
                    ec_by_proc_type[ec['p_type']] += 1
                    ec_by_neighbor_sig[ec['neighbor_sig']] += 1
                    ec_by_space_size[ec['space_size']] += 1
                    if ec['p_type'] == 'B':
                        has_binary = True
                        has_ternary_only = False
                        ec_at_binary += 1
                    else:
                        ec_at_ternary += 1
                    min_space = min(min_space, ec['space_size'])

                min_space_sizes.append(min_space)
                if has_binary:
                    words_with_binary_ec += 1
                else:
                    words_with_ternary_only_ec += 1
                    if n <= 7:
                        # Print first few to understand
                        ec0 = ecs[0]
                        print(f"  Ternary-only EC: ms={ms}, p={ec0['p']}, "
                              f"sig={ec0['neighbor_sig']}, space={ec0['space_size']}, "
                              f"fc_p={ec0['fc_p']}, CL={len(wl)}")
                        always_binary_ec = False

    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"Total OW-NU words analyzed: {total_words}")
    print(f"\nEC by processor type:")
    for k, v in ec_by_proc_type.most_common():
        print(f"  {k}: {v}")
    print(f"\nEC by neighbor signature (L-P-R):")
    for k, v in ec_by_neighbor_sig.most_common():
        print(f"  {k}: {v}")
    print(f"\nEC by space size:")
    for k, v in ec_by_space_size.most_common():
        print(f"  {k}: {v}")
    print(f"\nWords with EC at a binary proc: {words_with_binary_ec}")
    print(f"Words with EC only at ternary: {words_with_ternary_only_ec}")
    print(f"Always has binary EC: {always_binary_ec}")
    if min_space_sizes:
        print(f"\nMin space size per word: min={min(min_space_sizes)}, max={max(min_space_sizes)}, "
              f"mean={sum(min_space_sizes)/len(min_space_sizes):.1f}")

    # Key question: for binary p, space = m_L * 2 * m_R
    # With non-consecutive binary: both neighbors are ternary
    # So space = 3 * 2 * 3 = 18 for binary p
    # CL = sum(fc) = sum(ms) for mult=1
    # n=5: CL = 2+3+2+3+2 = 12 < 18. Pigeonhole fails!
    # But does the SPECIFIC structure of OW-NU words force it?
    print(f"\n{'='*70}")
    print("PIGEONHOLE ANALYSIS")
    for n in [5, 7, 9]:
        # Non-consecutive 3-binary: all binary have ternary neighbors
        # Binary space = 3*2*3 = 18
        # CL with mult=1: 3*2 + (n-3)*3 = 6 + 3n - 9 = 3n - 3
        cl = 3*2 + (n-3)*3
        print(f"  n={n}: CL={cl}, binary space=18, pigeonhole={'YES' if cl > 18 else 'NO'} (CL {'>' if cl > 18 else '<='} 18)")


if __name__ == '__main__':
    main()
