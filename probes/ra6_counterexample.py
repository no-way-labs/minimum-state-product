#!/usr/bin/env python3
"""
RA6: Deep analysis of the CF counterexample at n=9, ms=[2,3,3,2,3,3,2,3,3].

This multiset has 3 non-consecutive binary at positions {0,3,6} and
product = 2^3 * 3^6 = 5832 < 8748 = 4*3^7 (SUB-THRESHOLD).

The biased random search found CF cycles with word starting
[8,7,8,7,6,5,4,5,4,3,2,1,2,1,0...].

Questions:
1. What is the full word?
2. What does the cycle look like?
3. Is it really conflict-free?
4. Does it use incrementing transitions? What about other transitions?
5. Is this a true counterexample to universal EC?
"""
from collections import defaultdict
import time

def build_good_cycle_inc(word, ms, n):
    """Build good cycle with incrementing transition."""
    L = len(word)
    configs = [[0]*n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + 1) % ms[p]
        configs.append(c)
    if configs[-1] != configs[0]:
        return None
    if len(set(tuple(c) for c in configs[:L])) != L:
        return None
    return [tuple(c) for c in configs[:L]]


def check_ec_detailed(good, word, n, ms):
    """Detailed EC check with per-proc info."""
    L = len(word)
    mover_triples = defaultdict(set)
    nonmover_triples = defaultdict(set)
    mover_entries = {}   # (proc, L, S, R) -> new_val
    nonmover_entries = defaultdict(set)  # (proc, L, S, R) -> set of S

    for t in range(L):
        c = good[t]
        cn = good[(t+1)%L]
        mover = word[t]
        for j in range(n):
            Lp = (j-1)%n; Rp = (j+1)%n
            triple = (c[Lp], c[j], c[Rp])
            if j == mover:
                mover_triples[j].add(triple)
                mover_entries[(j, c[Lp], c[j], c[Rp])] = cn[j]
            else:
                nonmover_triples[j].add(triple)
                nonmover_entries[(j, c[Lp], c[j], c[Rp])].add(c[j])

    conflicts = {}
    for j in range(n):
        overlap = mover_triples[j] & nonmover_triples[j]
        if overlap:
            conflicts[j] = overlap
    return conflicts, mover_triples, nonmover_triples, mover_entries


def biased_random_word_v2(n, ms, attempts=1000):
    """Generate ring-adjacent words. Returns full word."""
    import random
    target_fc = list(ms)
    total_fires = sum(target_fc)

    for _ in range(attempts):
        fc = [0]*n
        start = random.randint(0, n-1)
        word = [start]
        fc[start] = 1

        for step in range(total_fires - 1):
            last = word[-1]
            neighbors = [(last+1)%n, (last-1)%n]
            random.shuffle(neighbors)
            scores = []
            for nxt in neighbors:
                need = max(0, target_fc[nxt] - fc[nxt])
                scores.append((need, nxt))
            scores.sort(reverse=True)
            if scores[0][0] > 0:
                nxt = scores[0][1]
            elif scores[1][0] > 0:
                nxt = scores[1][1]
            else:
                nxt = random.choice(neighbors)
            word.append(nxt)
            fc[nxt] += 1

        if all(fc[p] >= target_fc[p] and fc[p] % ms[p] == 0 for p in range(n)):
            if abs(word[-1] - word[0]) % n in (1, n-1):
                return word
    return None


def main():
    print("RA6: Counterexample Deep Analysis")
    print("=" * 70)

    n = 9
    ms = [2,3,3,2,3,3,2,3,3]
    prod = 1
    for m in ms:
        prod *= m
    thresh = 4*3**(n-2)
    print(f"n={n}, ms={ms}")
    print(f"Product={prod}, threshold={thresh}")
    print(f"Sub-threshold: {prod < thresh}")
    print(f"Binary positions: {[p for p in range(n) if ms[p]==2]}")
    bin_pos = [p for p in range(n) if ms[p]==2]
    consec = any(abs(bin_pos[i]-bin_pos[j])%n in (1,n-1) for i in range(len(bin_pos)) for j in range(i+1,len(bin_pos)))
    print(f"Binary consecutive: {consec}")
    print()

    # Find CF cycles
    print("--- Finding conflict-free cycles ---")
    import random
    random.seed(42)

    cf_words = []
    ec_words = []
    total_valid = 0

    for trial in range(10000):
        word = biased_random_word_v2(n, ms, attempts=5)
        if word is None:
            continue
        good = build_good_cycle_inc(word, ms, n)
        if good is None:
            continue
        total_valid += 1
        conflicts, mt, nmt, me = check_ec_detailed(good, word, n, ms)
        if not conflicts:
            cf_words.append((word, good))
        else:
            ec_words.append((word, good, conflicts))

    print(f"Total valid cycles: {total_valid}")
    print(f"Conflict-free: {len(cf_words)}")
    print(f"With EC: {len(ec_words)}")
    print(f"CF rate: {100*len(cf_words)/total_valid:.1f}%")
    print()

    # Analyze CF cycles
    if cf_words:
        print("--- CF Cycle Details ---\n")
        # Show first few
        seen_words = set()
        unique_cf = []
        for word, good in cf_words:
            wt = tuple(word)
            if wt not in seen_words:
                seen_words.add(wt)
                unique_cf.append((word, good))

        print(f"Unique CF words: {len(unique_cf)}")
        for idx, (word, good) in enumerate(unique_cf[:5]):
            L = len(word)
            fc = [0]*n
            for p in word:
                fc[p] += 1

            # Direction pattern
            dirs = []
            for i in range(L):
                d = (word[(i+1)%L] - word[i]) % n
                dirs.append('+' if d == 1 else '-')

            print(f"\n  CF Cycle {idx+1}:")
            print(f"    Word: {word}")
            print(f"    CL={L}, fc={fc}")
            print(f"    Dirs: {''.join(dirs)}")

            # Is it a wiggle pattern?
            # Count direction changes
            changes = sum(1 for i in range(L) if dirs[i] != dirs[(i+1)%L])
            print(f"    Direction changes: {changes}")

            # Show configs
            for t in range(L):
                c = good[t]
                m = word[t]
                print(f"      t={t:2d}: {c} mover={m}(m={ms[m]})")

            # Per-proc mover/nonmover triple counts
            mt_count = defaultdict(int)
            nmt_count = defaultdict(int)
            for t in range(L):
                c = good[t]
                mover = word[t]
                for j in range(n):
                    if j == mover:
                        mt_count[j] += 1
                    else:
                        nmt_count[j] += 1

            print(f"    Per-proc: mover_fires={[mt_count[j] for j in range(n)]}, "
                  f"nonmover_steps={[nmt_count[j] for j in range(n)]}")

            # Verify no EC
            conflicts, _, _, _ = check_ec_detailed(good, word, n, ms)
            print(f"    EC verification: {'PASS (no EC)' if not conflicts else 'FAIL (has EC at ' + str(list(conflicts.keys())) + ')'}")

    # Check: is this just because of incrementing transition?
    # The non-consecutive binary arrangement [2,3,3,2,3,3,2,3,3] has
    # a special structure: 3 copies of [2,3,3]
    print("\n--- Structural Analysis ---")
    print(f"ms has period-3 structure: [2,3,3] repeated 3 times")
    print(f"Binary at positions {bin_pos} = every 3rd position")
    print(f"Gap between binaries = 3 (not adjacent)")

    # Compare with other 3-binary arrangements
    print("\n--- Compare with [2,3,2,3,2,3,3,3,3] ---")
    ms2 = [2,3,2,3,2,3,3,3,3]
    random.seed(42)
    cf2 = 0
    ec2 = 0
    for trial in range(10000):
        word = biased_random_word_v2(n, ms2, attempts=5)
        if word is None:
            continue
        good = build_good_cycle_inc(word, ms2, n)
        if good is None:
            continue
        conflicts, _, _, _ = check_ec_detailed(good, word, n, ms2)
        if not conflicts:
            cf2 += 1
        else:
            ec2 += 1
    print(f"ms={ms2}: valid={cf2+ec2}, CF={cf2}, EC={ec2}")

    # And the third arrangement
    print("\n--- Compare with [3,2,3,3,2,3,3,2,3] ---")
    ms3 = [3,2,3,3,2,3,3,2,3]
    random.seed(42)
    cf3 = 0
    ec3 = 0
    for trial in range(10000):
        word = biased_random_word_v2(n, ms3, attempts=5)
        if word is None:
            continue
        good = build_good_cycle_inc(word, ms3, n)
        if good is None:
            continue
        conflicts, _, _, _ = check_ec_detailed(good, word, n, ms3)
        if not conflicts:
            cf3 += 1
        else:
            ec3 += 1
    print(f"ms={ms3}: valid={cf3+ec3}, CF={cf3}, EC={ec3}")

    # KEY: also check at n=7 with same periodic structure
    print("\n--- Check n=7 with [2,3,3,2,3,3,3] ---")
    ms7 = [2,3,3,2,3,3,3]
    n7 = 7
    random.seed(42)
    cf7 = 0
    ec7 = 0
    for trial in range(10000):
        word = biased_random_word_v2(n7, ms7, attempts=5)
        if word is None:
            continue
        good = build_good_cycle_inc(word, ms7, n7)
        if good is None:
            continue
        conflicts, _, _, _ = check_ec_detailed(good, word, n7, ms7)
        if not conflicts:
            cf7 += 1
        else:
            ec7 += 1
    print(f"ms={ms7}: valid={cf7+ec7}, CF={cf7}, EC={ec7}")
    if cf7 > 0:
        print("  CF also found at n=7!")
    else:
        print("  No CF at n=7")

    print("\nDone.")


if __name__ == "__main__":
    main()
