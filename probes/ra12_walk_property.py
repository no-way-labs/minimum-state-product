#!/usr/bin/env python3
"""
RA12: Understand WHY the 8 ring walks are EC-free.

Key question: is the EC-free property due to:
(a) Ring-walk structure (adjacent movers)
(b) Specific permutation pattern
(c) Something else

Test: take the 8 EC-free words and perturb them slightly
(swap two movers). Does EC appear?

Also test: permutations of the same mover words that are NOT ring walks.
"""

from itertools import product as iproduct
from collections import Counter
import random
import time


def make_ms(n, binary_positions):
    ms = [3] * n
    for b in binary_positions:
        ms[b] = 2
    return ms


def enumerate_state_sequences(m, k):
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(tuple(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0:
                    continue
                seq.append(nv)
                dfs(seq, remaining - 1)
                seq.pop()
    dfs([0], k)
    return seqs


def check_ec_rate(word, n, ms):
    """Check what fraction of valid combos have EC."""
    L = len(word)
    fc = [0] * n
    for p in word:
        fc[p] += 1

    proc_seqs = {p: enumerate_state_sequences(ms[p], fc[p]) for p in range(n)}
    sl = [proc_seqs[p] for p in range(n)]

    total = 0
    ec_count = 0

    for combo in iproduct(*sl):
        ss = {p: combo[p] for p in range(n)}
        fcc = [0] * n
        configs = [tuple(ss[p][0] for p in range(n))]
        for t in range(L):
            fcc[word[t]] += 1
            configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
        if configs[-1] != configs[0]:
            continue
        if len(set(configs[:L])) != L:
            continue
        total += 1
        good = configs[:L]

        has_conflict = False
        for j in range(n):
            Lp = (j - 1) % n
            Rp = (j + 1) % n
            mc = set()
            nc = set()
            for t in range(L):
                ctx = (good[t][Lp], good[t][j], good[t][Rp])
                if word[t] == j:
                    nv = good[(t + 1) % L][j]
                    if nv != ctx[1]:
                        mc.add(ctx)
                else:
                    nc.add(ctx)
            if mc & nc:
                has_conflict = True
                break
        if has_conflict:
            ec_count += 1

    return total, ec_count


def enumerate_walks(n, ms):
    total_len = sum(ms)
    walks = []
    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == total_len:
            nxt = path[0]
            if abs(pos - nxt) % n in (1, n - 1):
                if all(fc[p] == ms[p] for p in range(n)):
                    walks.append(tuple(path))
            return
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] < ms[nxt]:
                fc[nxt] += 1
                path.append(nxt)
                dfs(path, fc)
                path.pop()
                fc[nxt] -= 1
    for p0 in range(n):
        fc = [0] * n
        fc[p0] = 1
        dfs([p0], fc)
    unique = set()
    result = []
    for w in walks:
        ell = len(w)
        best = w
        for i in range(ell):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique:
            unique.add(best)
            result.append(w)
    return result


def is_ring_walk(word, n):
    """Check if word is a valid ring walk (adjacent movers)."""
    for i in range(len(word) - 1):
        if abs(word[i] - word[i+1]) % n not in (1, n-1):
            return False
    # Check wrap
    if abs(word[-1] - word[0]) % n not in (1, n-1):
        return False
    return True


def main():
    n = 9
    ms = make_ms(n, (0, 3, 6))
    random.seed(42)

    print("=" * 70)
    print("RA12: Why are the 8 walks EC-free?")
    print("=" * 70)

    # Get the 8 EC-free walks
    walks = enumerate_walks(n, ms)
    ec_free_walks = []
    ec_walks = []
    for word in walks:
        total, ec = check_ec_rate(word, n, ms)
        if ec == 0:
            ec_free_walks.append(word)
        else:
            ec_walks.append(word)

    print(f"\nEC-free walks: {len(ec_free_walks)}")
    print(f"EC walks: {len(ec_walks)}")

    # Test 1: Swap two adjacent positions in an EC-free walk
    print(f"\n{'='*70}")
    print("TEST 1: Perturbation — swap two positions in EC-free walk")
    print(f"{'='*70}")

    word0 = ec_free_walks[0]
    print(f"Original: {list(word0)}")
    total, ec = check_ec_rate(word0, n, ms)
    print(f"  valid={total}, EC={ec}")

    for i in range(len(word0) - 1):
        perturbed = list(word0)
        perturbed[i], perturbed[i+1] = perturbed[i+1], perturbed[i]
        perturbed = tuple(perturbed)
        # Check if fc is still correct
        fc = Counter(perturbed)
        if any(fc[p] != ms[p] for p in range(n)):
            continue
        total, ec = check_ec_rate(perturbed, n, ms)
        if total > 0:
            pct = f"{100*ec/total:.0f}%" if total > 0 else "N/A"
            walk_str = "walk" if is_ring_walk(perturbed, n) else "non-walk"
            if ec < total:
                print(f"  Swap {i},{i+1}: valid={total}, EC={ec} ({pct}), {walk_str}"
                      f" *** SOME EC-FREE ***")
            else:
                print(f"  Swap {i},{i+1}: valid={total}, EC={ec} ({pct}), {walk_str}")

    # Test 2: Random shuffles of the same fc vector
    print(f"\n{'='*70}")
    print("TEST 2: Random shuffles (same fc, not ring walks)")
    print(f"{'='*70}")

    base_fc = list(word0)
    n_free = 0
    n_all_ec = 0
    for trial in range(1000):
        shuffled = base_fc[:]
        random.shuffle(shuffled)
        shuffled = tuple(shuffled)
        total, ec = check_ec_rate(shuffled, n, ms)
        if total > 0:
            if ec < total:
                n_free += 1
                if n_free <= 3:
                    print(f"  Trial {trial}: valid={total}, EC={ec}/{total}, "
                          f"ring_walk={is_ring_walk(shuffled, n)}")
            else:
                n_all_ec += 1

    print(f"\n  1000 trials: {n_free} with some EC-free, {n_all_ec} all-EC")

    # Test 3: What makes the EC-free walks special?
    print(f"\n{'='*70}")
    print("TEST 3: Structural analysis of EC-free vs EC walks")
    print(f"{'='*70}")

    # Compare direction patterns
    print("\nEC-free walk directions:")
    for word in ec_free_walks:
        dirs = []
        for i in range(len(word)):
            d = (word[(i+1) % len(word)] - word[i]) % n
            dirs.append('+' if d == 1 else '-')
        print(f"  {''.join(dirs)}")

    print("\nEC walk directions (first 10):")
    for word in ec_walks[:10]:
        dirs = []
        for i in range(len(word)):
            d = (word[(i+1) % len(word)] - word[i]) % n
            dirs.append('+' if d == 1 else '-')
        total, ec = check_ec_rate(word, n, ms)
        print(f"  {''.join(dirs)}  EC={ec}/{total}")

    # Test 4: What if we use exhaustive enumeration of ALL mover sequences
    # (not just ring walks) for a SMALLER ring?
    print(f"\n{'='*70}")
    print("TEST 4: Exhaustive at smaller n (n=6, equal gaps)")
    print(f"{'='*70}")

    n6 = 6
    ms6 = [2, 3, 2, 3, 2, 3]  # alternating, gaps (2,2,2)
    walks6 = enumerate_walks(n6, ms6)
    print(f"n=6, ms={ms6}: {len(walks6)} ring walks")

    # Check all mover sequences (not just walks)
    # L = sum(ms6) = 15. Sequences with fc = ms6.
    # Number = 15! / (2!*3!*2!*3!*2!*3!) = huge
    # Can't enumerate all. Sample instead.
    L6 = sum(ms6)
    base = []
    for p in range(n6):
        base.extend([p] * ms6[p])
    assert len(base) == L6

    n_free6 = 0
    n_checked6 = 0
    for trial in range(10000):
        shuffled = base[:]
        random.shuffle(shuffled)
        shuffled = tuple(shuffled)
        total, ec = check_ec_rate(shuffled, n6, ms6)
        if total > 0:
            n_checked6 += 1
            if ec < total:
                n_free6 += 1
                if n_free6 <= 3:
                    rw = is_ring_walk(shuffled, n6)
                    print(f"  Trial {trial}: valid={total}, EC={ec}/{total}, "
                          f"ring_walk={rw}")

    print(f"\n  n=6: {n_checked6} checked, {n_free6} with some EC-free")

    # Test 5: The definitive test — among ALL possible mover sequences
    # (not just ring walks), do EC-free cycles exist?
    # We already showed random sampling finds 0 for non-walks.
    # Now confirm: the 8 ring walks are the ONLY EC-free sequences.
    print(f"\n{'='*70}")
    print("TEST 5: Are the 8 ring walks really the ONLY EC-free mover sequences?")
    print(f"{'='*70}")

    # Check a large sample including near-ring-walks
    n_found = 0
    n_total = 0

    # Strategy: start from EC-free walks and make small modifications
    for base_word in ec_free_walks[:2]:
        base_list = list(base_word)
        for trial in range(5000):
            # Randomly swap 2-4 positions
            perturbed = base_list[:]
            n_swaps = random.randint(1, 3)
            for _ in range(n_swaps):
                i = random.randint(0, len(perturbed)-1)
                j = random.randint(0, len(perturbed)-1)
                perturbed[i], perturbed[j] = perturbed[j], perturbed[i]
            perturbed_t = tuple(perturbed)
            # Check fc
            if Counter(perturbed_t) != Counter(base_word):
                continue
            total, ec = check_ec_rate(perturbed_t, n, ms)
            if total > 0:
                n_total += 1
                if ec < total:
                    n_found += 1
                    rw = is_ring_walk(perturbed_t, n)
                    if n_found <= 5:
                        print(f"  EC-free found! ring_walk={rw}, "
                              f"valid={total}, EC={ec}/{total}")

    print(f"\n  {n_total} checked near ring-walks, {n_found} EC-free")
    if n_found == 0:
        print("  Only ring walks are EC-free among tested sequences.")


if __name__ == "__main__":
    main()
