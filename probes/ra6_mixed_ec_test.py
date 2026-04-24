#!/usr/bin/env python3
"""
RA6 Investigation 2+4: Definitive test — can ANY good cycle on mixed rings
avoid entry conflict while being ring-adjacent and hfull?

Strategy:
1. Enumerate ring-adjacent mover words (all consecutive movers neighbors on ring)
2. For each word, try ALL state-sequence combos (incrementing transitions)
3. Check entry conflict

For n=9 this is large, so we also do n=5,6,7 exhaustively first.
"""
from itertools import product as iproduct
from collections import defaultdict
import sys
import time

def enumerate_ring_adj_words(n, ms, max_cl):
    """Enumerate all ring-adjacent mover words where:
    - Each proc fires fc[p] times with fc[p] % ms[p] == 0 and fc[p] > 0
    - Consecutive movers are ring-adjacent
    - Word closes (last->first also ring-adjacent)
    Returns list of (word, fc_dict).
    Uses DFS with pruning."""
    results = []

    # Minimum total fires
    min_fires = sum(ms)  # each fires at least ms[p] times

    def dfs(word, fc, steps):
        if steps > max_cl:
            return
        # Check if we can close
        if steps >= min_fires:
            # Check closure: all fc divisible by ms
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                # Check ring-adjacency of wrap-around
                if abs(word[-1] - word[0]) % n in (1, n-1):
                    results.append(tuple(word))
                    return  # Don't extend further (minimal length)

        # Pruning: remaining steps
        remaining = max_cl - steps
        needed = sum(max(0, ms[p] - fc[p]) if fc[p] == 0 or fc[p] % ms[p] != 0
                      else 0 for p in range(n))
        if needed > remaining:
            return

        last = word[-1]
        for nxt in [(last + 1) % n, (last - 1) % n]:
            fc[nxt] += 1
            word.append(nxt)
            dfs(word, fc, steps + 1)
            word.pop()
            fc[nxt] -= 1

    for start in range(n):
        fc = [0] * n
        fc[start] = 1
        dfs([start], fc, 1)

    # Deduplicate by rotation
    unique = set()
    result = []
    for w in results:
        L = len(w)
        best = w
        for i in range(L):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique:
            unique.add(best)
            result.append(list(best))
    return result


def enumerate_state_sequences(m, k):
    """All sequences of length k+1 starting and ending at 0, with consecutive different,
    values in {0,...,m-1}. Represents a processor firing k times starting from state 0."""
    if k == 0:
        return [[0]]
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(list(seq))
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


def check_ec_for_word(word, ms, n):
    """Check entry conflict for ALL valid state-sequence combos.
    Returns (total_valid, total_with_ec, conflict_free_examples)."""
    L = len(word)
    fc = [0] * n
    for p in word:
        fc[p] += 1

    # Get all state sequences per proc
    proc_seqs = {}
    for p in range(n):
        proc_seqs[p] = enumerate_state_sequences(ms[p], fc[p])
        if not proc_seqs[p]:
            return 0, 0, []  # No valid sequences

    total_valid = 0
    total_ec = 0
    cf_examples = []

    for combo in iproduct(*(proc_seqs[p] for p in range(n))):
        ss = {p: combo[p] for p in range(n)}

        # Build configs
        fcc = [0] * n
        configs = [tuple(ss[p][0] for p in range(n))]
        for t in range(L):
            fcc[word[t]] += 1
            configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
        if configs[-1] != configs[0]:
            continue
        if len(set(configs[:L])) != L:
            continue

        total_valid += 1
        good = configs[:L]

        # Check EC
        mover_triples = defaultdict(set)
        nonmover_triples = defaultdict(set)
        for t in range(L):
            c = good[t]
            mover = word[t]
            for j in range(n):
                Lp = (j-1) % n
                Rp = (j+1) % n
                triple = (c[Lp], c[j], c[Rp])
                if j == mover:
                    mover_triples[j].add(triple)
                else:
                    nonmover_triples[j].add(triple)

        has_ec = False
        for j in range(n):
            overlap = mover_triples[j] & nonmover_triples[j]
            if overlap:
                has_ec = True
                break

        if has_ec:
            total_ec += 1
        else:
            cf_examples.append((combo, word))
            if len(cf_examples) <= 3:
                pass  # Keep a few examples

    return total_valid, total_ec, cf_examples


def main():
    print("RA6 Investigation 2+4: Entry Conflict on Mixed Rings")
    print("=" * 70)

    # Small n first for exhaustive check
    test_configs = [
        (5, [2,3,2,3,3], "n=5 non-consec binary"),
        (5, [3,2,3,2,3], "n=5 alternating"),
        (6, [2,3,2,3,3,3], "n=6 non-consec binary"),
        (6, [2,3,3,2,3,3], "n=6 non-consec binary v2"),
        (7, [2,3,2,3,2,3,3], "n=7 3 non-consec binary"),
        (7, [3,2,3,2,3,2,3], "n=7 alternating"),
    ]

    for n, ms, label in test_configs:
        print(f"\n{'='*70}")
        print(f"{label}: ms={ms}, n={n}, product={eval('*'.join(map(str,ms)))}")
        print(f"  Threshold: 4*3^{n-2} = {4*3**(n-2)}")
        prod = 1
        for m in ms:
            prod *= m
        sub = "SUB-THRESHOLD" if prod < 4*3**(n-2) else "AT/ABOVE THRESHOLD"
        print(f"  Product={prod}: {sub}")

        # min CL = sum(ms) since each fires at least ms[p] times
        min_cl = sum(ms)
        max_cl = min_cl + 6  # Allow some extra
        print(f"  Min CL={min_cl}, searching up to CL={max_cl}")

        t0 = time.time()
        words = enumerate_ring_adj_words(n, ms, max_cl)
        t1 = time.time()
        print(f"  Found {len(words)} ring-adjacent words in {t1-t0:.1f}s")

        if not words:
            print(f"  No words found — trying larger max_cl")
            max_cl = min_cl + 12
            words = enumerate_ring_adj_words(n, ms, max_cl)
            print(f"  Found {len(words)} words with max_cl={max_cl}")

        total_words = len(words)
        total_valid_all = 0
        total_ec_all = 0
        total_cf_all = 0

        for i, word in enumerate(words):
            tv, tec, cf = check_ec_for_word(word, ms, n)
            total_valid_all += tv
            total_ec_all += tec
            total_cf_all += len(cf)
            if cf:
                print(f"  *** CONFLICT-FREE found! word={word[:20]}... ({len(cf)} combos)")

        t2 = time.time()
        print(f"  Results: {total_words} words, {total_valid_all} valid combos, "
              f"{total_ec_all} with EC, {total_cf_all} conflict-free")
        print(f"  Time: {t2-t1:.1f}s")
        if total_cf_all == 0:
            print(f"  CONCLUSION: ALL valid good cycles have EC for {label}")
        else:
            print(f"  *** WARNING: {total_cf_all} conflict-free cycles found!")

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print("If all tests show 0 conflict-free: 3-arc obstruction holds for mixed rings.")
    print("Done.")


if __name__ == "__main__":
    main()
