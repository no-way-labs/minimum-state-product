#!/usr/bin/env python3
"""
RA12: Verify entry conflict universality for ALL non-consecutive binary
placements on a 9-ring at sub-threshold product.

For 3 binary processors on n=9:
  - Binary at positions b0, b1, b2 (non-consecutive on ring)
  - Ternary elsewhere
  - Product = 2^3 * 3^6 = 5832 < 8748 = 4*3^7 (sub-threshold)

Approach:
  1. Enumerate ALL mover words (ring walks visiting each proc the right # times)
  2. For each word, enumerate ALL valid state-sequence combos (not just incrementing)
  3. Check entry conflict for each (word, state-sequence) pair

This avoids the "incrementing transition limitation" noted in MEMORY.md.
"""

from itertools import combinations, product as iproduct
from collections import Counter
import time
import sys


def make_ms(n, binary_positions):
    ms = [3] * n
    for b in binary_positions:
        ms[b] = 2
    return ms


def is_non_consecutive(positions, n):
    for i in range(len(positions)):
        for j in range(i + 1, len(positions)):
            if abs(positions[i] - positions[j]) % n in (1, n - 1):
                return False
    return True


def canonical_placement(positions, n):
    best = None
    for r in range(n):
        rotated = tuple(sorted((p + r) % n for p in positions))
        if best is None or rotated < best:
            best = rotated
    return best


def enumerate_placements(n, num_binary):
    seen = set()
    results = []
    for combo in combinations(range(n), num_binary):
        if not is_non_consecutive(combo, n):
            continue
        canon = canonical_placement(combo, n)
        if canon not in seen:
            seen.add(canon)
            positions = sorted(canon)
            gaps = [(positions[(i + 1) % len(positions)] - positions[i]) % n
                    for i in range(len(positions))]
            results.append((canon, tuple(gaps)))
    return results


def enumerate_fc2_walks(n, ms):
    """Enumerate all fc=2 ring walks of length 2n returning to start.
    Each proc fires exactly 2 times. Walk length = 2n.
    This is for binary procs with ms[p]=2. For ternary with ms[p]=3,
    we use fc=3 walks of length sum(ms).
    """
    # Actually we need walks where each proc p fires exactly ms[p] times.
    # Total length = sum(ms).
    total_len = sum(ms)
    walks = []

    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == total_len:
            # Check wrap-around adjacency
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
        if ms[p0] > 0:
            fc = [0] * n
            fc[p0] = 1
            dfs([p0], fc)

    # Deduplicate under cyclic rotation
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
            result.append(list(w))
    return result


def enumerate_state_sequences(m, k):
    """Enumerate all state sequences of length k+1 starting and ending at 0,
    where consecutive values differ, and each value in 0..m-1."""
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


def check_entry_conflicts_allseq(word, n, ms):
    """For a given mover word, check ALL state-sequence combos.
    Returns (total_valid, total_with_ec, conflict_free_combos)."""
    L = len(word)
    fc = [0] * n
    for p in word:
        fc[p] += 1

    # State sequences for each processor
    proc_seqs = {}
    for p in range(n):
        proc_seqs[p] = enumerate_state_sequences(ms[p], fc[p])

    sl = [proc_seqs[p] for p in range(n)]

    total_valid = 0
    total_conflict = 0
    conflict_free = []

    for combo in iproduct(*sl):
        ss = {p: combo[p] for p in range(n)}

        # Build good cycle configs
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

        # Check entry conflict at every processor
        has_conflict = False
        for j in range(n):
            Lp = (j - 1) % n
            Rp = (j + 1) % n
            mover_ctxs = set()
            nonmover_ctxs = set()
            for t in range(L):
                ctx = (good[t][Lp], good[t][j], good[t][Rp])
                if word[t] == j:
                    next_val = good[(t + 1) % L][j]
                    if next_val != ctx[1]:
                        mover_ctxs.add(ctx)
                else:
                    nonmover_ctxs.add(ctx)
            if mover_ctxs & nonmover_ctxs:
                has_conflict = True
                break

        if has_conflict:
            total_conflict += 1
        else:
            conflict_free.append(combo)

    return total_valid, total_conflict, conflict_free


def check_entry_conflicts_inc(word, n, ms):
    """Check EC for incrementing-transition-only cycle."""
    L = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(L):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:L])) != L:
        return None
    cycle = configs[:L]

    for j in range(n):
        Lp = (j - 1) % n
        Rp = (j + 1) % n
        mover_ctxs = set()
        nonmover_ctxs = set()
        for t in range(L):
            ctx = (cycle[t][Lp], cycle[t][j], cycle[t][Rp])
            if word[t] == j:
                next_val = cycle[(t + 1) % L][j]
                if next_val != ctx[1]:
                    mover_ctxs.add(ctx)
            else:
                nonmover_ctxs.add(ctx)
        if mover_ctxs & nonmover_ctxs:
            return True
    return False


def main():
    n = 9
    threshold = 4 * (3 ** 7)  # 8748

    print("=" * 70)
    print("RA12: Non-consecutive binary EC verification at n=9")
    print(f"Threshold product: 4*3^7 = {threshold}")
    print("=" * 70)

    placements_3 = enumerate_placements(n, 3)
    print(f"\n3-binary distinct placements (up to rotation): {len(placements_3)}")
    for pos, gaps in sorted(placements_3, key=lambda x: x[1]):
        ms = make_ms(n, pos)
        product = 1
        for m in ms:
            product *= m
        print(f"  pos={pos}, gaps={gaps}, ms={ms}, product={product}")

    # PHASE 1: Use incrementing transitions first (fast) to find cycles
    # Then use all-state-sequence check for thoroughness
    print(f"\n{'='*70}")
    print("PHASE 1: Enumerate mover words (minimum-length cycles)")
    print(f"{'='*70}")

    # Total length for min cycle: sum(ms) = 3*2 + 6*3 = 24
    total_len = sum(make_ms(n, placements_3[0][0]))
    print(f"Minimum cycle length: {total_len}")
    print(f"(Each binary fires 2x, each ternary fires 3x)")

    # Enumerate walks for each placement
    for pos, gaps in sorted(placements_3, key=lambda x: x[1]):
        ms = make_ms(n, pos)
        print(f"\n--- gaps={gaps}, positions={pos} ---")
        t0 = time.time()
        walks = enumerate_fc2_walks(n, ms)
        t1 = time.time()
        print(f"  Mover words found: {len(walks)} ({t1-t0:.1f}s)")

        if not walks:
            print(f"  WARNING: No valid ring walks of length {total_len}!")
            print(f"  This means no min-length good cycle exists for this placement.")
            continue

        # Check each word with ALL state sequences
        total_valid = 0
        total_ec = 0
        total_no_ec = 0
        no_ec_examples = []

        for widx, word in enumerate(walks):
            tv, tc, cf = check_entry_conflicts_allseq(word, n, ms)
            total_valid += tv
            total_ec += tc
            if cf:
                total_no_ec += len(cf)
                if len(no_ec_examples) < 3:
                    no_ec_examples.append((word, cf[0]))

            # Progress
            if (widx + 1) % 100 == 0:
                print(f"    Checked {widx+1}/{len(walks)} words, "
                      f"valid cycles so far: {total_valid}, EC: {total_ec}")

        t2 = time.time()
        pct = f"{100*total_ec/total_valid:.1f}%" if total_valid > 0 else "N/A"
        print(f"  Total valid (word, state-seq) pairs: {total_valid}")
        print(f"  With EC: {total_ec} ({pct})")
        print(f"  Without EC: {total_no_ec}")
        print(f"  Check time: {t2-t1:.1f}s")

        if no_ec_examples:
            print(f"  *** EXCEPTIONS (first 3): ***")
            for word, combo in no_ec_examples:
                print(f"    word={list(word)[:12]}..., len={len(word)}")
                print(f"    state-seqs: {[list(combo[p]) for p in range(n)]}")

    # PHASE 2: 4-binary
    print(f"\n\n{'='*70}")
    print("PHASE 2: 4 non-consecutive binary on 9-ring")
    product_4 = 2**4 * 3**5
    print(f"Product = 2^4 * 3^5 = {product_4} (sub-threshold: {product_4 < threshold})")
    print(f"{'='*70}")

    placements_4 = enumerate_placements(n, 4)
    print(f"Distinct placements: {len(placements_4)}")

    for pos, gaps in sorted(placements_4, key=lambda x: x[1]):
        ms = make_ms(n, pos)
        total_len_4 = sum(ms)
        print(f"\n--- gaps={gaps}, positions={pos}, ms={ms}, cycle_len={total_len_4} ---")
        t0 = time.time()
        walks = enumerate_fc2_walks(n, ms)
        t1 = time.time()
        print(f"  Mover words: {len(walks)} ({t1-t0:.1f}s)")

        if not walks:
            print(f"  No valid ring walks.")
            continue

        total_valid = 0
        total_ec = 0

        for word in walks:
            tv, tc, cf = check_entry_conflicts_allseq(word, n, ms)
            total_valid += tv
            total_ec += tc

        t2 = time.time()
        pct = f"{100*total_ec/total_valid:.1f}%" if total_valid > 0 else "N/A"
        print(f"  Valid: {total_valid}, EC: {total_ec} ({pct})")
        print(f"  Time: {t2-t1:.1f}s")

    # Summary
    print(f"\n\n{'='*70}")
    print("FINAL SUMMARY")
    print(f"{'='*70}")


if __name__ == "__main__":
    main()
