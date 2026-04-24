#!/usr/bin/env python3
"""Exact EC characterization for anti-diagonal (2,1)/(1,2) phases.

For (J=2, K=1), M=1: mover = (L₀, R̄₀) [L returns, R flips]
Nonmover visits depends on interleaving of 2 bL-firings and 1 bR-firing.

HYPOTHESIS: EC ⟺ bR fires BETWEEN the two bL firings (interleaved ordering).
  Interleaved (bL,bR,bL): nonmover visits all 4 corners → mover corner included → EC
  Block (bL,bL,bR) or (bR,bL,bL): nonmover visits only 3 corners → 4th corner = mover → NO EC

Check this exactly, considering far-steps.
"""
import time
from collections import Counter

def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n)
                      if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            dfs(word, nf, tuple(nc))
            word.pop()
    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))
    return results

def build_cycle(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]

def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)

print("=" * 70)
print("INTERLEAVING HYPOTHESIS: EC ⟺ singleton interleaved between pair")
print("=" * 70)

for n, ms, label, max_len in [
    (5, [2,3,2,3,2], "n=5", 16),
    (8, [2,3,2,3,2,3,2,3], "n=8", 24),
]:
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

    interleave_test = Counter()
    corners_test = Counter()

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)
        fc = Counter(word)

        for t in sandwiched:
            if fc[t] != 3:
                continue
            bL, bR = (t-1)%n, (t+1)%n
            for k in range(3):
                steps = [s for s in range(ell) if cycle[s][t] == k]
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)

                if not ((J == 2 and K == 1) or (J == 1 and K == 2)):
                    continue

                # Actual EC
                m_lr, nm_lr = set(), set()
                for s in steps:
                    lr = (cycle[s][bL], cycle[s][bR])
                    if word[s] == t: m_lr.add(lr)
                    else: nm_lr.add(lr)
                actual_ec = bool(m_lr & nm_lr)

                # Determine the "pair" side (count=2) and "singleton" side (count=1)
                if J == 2:  # bL fires twice, bR fires once
                    pair_side = bL
                    single_side = bR
                else:  # bR fires twice, bL fires once
                    pair_side = bR
                    single_side = bL

                # Get positions of pair and singleton firings in the phase
                pair_positions = [i for i, s in enumerate(steps) if word[s] == pair_side]
                single_positions = [i for i, s in enumerate(steps) if word[s] == single_side]

                # Is singleton interleaved between the pair?
                if len(pair_positions) >= 2 and len(single_positions) >= 1:
                    p1, p2 = pair_positions[0], pair_positions[1]
                    s1 = single_positions[0]
                    interleaved = (p1 < s1 < p2)
                    interleave_test[(interleaved, actual_ec)] += 1

                # Also check: how many corners does nonmover visit?
                n_corners = len(nm_lr)
                corners_test[(n_corners, actual_ec)] += 1

    print(f"\n{label}:")
    print(f"  Interleaving test:")
    for (inter, ec), cnt in sorted(interleave_test.items()):
        match = "✓" if inter == ec else "✗"
        print(f"    interleaved={inter}, ec={ec}: {cnt} {match}")

    total = sum(interleave_test.values())
    correct = interleave_test.get((True, True), 0) + interleave_test.get((False, False), 0)
    print(f"    Accuracy: {correct}/{total} ({100*correct/total:.1f}%)")

    print(f"  Corners test:")
    for (nc, ec), cnt in sorted(corners_test.items()):
        print(f"    nm_corners={nc}, ec={ec}: {cnt}")

# PART 2: More nuanced — is singleton between pair in terms of RING position
# (not phase-step position)? Or: does singleton fire in the L̄₀ window?
print(f"\n{'='*70}")
print("REFINED: EC ⟺ singleton fires when even-count side is at non-initial value")
print("=" * 70)

for n, ms, label, max_len in [
    (5, [2,3,2,3,2], "n=5", 16),
    (8, [2,3,2,3,2,3,2,3], "n=8", 24),
]:
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

    refined_test = Counter()

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)
        fc = Counter(word)

        for t in sandwiched:
            if fc[t] != 3:
                continue
            bL, bR = (t-1)%n, (t+1)%n
            for k in range(3):
                steps = [s for s in range(ell) if cycle[s][t] == k]
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)

                if not ((J == 2 and K == 1) or (J == 1 and K == 2)):
                    continue

                m_lr, nm_lr = set(), set()
                for s in steps:
                    lr = (cycle[s][bL], cycle[s][bR])
                    if word[s] == t: m_lr.add(lr)
                    else: nm_lr.add(lr)
                actual_ec = bool(m_lr & nm_lr)

                # Track the L,R state at each step
                L0 = cycle[steps[0]][bL]
                R0 = cycle[steps[0]][bR]

                # For (J=2, K=1): pair=bL, single=bR
                # At the bR firing step: what is L?
                # EC iff L ≠ L₀ at bR step (i.e., bR fires between the two bL firings)
                if J == 2 and K == 1:
                    bR_step = [s for s in steps if word[s] == bR][0]
                    L_at_bR = cycle[bR_step][bL]
                    single_in_flipped = (L_at_bR != L0)
                elif J == 1 and K == 2:
                    bL_step = [s for s in steps if word[s] == bL][0]
                    R_at_bL = cycle[bL_step][bR]
                    single_in_flipped = (R_at_bL != R0)

                refined_test[(single_in_flipped, actual_ec)] += 1

    print(f"\n{label}:")
    for (sif, ec), cnt in sorted(refined_test.items()):
        match = "✓" if sif == ec else "✗"
        print(f"    singleton_in_flipped={sif}, ec={ec}: {cnt} {match}")

    total = sum(refined_test.values())
    correct = refined_test.get((True, True), 0) + refined_test.get((False, False), 0)
    print(f"    Accuracy: {correct}/{total} ({100*correct/total:.1f}%)")
