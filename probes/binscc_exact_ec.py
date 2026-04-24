#!/usr/bin/env python3
"""EXACT EC characterization for (J=2,K=1)/(J=1,K=2) phases with M=1.

Analysis: mover = (L₀ ⊕ J, R₀ ⊕ K). For (2,1): mover = (L₀, R̄₀).

The (j,r) trajectory goes (0,0)→(2,1) via 3 increments.
Orderings A,B,C:
  A (pair,pair,single): (0,0)→(1,0)→(2,0)→(2,1)
  B (pair,single,pair): (0,0)→(1,0)→(1,1)→(2,1)
  C (single,pair,pair): (0,0)→(0,1)→(1,1)→(2,1)

Nonmover visits intermediate states. AFTER each state, there may be far-steps
that see the NEXT state. Between the last neighbor and T:
  - "gap": far-steps exist → nonmover sees final state (2,1) = mover → EC
  - "no gap": walk goes directly neighbor→T → mover state only seen by T

CLAIM: EC ⟺ (ordering C, any gap status) OR (gap between last neighbor and T)
Equivalently: no EC ⟺ (ordering A or B) AND (no gap)
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
print("EXACT EC TEST: ordering C gives EC always; A/B need gap")
print("=" * 70)

for n, ms, label, max_len in [
    (5, [2,3,2,3,2], "n=5", 16),
    (8, [2,3,2,3,2,3,2,3], "n=8", 24),
]:
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

    exact_test = Counter()  # (ordering, gap, ec)
    claim_test = Counter()  # (predicted_ec, actual_ec)

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

                # Determine ordering
                if J == 2:  # pair = bL, single = bR
                    pair = bL; single = bR
                else:       # pair = bR, single = bL
                    pair = bR; single = bL

                # Get positions within phase (indices into steps[])
                neighbor_events = []
                for idx, s in enumerate(steps):
                    if word[s] == pair:
                        neighbor_events.append(('P', idx))
                    elif word[s] == single:
                        neighbor_events.append(('S', idx))

                # Extract ordering: positions of P and S
                ne_types = ''.join(t for t, _ in neighbor_events)
                if ne_types == 'PPS':
                    ordering = 'A'
                elif ne_types == 'PSP':
                    ordering = 'B'
                elif ne_types == 'SPP':
                    ordering = 'C'
                else:
                    ordering = ne_types  # unexpected

                # Gap: is there a non-neighbor step between last neighbor and T?
                # T is the last step. Last neighbor = last P or S step.
                mover_idx = next(idx for idx, s in enumerate(steps) if word[s] == t)
                last_neighbor_idx = max(idx for _, idx in neighbor_events)

                gap = (mover_idx - last_neighbor_idx > 1)

                exact_test[(ordering, gap, actual_ec)] += 1

                # Predict EC
                if ordering == 'C':
                    predicted_ec = True
                else:
                    predicted_ec = gap

                claim_test[(predicted_ec, actual_ec)] += 1

    print(f"\n{label}:")
    print(f"  (ordering, gap, EC):")
    for (o, g, ec), cnt in sorted(exact_test.items()):
        print(f"    order={o} gap={str(g):5s} ec={str(ec):5s}: {cnt}")

    print(f"\n  Claim test:")
    for (pred, actual), cnt in sorted(claim_test.items()):
        match = "✓" if pred == actual else "✗"
        print(f"    predicted={pred:5s} actual={actual:5s}: {cnt} {match}")
    total = sum(claim_test.values())
    correct = claim_test.get((True, True), 0) + claim_test.get((False, False), 0)
    print(f"    Accuracy: {correct}/{total} ({100*correct/total:.1f}%)")

# PART 2: Simpler characterization — does the walk go AWAY from T after last neighbor?
# "gap" on the ring: after last neighbor fires at position p, walk goes to p±1.
# If walk goes to T (position t): no gap. If walk goes away: gap.
print(f"\n{'='*70}")
print("RING GAP: does walk go away from T after last neighbor?")
print("=" * 70)

for n, ms, label, max_len in [
    (5, [2,3,2,3,2], "n=5", 16),
    (8, [2,3,2,3,2,3,2,3], "n=8", 24),
]:
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

    ring_gap_test = Counter()

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

                # Find last neighbor firing step
                mover_step = [s for s in steps if word[s] == t][0]
                last_neighbor_step = max(s for s in steps
                                         if word[s] in (bL, bR) and s < mover_step)

                # Does walk go to T or away after last neighbor?
                next_step_after_last = steps[steps.index(last_neighbor_step) + 1]
                goes_to_T = (word[next_step_after_last] == t)

                # Also: which neighbor was last?
                last_is_bL = (word[last_neighbor_step] == bL)
                last_is_bR = (word[last_neighbor_step] == bR)

                ring_gap_test[(label, goes_to_T, actual_ec)] += 1

    print(f"\n{label}:")
    for (lab, gtt, ec), cnt in sorted(ring_gap_test.items()):
        if lab == label:
            print(f"    goes_to_T={gtt:5s} ec={ec:5s}: {cnt}")

# PART 3: Simplest test: EC ⟺ nonmover includes mover (L,R)
# What is the nonmover set in terms of corners?
# And: does the walk ALWAYS visit (L₀,R̄₀) when ordering C?
print(f"\n{'='*70}")
print("VERIFY: ordering C ALWAYS has EC?")
print("=" * 70)

for n, ms, label, max_len in [
    (5, [2,3,2,3,2], "n=5", 16),
    (8, [2,3,2,3,2,3,2,3], "n=8", 24),
]:
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

    c_test = Counter()

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

                if J == 2: pair, single = bL, bR
                else: pair, single = bR, bL

                ne_types = ''
                for s in steps:
                    if word[s] == pair: ne_types += 'P'
                    elif word[s] == single: ne_types += 'S'

                if ne_types.startswith('S'):  # ordering C: single first
                    c_test[actual_ec] += 1

    print(f"\n{label}: ordering C phases: EC={c_test[True]}, no-EC={c_test[False]}")
