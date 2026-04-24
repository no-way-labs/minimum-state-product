#!/usr/bin/env python3
"""Traversal Return EC: the EXACT characterization.

For (J=1, K=2) phase with M=1:
  Mover = (L̄₀, R₀) since L toggles 1x (odd), R toggles 2x (even→returns)

CLAIM: EC ⟺ bL fires first (before any bR) in the phase.
  If bL first: right after bL, nonmover at (L̄₀, R₀) = mover → EC
  If bR first: nonmover visits (L₀,R̄₀),(L̄₀,R̄₀),... but NOT (L̄₀,R₀) → no EC

More generally for (J=odd, K=even≥2) with M=1:
  Mover = (L̄₀, R₀)
  EC ⟺ first neighbor = bL (the odd-count side)

For (J=even≥2, K=odd) with M=1:
  Mover = (L₀, R̄₀)
  EC ⟺ first neighbor = bR (the odd-count side)

UNIVERSAL: EC ⟺ the "odd-count side fires first"

Then on the ring: at least one ternary always has the favorable direction.
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
print("TEST: EC ⟺ odd-count side fires first")
print("=" * 70)

for n, ms, label, max_len in [
    (5, [2,3,2,3,2], "n=5", 16),
    (8, [2,3,2,3,2,3,2,3], "n=8", 24),
]:
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

    # Test: EC ⟺ odd-count side fires first
    confirm = Counter()  # (ec_predicted, ec_actual) → count

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
                if J + K < 2 or J == K:
                    continue  # only (J≠K) with both >0
                if J % 2 == 0 and K % 2 == 0:
                    continue  # both-even handled separately

                # Odd-count side
                if J % 2 == 1 and K % 2 == 0:
                    odd_side = bL
                elif J % 2 == 0 and K % 2 == 1:
                    odd_side = bR
                else:
                    continue  # both odd — skip

                # Who fires first?
                first_neighbor = None
                for s in steps:
                    if word[s] == bL:
                        first_neighbor = bL
                        break
                    elif word[s] == bR:
                        first_neighbor = bR
                        break

                predicted_ec = (first_neighbor == odd_side)

                # Actual EC
                m_lr, nm_lr = set(), set()
                for s in steps:
                    lr = (cycle[s][bL], cycle[s][bR])
                    if word[s] == t:
                        m_lr.add(lr)
                    else:
                        nm_lr.add(lr)
                actual_ec = bool(m_lr & nm_lr)

                confirm[(predicted_ec, actual_ec)] += 1

    print(f"\n{label}:")
    for (pred, actual), cnt in sorted(confirm.items()):
        match = "✓" if pred == actual else "✗"
        print(f"  predicted={pred}, actual={actual}: {cnt} {match}")

    total = sum(confirm.values())
    correct = confirm[(True, True)] + confirm[(False, False)]
    print(f"  Accuracy: {correct}/{total} ({100*correct/total:.1f}%)")

# PART 2: For uncovered cycles, which ternary has EC?
# Is it always alternating around the ring?
print(f"\n{'='*70}")
print("COUPLING: which ternary get EC in uncovered cycles?")
print("=" * 70)

for n, ms, label, max_len in [
    (5, [2,3,2,3,2], "n=5", 16),
    (8, [2,3,2,3,2,3,2,3], "n=8", 24),
]:
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

    ec_patterns = Counter()  # which subset of ternary has (2,1)/(1,2) EC

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)
        fc = Counter(word)

        # Check if covered by 3 proved mechanisms
        cycle_covered = False
        for t in sandwiched:
            bL, bR = (t-1)%n, (t+1)%n
            m = fc[t]; M = m // 3
            for k in range(3):
                steps = [s for s in range(ell) if cycle[s][t] == k]
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)
                if M == 1 and J % 2 == 0 and K % 2 == 0:
                    cycle_covered = True; break
                if (J >= 3 and K == 0) or (J == 0 and K >= 3):
                    cycle_covered = True; break
                if M == 1 and ((J >= 2 and K == 0) or (J == 0 and K >= 2)):
                    cycle_covered = True; break
            if cycle_covered: break

        if cycle_covered:
            continue

        # Which ternary have (2,1)/(1,2) EC?
        ec_set = []
        for t in sandwiched:
            bL, bR = (t-1)%n, (t+1)%n
            has_ec = False
            for k in range(3):
                steps = [s for s in range(ell) if cycle[s][t] == k]
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)
                if (J, K) not in [(2, 1), (1, 2)]:
                    continue
                m_lr, nm_lr = set(), set()
                for s in steps:
                    lr = (cycle[s][bL], cycle[s][bR])
                    if word[s] == t: m_lr.add(lr)
                    else: nm_lr.add(lr)
                if m_lr & nm_lr:
                    has_ec = True
                    break
            ec_set.append(t if has_ec else None)

        pattern = tuple(1 if x is not None else 0 for x in ec_set)
        ec_patterns[pattern] += 1

    print(f"\n{label}: EC pattern across ternary {sandwiched}:")
    for pattern, cnt in sorted(ec_patterns.items(), key=lambda x: -x[1]):
        print(f"  {pattern}: {cnt}")

# PART 3: Does "odd-count side fires first → EC" hold for ALL odd/even combos?
# Including (3,2), (2,3), etc.?
print(f"\n{'='*70}")
print("GENERAL odd/even: EC ⟺ odd-count side fires first?")
print("=" * 70)

for n, ms, label, max_len in [
    (5, [2,3,2,3,2], "n=5", 16),
    (6, [2,3,2,3,2,3], "n=6", 24),
]:
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

    confirm_general = Counter()

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)
        fc = Counter(word)

        for t in sandwiched:
            bL, bR = (t-1)%n, (t+1)%n
            M_per_phase = fc[t] // 3
            for k in range(3):
                steps = [s for s in range(ell) if cycle[s][t] == k]
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)
                M = sum(1 for s in steps if word[s] == t)

                # Only anti-diagonal phases with both J,K > 0
                if J == 0 or K == 0: continue
                if J % 2 == K % 2: continue  # not anti-diagonal

                # Determine odd-count side
                if J % 2 == 1:
                    odd_side = bL
                else:
                    odd_side = bR

                # Who fires first?
                first_neighbor = None
                for s in steps:
                    if word[s] == bL:
                        first_neighbor = bL; break
                    elif word[s] == bR:
                        first_neighbor = bR; break

                predicted_ec = (first_neighbor == odd_side)

                m_lr, nm_lr = set(), set()
                for s in steps:
                    lr = (cycle[s][bL], cycle[s][bR])
                    if word[s] == t: m_lr.add(lr)
                    else: nm_lr.add(lr)
                actual_ec = bool(m_lr & nm_lr)

                confirm_general[(label, J, K, M, predicted_ec, actual_ec)] += 1

    print(f"\n{label}:")
    wrong = 0
    for (lab, J, K, M, pred, actual), cnt in sorted(confirm_general.items()):
        if lab != label: continue
        if pred != actual:
            wrong += 1
            print(f"  ✗ ({J},{K}) M={M}: pred={pred} actual={actual}: {cnt}")
    if wrong == 0:
        print(f"  ALL CORRECT — odd-count-first ⟺ EC for all anti-diagonal phases!")
    else:
        # Show summary
        for (lab, J, K, M, pred, actual), cnt in sorted(confirm_general.items()):
            if lab == label and pred != actual:
                pass  # already printed
