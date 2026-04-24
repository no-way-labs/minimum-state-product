#!/usr/bin/env python3
"""
RA16: Prove exists_zw_oneSided_provider

Theorem: In a zero-winding good cycle on ring of n >= 9 processors with:
- >= 3 binary procs
- sub-threshold product
- cwStepCount > 0
- no safe processor
- all fc >= 2
- some proc q with fc(q) >= 3

There exists proc t and a TernaryPhase at t where:
- One neighbor of t fires 0 times in the phase (silent side)
- Other neighbor is binary with even fire count >= 2 in the phase (active side)

Strategy: analyze the walk structure near binary processors.
"""
import sys, os
from collections import Counter, defaultdict
from itertools import product as iterproduct

sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', buffering=1)

def enumerate_zw_gap_words(ms, n, max_cl=None):
    """Enumerate zero-winding good-cycle mover words with some fc >= 3."""
    if max_cl is None:
        max_cl = 3 * n + 4

    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))

    def direction(a, b, n):
        """CW = +1, CCW = -1"""
        if (a + 1) % n == b:
            return 1  # CW
        return -1  # CCW

    def dfs(word, fc, config, winding):
        if len(word) > max_cl:
            return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                if winding == 0 and any(fc[p] >= 3 for p in range(n)):
                    # Check cwStepCount > 0
                    cw = sum(1 for i in range(len(word)-1) if (word[i]+1)%n == word[i+1])
                    ccw = sum(1 for i in range(len(word)-1) if (word[i]-1)%n == word[i+1])
                    if cw > 0 and ccw > 0:
                        results.append(tuple(word))
            return
        remaining = max_cl - len(word)
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
            d = direction(last, nxt, n)
            word.append(nxt)
            dfs(word, nf, tuple(nc), winding + d)
            word.pop()

    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first), 0)

    return results


def check_theorem(word, ms, n):
    """Check if the theorem holds: exists t with a TernaryPhase having one-sided binary provider.

    A TernaryPhase of proc t: a maximal interval [a, s) where t does not fire.
    t fires at step a-1 and step s (the boundaries).

    We need: in some phase of some t,
    - one neighbor of t is binary, fires even >= 2 times in [a,s)
    - other neighbor fires 0 times in [a,s)
    """
    fc = Counter(word)
    CL = len(word)

    # Find all procs with fc >= 3
    high_fc = [p for p in range(n) if fc[p] >= 3]
    if not high_fc:
        return None, "no fc >= 3"

    binary_pos = set(i for i in range(n) if ms[i] == 2)

    # For each proc t, find its firing steps
    firing_steps = defaultdict(list)
    for k, mover in enumerate(word):
        firing_steps[mover].append(k)

    # For each proc t with fc >= 2, extract phases
    for t in range(n):
        if fc[t] < 2:
            continue
        steps_t = firing_steps[t]
        # Phases: between consecutive firings of t
        # Phase i: from steps_t[i]+1 to steps_t[i+1]-1 (inclusive)
        # Meaning [steps_t[i]+1, steps_t[i+1]) in terms of mover steps
        for phase_idx in range(len(steps_t)):
            a = steps_t[phase_idx]  # t fires at step a
            s = steps_t[(phase_idx + 1) % len(steps_t)]  # t fires at step s

            # Phase interval: steps after a, before s (where t doesn't fire)
            # Count fires of left(t) and right(t) in this interval
            left_t = (t - 1) % n
            right_t = (t + 1) % n

            left_fires = 0
            right_fires = 0

            # Handle wraparound
            if s > a:
                for k in range(a + 1, s):
                    if word[k] == left_t:
                        left_fires += 1
                    if word[k] == right_t:
                        right_fires += 1
            else:
                for k in range(a + 1, CL):
                    if word[k] == left_t:
                        left_fires += 1
                    if word[k] == right_t:
                        right_fires += 1
                for k in range(0, s):
                    if word[k] == left_t:
                        left_fires += 1
                    if word[k] == right_t:
                        right_fires += 1

            # Check: left is binary, even >= 2, right fires 0
            if (left_t in binary_pos and left_fires >= 2 and left_fires % 2 == 0
                    and right_fires == 0):
                return (t, phase_idx, 'left_active'), f"t={t}, left={left_t} fires {left_fires}, right={right_t} silent"

            # Check: right is binary, even >= 2, left fires 0
            if (right_t in binary_pos and right_fires >= 2 and right_fires % 2 == 0
                    and left_fires == 0):
                return (t, phase_idx, 'right_active'), f"t={t}, right={right_t} fires {right_fires}, left={left_t} silent"

    return None, "FAILED"


# ============================================================
# Test at small n values
# ============================================================
print("=" * 70)
print("VERIFICATION: exists_zw_oneSided_provider")
print("=" * 70)

for ms_desc, ms_list in [
    ("3 consec binary", [[2,2,2,3,3]]),
    ("3 non-consec binary", [[2,3,2,3,2]]),
]:
    for ms in ms_list:
        n = len(ms)
        print(f"\nms={ms}, n={n} ({ms_desc})")
        words = enumerate_zw_gap_words(ms, n)
        if not words:
            print(f"  No qualifying words found")
            continue

        passed = 0
        failed = 0
        failed_words = []
        for w in words:
            result, msg = check_theorem(w, ms, n)
            if result is not None:
                passed += 1
            else:
                failed += 1
                if len(failed_words) < 3:
                    failed_words.append((w, msg))

        print(f"  Words: {len(words)}, Passed: {passed}, Failed: {failed}")
        for w, msg in failed_words:
            print(f"  FAILED: word={w[:20]}... msg={msg}")


# ============================================================
# n=7
# ============================================================
print("\n" + "=" * 70)
print("n=7 tests")
print("=" * 70)

for ms in [[2,2,2,3,3,3,3], [2,3,2,3,2,3,3]]:
    n = len(ms)
    print(f"\nms={ms}, n={n}")
    words = enumerate_zw_gap_words(ms, n, max_cl=22)
    if not words:
        print(f"  No qualifying words found (trying larger CL...)")
        words = enumerate_zw_gap_words(ms, n, max_cl=24)

    if not words:
        print(f"  Still none at CL<=24")
        continue

    passed = 0
    failed = 0
    failed_words = []
    for w in words:
        result, msg = check_theorem(w, ms, n)
        if result is not None:
            passed += 1
        else:
            failed += 1
            if len(failed_words) < 3:
                failed_words.append((w, msg))

    print(f"  Words: {len(words)}, Passed: {passed}, Failed: {failed}")
    for w, msg in failed_words:
        fc = Counter(w)
        print(f"  FAILED: CL={len(w)}, fc={dict(fc)}, msg={msg}")
        print(f"    word={w}")
