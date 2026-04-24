#!/usr/bin/env python3
"""Ring Alternation Lemma: at least one ternary always has ordering C.

KEY INSIGHT: On the alternating ring, the binary fc pattern alternates
high/low: [4,3,2,3,4,3,2,3,...] or [2,3,4,3,2,3,4,3,...].

For each ternary T (sandwiched between binary bL, bR):
  The "singleton side" = the binary neighbor with FEWER firings.

  In the (2,1)/(1,2) phase: the singleton is the neighbor firing 1 time.
  This is the neighbor with lower total fc (fc=2 contributes 1 to this phase,
  while fc=4 contributes 2).

  The singleton side alternates left/right at consecutive ternary.

  The walk direction determines which ternary has the singleton fire first.
  Walk clockwise → half get ordering C. Walk counterclockwise → the other half.

  Since k ≥ 2 ternary (from n ≥ 5, ≥3 binary), at least one has ordering C → EC.

VERIFY: this structural argument, and check that the singleton side alternation
holds computationally.
"""
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

def temporal_order(steps, ell):
    if len(steps) <= 1:
        return steps
    max_gap = 0
    start_after = 0
    for i in range(len(steps)):
        nxt = (i + 1) % len(steps)
        gap = (steps[nxt] - steps[i]) % ell
        if gap > max_gap:
            max_gap = gap
            start_after = i
    start_idx = (start_after + 1) % len(steps)
    return [steps[(start_idx + i) % len(steps)] for i in range(len(steps))]

# For each anti-diagonal cycle: which ternary has the singleton as "first neighbor"?
# And does the singleton side alternate?
print("=" * 70)
print("SINGLETON SIDE ALTERNATION")
print("=" * 70)

for n, ms, label, max_len in [
    (5, [2, 3, 2, 3, 2], "n=5", 16),
    (8, [2, 3, 2, 3, 2, 3, 2, 3], "n=8", 24),
]:
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p - 1) % n] == 2 and ms[(p + 1) % n] == 2]

    singleton_patterns = Counter()
    first_fire_patterns = Counter()

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)
        fc = Counter(word)

        # Check if all fc=3 ternary are anti-diagonal
        all_anti = True
        for t in sandwiched:
            if fc[t] != 3:
                all_anti = False
                break
            bL, bR = (t - 1) % n, (t + 1) % n
            for k in range(3):
                steps = sorted(s for s in range(ell) if cycle[s][t] == k)
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)
                if J % 2 == 0 and K % 2 == 0:
                    all_anti = False
                    break
            if not all_anti:
                break
        if not all_anti:
            continue

        # For each ternary: find the (2,1)/(1,2) phase
        singleton_side = []  # 'L' or 'R' for each ternary
        first_fire_side = []  # 'L' or 'R'

        for t in sandwiched:
            bL, bR = (t - 1) % n, (t + 1) % n
            for k in range(3):
                raw = sorted(s for s in range(ell) if cycle[s][t] == k)
                steps = temporal_order(raw, ell)
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)
                if (J, K) not in [(2, 1), (1, 2)]:
                    continue

                # Singleton side
                if K == 1:
                    singleton_side.append('R')
                else:
                    singleton_side.append('L')

                # First neighbor to fire
                for s in steps:
                    if word[s] == bL:
                        first_fire_side.append('L')
                        break
                    elif word[s] == bR:
                        first_fire_side.append('R')
                        break

        singleton_patterns[tuple(singleton_side)] += 1
        first_fire_patterns[tuple(first_fire_side)] += 1

    print(f"\n{label}: anti-diagonal cycles")
    print(f"  Singleton side patterns:")
    for pat, cnt in sorted(singleton_patterns.items(), key=lambda x: -x[1]):
        print(f"    {pat}: {cnt}")
    print(f"  First-fire side patterns:")
    for pat, cnt in sorted(first_fire_patterns.items(), key=lambda x: -x[1]):
        print(f"    {pat}: {cnt}")

# PART 2: For each ternary, does singleton_side == first_fire_side → EC?
print(f"\n{'='*70}")
print("VERIFY: singleton=first ↔ ordering C ↔ EC")
print("=" * 70)

for n, ms, label, max_len in [
    (5, [2, 3, 2, 3, 2], "n=5", 16),
    (8, [2, 3, 2, 3, 2, 3, 2, 3], "n=8", 24),
]:
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p - 1) % n] == 2 and ms[(p + 1) % n] == 2]

    per_ternary_ec = Counter()  # (t_idx, singleton==first, actual_ec)

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)
        fc = Counter(word)

        all_anti = True
        for t in sandwiched:
            if fc[t] != 3:
                all_anti = False
                break
            bL, bR = (t - 1) % n, (t + 1) % n
            for k in range(3):
                steps = sorted(s for s in range(ell) if cycle[s][t] == k)
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)
                if J % 2 == 0 and K % 2 == 0:
                    all_anti = False
                    break
            if not all_anti:
                break
        if not all_anti:
            continue

        for ti, t in enumerate(sandwiched):
            bL, bR = (t - 1) % n, (t + 1) % n
            for k in range(3):
                raw = sorted(s for s in range(ell) if cycle[s][t] == k)
                steps = temporal_order(raw, ell)
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)
                if (J, K) not in [(2, 1), (1, 2)]:
                    continue

                # Singleton side
                single_is_bR = (K == 1)

                # First neighbor
                first_is_bR = None
                for s in steps:
                    if word[s] == bL:
                        first_is_bR = False
                        break
                    elif word[s] == bR:
                        first_is_bR = True
                        break

                singleton_first = (single_is_bR == first_is_bR)

                # Actual EC
                m_lr, nm_lr = set(), set()
                for s in steps:
                    lr = (cycle[s][bL], cycle[s][bR])
                    if word[s] == t:
                        m_lr.add(lr)
                    else:
                        nm_lr.add(lr)
                actual_ec = bool(m_lr & nm_lr)

                per_ternary_ec[(singleton_first, actual_ec)] += 1

    print(f"\n{label}:")
    for (sf, ec), cnt in sorted(per_ternary_ec.items()):
        match = "✓" if sf == ec else "✗"
        print(f"    singleton_first={str(sf):5s} ec={str(ec):5s}: {cnt} {match}")

# PART 3: What about odd n (e.g., n=5)?
# n=5 has 3 binary, 2 ternary. Binary fc: each binary fires at least 2 times.
# fc pattern for anti-diagonal cycles at n=5?
print(f"\n{'='*70}")
print("n=5: binary fc in anti-diagonal cycles")
print("=" * 70)

n, ms = 5, [2, 3, 2, 3, 2]
words = enumerate_mover_words(ms, n, 16)
sandwiched = [1, 3]

fc_patterns = Counter()
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)
    all_anti = True
    for t in sandwiched:
        if fc[t] != 3:
            all_anti = False
            break
        bL, bR = (t - 1) % n, (t + 1) % n
        for k in range(3):
            steps = sorted(s for s in range(ell) if cycle[s][t] == k)
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            if J % 2 == 0 and K % 2 == 0:
                all_anti = False
                break
        if not all_anti:
            break
    if all_anti:
        fc_patterns[tuple(fc.get(p, 0) for p in range(n))] += 1

print(f"n=5 anti-diagonal fc patterns:")
for pat, cnt in sorted(fc_patterns.items(), key=lambda x: -x[1]):
    print(f"  fc={list(pat)}: {cnt}")
