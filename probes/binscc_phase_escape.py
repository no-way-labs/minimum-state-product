#!/usr/bin/env python3
"""Which phase-level mechanisms are ACTUALLY universal?

Key question: (2,0) and (0,2) fail at n=6 phase-level.
Does (3,0)/(0,3) still hold? What about Both-Even?
And: when a phase escapes, does the PROCESSOR still get caught?
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

def has_entry_conflict_at(ms, n, word, cycle, p):
    ell = len(word)
    bL, bR = (p-1)%n, (p+1)%n
    mover, nonmover = set(), set()
    for s in range(ell):
        lsr = (cycle[s][bL], cycle[s][p], cycle[s][bR])
        if word[s] == p: mover.add(lsr)
        else: nonmover.add(lsr)
    return bool(mover & nonmover)

def phase_ec_at(ms, n, word, cycle, p, k):
    """Entry conflict restricted to phase k of proc p."""
    ell = len(word)
    bL, bR = (p-1)%n, (p+1)%n
    mover, nonmover = set(), set()
    for s in range(ell):
        if cycle[s][p] != k:
            continue
        lsr = (cycle[s][bL], cycle[s][p], cycle[s][bR])
        if word[s] == p: mover.add(lsr)
        else: nonmover.add(lsr)
    return bool(mover & nonmover)

# PART 1: Verify (3,0)/(0,3) is truly universal at phase level
print("=" * 70)
print("PHASE-LEVEL MECHANISM UNIVERSALITY CHECK")
print("=" * 70)

for n, ms, label, max_len in [
    (4, [2,3,2,3], "n=4", 14),
    (5, [2,3,2,3,2], "n=5", 16),
    (6, [2,3,2,3,2,3], "n=6", 24),
]:
    t0 = time.time()
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

    check = Counter()  # (J,K,phase_ec) for specific conditions
    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)
        for t in sandwiched:
            bL, bR = (t-1)%n, (t+1)%n
            for k in range(3):
                steps = [s for s in range(ell) if cycle[s][t] == k]
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)
                pec = phase_ec_at(ms, n, word, cycle, t, k)
                if (J >= 3 and K == 0) or (J == 0 and K >= 3):
                    check[('≥3,0', pec)] += 1
                elif (J == 2 and K == 0) or (J == 0 and K == 2):
                    check[('2,0', pec)] += 1
                elif J % 2 == 0 and K % 2 == 0 and J > 0 and K > 0:
                    check[('both_even', pec)] += 1

    elapsed = time.time() - t0
    print(f"\n{label} ({elapsed:.1f}s):")
    for (cat, ec), cnt in sorted(check.items()):
        status = "✓ UNIVERSAL" if ec else f"✗ {cnt} FAILURES"
        print(f"  {cat:12s} ec={ec}: {cnt:>8} {status}")
    check.clear()

# PART 2: n=6 — when (2,0) phase escapes EC, does the PROCESSOR still have EC?
print(f"\n{'='*70}")
print("n=6: WHEN (2,0) PHASE ESCAPES, DOES PROCESSOR STILL HAVE EC?")
print("=" * 70)

n, ms = 6, [2,3,2,3,2,3]
words = enumerate_mover_words(ms, n, 24)
sandwiched = [1, 3, 5]

escape_20_proc_ec = Counter()  # does proc still have EC?
escape_22_proc_ec = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n
        proc_ec = has_entry_conflict_at(ms, n, word, cycle, t)
        for k in range(3):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            pec = phase_ec_at(ms, n, word, cycle, t, k)
            if (J == 2 and K == 0) or (J == 0 and K == 2):
                if not pec:
                    escape_20_proc_ec[proc_ec] += 1
            if J % 2 == 0 and K % 2 == 0 and J > 0 and K > 0:
                if not pec:
                    escape_22_proc_ec[proc_ec] += 1

print(f"  (2,0) phase escapes but proc has EC: {escape_20_proc_ec}")
print(f"  (2,2) phase escapes but proc has EC: {escape_22_proc_ec}")

# PART 3: What is the MINIMUM (J,K) pair that guarantees phase-level EC?
print(f"\n{'='*70}")
print("MINIMUM (J,K) FOR GUARANTEED PHASE-LEVEL EC")
print("=" * 70)

n, ms = 6, [2,3,2,3,2,3]
jk_ec_rate = Counter()
jk_total = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n
        for k in range(3):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            pec = phase_ec_at(ms, n, word, cycle, t, k)
            jk_total[(J,K)] += 1
            if pec:
                jk_ec_rate[(J,K)] += 1

print(f"  (J,K) → phase EC rate:")
for (J,K) in sorted(jk_total.keys()):
    tot = jk_total[(J,K)]
    ec = jk_ec_rate.get((J,K), 0)
    pct = 100*ec/tot if tot > 0 else 0
    uni = "UNIVERSAL" if ec == tot else ""
    print(f"    ({J},{K}): {ec}/{tot} = {pct:.1f}% {uni}")
