#!/usr/bin/env python3
"""Why can't ALL sandwiched ternary fail FR simultaneously in alternating rings?

In alternating ring (n=2k, ms=[2,3,2,3,...]):
- k sandwiched ternary: P1, P3, ..., P_{2k-1}
- k binary: P0, P2, ..., P_{2k-2}

If ALL sandwiched fail Both-Even:
- Each has parity ABC = {(1,0),(0,1),(1,1)}
- Binary fire counts are constrained

KEY QUESTION: What prevents all-fail?
- Parity constraints alone?
- Walk structure?
- Duration bounds?

This script investigates the near-miss cases at n=5,6 and
looks for the universal obstruction.
"""
import sys, time
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

def has_return_phase(ms, n, word, cycle, p):
    ell = len(word)
    bL, bR = (p-1)%n, (p+1)%n
    for k in range(ms[p]):
        steps = [s for s in range(ell) if cycle[s][p] == k]
        J = sum(1 for s in steps if word[s] == bL)
        K = sum(1 for s in steps if word[s] == bR)
        if J % ms[bL] == 0 and K % ms[bR] == 0:
            return True
    return False

def phase_jk(ms, n, word, cycle, p):
    """Get per-phase (J,K) values."""
    ell = len(word)
    bL, bR = (p-1)%n, (p+1)%n
    result = []
    for k in range(ms[p]):
        steps = [s for s in range(ell) if cycle[s][p] == k]
        J = sum(1 for s in steps if word[s] == bL)
        K = sum(1 for s in steps if word[s] == bR)
        result.append((J, K))
    return result

print("=" * 70)
print("ALTERNATING RING: WHY ALL-FAIL IS IMPOSSIBLE")
print("=" * 70)

# ======== n=5 alternating ========
print("\n" + "=" * 60)
print("n=5, ms=[2,3,2,3,2]")

n, ms = 5, [2, 3, 2, 3, 2]
max_len = 20

t0 = time.time()
words = enumerate_mover_words(ms, n, max_len)
print(f"Words: {len(words)} ({time.time()-t0:.1f}s)")

sandwiched = [1, 3]
total = 0
fail_pattern = Counter()  # which ternary fail
near_miss = []  # only one ternary has FR

# Phase parity analysis for failing ternary
parity_analysis = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    total += 1

    fr_status = {}
    ret_status = {}
    for t in sandwiched:
        fr_status[t] = has_entry_conflict_at(ms, n, word, cycle, t)
        ret_status[t] = has_return_phase(ms, n, word, cycle, t)

    pattern = tuple(1 if fr_status[t] else 0 for t in sandwiched)
    fail_pattern[pattern] += 1

    # Near-miss: exactly one fails
    num_fail = sum(1 for t in sandwiched if not fr_status[t])
    if num_fail == 1:
        near_miss.append((word, cycle, fr_status, ret_status))

    # Phase parities when a ternary fails
    for t in sandwiched:
        if not fr_status[t]:
            jk = phase_jk(ms, n, word, cycle, t)
            parities = tuple(sorted((j % 2, k % 2) for j, k in jk))
            parity_analysis[(t, parities)] += 1

print(f"Total: {total}")
print(f"\nFR status at (P1, P3):")
for pattern, cnt in sorted(fail_pattern.items()):
    p1_lab = "FR" if pattern[0] else "fail"
    p3_lab = "FR" if pattern[1] else "fail"
    print(f"  P1={p1_lab}, P3={p3_lab}: {cnt}")

print(f"\nNear-miss (exactly 1 fails): {len(near_miss)}")

print(f"\nPhase parities when ternary fails (all should be ABC):")
for (t, parities), cnt in sorted(parity_analysis.items()):
    print(f"  P{t}, parities={parities}: {cnt}")

# Analyze near-miss: when P1 fails, what forces P3 to have FR?
print(f"\n{'='*60}")
print("NEAR-MISS ANALYSIS: WHEN P1 FAILS, WHAT FORCES P3 FR?")

p3_mechanism = Counter()
p3_return_jk = Counter()

for word, cycle, fr_status, ret_status in near_miss[:500]:
    if fr_status[1]:  # P1 has FR, look at P3
        continue
    # P1 fails, P3 has FR
    fc = Counter(word)
    jk3 = phase_jk(ms, n, word, cycle, 3)
    ret3 = ret_status[3]

    if ret3:
        p3_mechanism['return'] += 1
        for k, (j, kk) in enumerate(jk3):
            if j % 2 == 0 and kk % 2 == 0:
                p3_return_jk[(j, kk)] += 1
    else:
        p3_mechanism['non-return FR'] += 1

    # Also check: which binary fire counts when P1 fails?
    jk1 = phase_jk(ms, n, word, cycle, 1)
    fc_key = tuple(fc.get(p, 0) for p in range(n))

print(f"  P3 mechanism: {dict(p3_mechanism)}")
print(f"  P3 return (J,K): {dict(sorted(p3_return_jk.items()))}")

# Deeper: what are binary fire counts when P1 fails?
fc_when_p1_fail = Counter()
for word, cycle, fr_status, ret_status in near_miss[:500]:
    if fr_status[1]:
        continue
    fc = Counter(word)
    fc_bin = (fc[0], fc[2], fc[4])
    fc_when_p1_fail[fc_bin] += 1

print(f"\n  Binary fire counts when P1 fails:")
for fb, cnt in sorted(fc_when_p1_fail.items(), key=lambda x: -x[1]):
    print(f"    fc_bin={fb}: {cnt}")

# KEY: For each near-miss where P1 fails, what are P1's and P3's phase (J,K)?
print(f"\n  P1 phase (J,K) tuples when P1 fails:")
p1_jk_tuples = Counter()
p3_jk_tuples = Counter()
for word, cycle, fr_status, ret_status in near_miss[:500]:
    if fr_status[1]:
        continue
    jk1 = tuple(phase_jk(ms, n, word, cycle, 1))
    jk3 = tuple(phase_jk(ms, n, word, cycle, 3))
    p1_jk_tuples[jk1] += 1
    p3_jk_tuples[jk3] += 1

for jk, cnt in sorted(p1_jk_tuples.items(), key=lambda x: -x[1])[:10]:
    print(f"    {jk}: {cnt}")
print(f"  P3 phase (J,K) tuples when P1 fails (→ P3 has FR):")
for jk, cnt in sorted(p3_jk_tuples.items(), key=lambda x: -x[1])[:10]:
    ret_phases = [k for k, (j, kk) in enumerate(jk) if j % 2 == 0 and kk % 2 == 0]
    print(f"    {jk}: {cnt}  {'RET@'+str(ret_phases) if ret_phases else 'non-ret FR'}")

# ======== n=6 alternating ========
print(f"\n{'='*60}")
print("n=6, ms=[2,3,2,3,2,3]")

n6, ms6 = 6, [2,3,2,3,2,3]
max_len6 = 24

t1 = time.time()
words6 = enumerate_mover_words(ms6, n6, max_len6)
print(f"Words: {len(words6)} ({time.time()-t1:.1f}s)")

sandwiched6 = [1, 3, 5]
total6 = 0
fail_pattern6 = Counter()
num_failing6 = Counter()

for word in words6:
    cycle = build_cycle(ms6, n6, word)
    if cycle is None or not is_wrap_adjacent(word, n6):
        continue
    total6 += 1

    fr = {}
    for t in sandwiched6:
        fr[t] = has_entry_conflict_at(ms6, n6, word, cycle, t)

    pattern = tuple(1 if fr[t] else 0 for t in sandwiched6)
    fail_pattern6[pattern] += 1
    nf = sum(1 for t in sandwiched6 if not fr[t])
    num_failing6[nf] += 1

print(f"Total: {total6}")
print(f"\nNumber of failing sandwiched ternary:")
for nf, cnt in sorted(num_failing6.items()):
    print(f"  {nf} fail: {cnt} ({100*cnt/total6:.1f}%)")
print(f"\nFR status at (P1, P3, P5):")
for pattern, cnt in sorted(fail_pattern6.items()):
    labels = [f"P{sandwiched6[i]}={'FR' if pattern[i] else 'fail'}" for i in range(3)]
    print(f"  {', '.join(labels)}: {cnt}")

# When 2 fail at n=6: which pair, and what rescues?
print(f"\n  When 2 fail: which pair?")
pair_fail = Counter()
for word in words6:
    cycle = build_cycle(ms6, n6, word)
    if cycle is None or not is_wrap_adjacent(word, n6):
        continue
    fr = {t: has_entry_conflict_at(ms6, n6, word, cycle, t) for t in sandwiched6}
    failing = [t for t in sandwiched6 if not fr[t]]
    if len(failing) == 2:
        pair_fail[tuple(failing)] += 1

for pair, cnt in sorted(pair_fail.items(), key=lambda x: -x[1]):
    print(f"    {pair} fail: {cnt}")

# Binary fire counts when 2 fail
print(f"\n  Binary fc when 2 sandwiched fail:")
fc_when_2fail = Counter()
for word in words6:
    cycle = build_cycle(ms6, n6, word)
    if cycle is None or not is_wrap_adjacent(word, n6):
        continue
    fr = {t: has_entry_conflict_at(ms6, n6, word, cycle, t) for t in sandwiched6}
    failing = [t for t in sandwiched6 if not fr[t]]
    if len(failing) == 2:
        fc = Counter(word)
        fc_bin = tuple(fc.get(p, 0) for p in [0, 2, 4])
        fc_when_2fail[(tuple(failing), fc_bin)] += 1

for (pair, fb), cnt in sorted(fc_when_2fail.items(), key=lambda x: -x[1])[:15]:
    print(f"    {pair} fail, fc_bin={fb}: {cnt}")

# Phase (J,K) at the rescuing ternary when 2 fail
print(f"\n  Phase (J,K) at rescuing ternary when 2 fail:")
rescue_jk = Counter()
for word in words6:
    cycle = build_cycle(ms6, n6, word)
    if cycle is None or not is_wrap_adjacent(word, n6):
        continue
    fr = {t: has_entry_conflict_at(ms6, n6, word, cycle, t) for t in sandwiched6}
    failing = [t for t in sandwiched6 if not fr[t]]
    if len(failing) == 2:
        rescuer = [t for t in sandwiched6 if fr[t]][0]
        jk = tuple(phase_jk(ms6, n6, word, cycle, rescuer))
        ret_phases = [k for k, (j, kk) in enumerate(jk) if j % 2 == 0 and kk % 2 == 0]
        rescue_jk[(rescuer, jk, bool(ret_phases))] += 1

for (r, jk, has_ret), cnt in sorted(rescue_jk.items(), key=lambda x: -x[1])[:20]:
    print(f"    P{r} {jk} ret={has_ret}: {cnt}")

print(f"\nTotal: {time.time()-t0:.1f}s")
