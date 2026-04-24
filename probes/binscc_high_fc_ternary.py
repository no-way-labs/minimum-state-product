#!/usr/bin/env python3
"""At n=6 alternating, one ternary fires 6 times (2 per phase).
Does this ALONE guarantee entry conflict?

If fc[T]=6 and T has 3 phases, each phase has 2 mover steps.
With context space {0,1}^2 = 4 values, 2 mover contexts + nonmover contexts
make entry conflict very likely.

Also: does the double-firing ternary ALWAYS have entry conflict?
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

n, ms = 6, [2,3,2,3,2,3]
t0 = time.time()
words = enumerate_mover_words(ms, n, 24)
print(f"n=6 alt: {len(words)} words ({time.time()-t0:.1f}s)")

ternary = [1, 3, 5]
total = 0

# For each ternary, check: does fc ≥ 6 guarantee entry conflict?
high_fc_ec = Counter()  # (proc, fc, has_ec)
single_fc_ec = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    total += 1
    fc = Counter(word)

    for t in ternary:
        has_ec = has_entry_conflict_at(ms, n, word, cycle, t)
        high_fc_ec[(t, fc[t], has_ec)] += 1

print(f"Total: {total}")
print(f"\nTernary fc vs entry conflict:")
for (t, fc_val, has_ec), cnt in sorted(high_fc_ec.items()):
    print(f"  P{t} fc={fc_val} ec={has_ec}: {cnt}")

# KEY: For fc=6 ternary, is ec always True?
print(f"\nSummary:")
for t in ternary:
    fc6_ec = high_fc_ec.get((t, 6, True), 0)
    fc6_noec = high_fc_ec.get((t, 6, False), 0)
    fc3_ec = high_fc_ec.get((t, 3, True), 0)
    fc3_noec = high_fc_ec.get((t, 3, False), 0)
    print(f"  P{t}: fc=6 → ec={fc6_ec}/{fc6_ec+fc6_noec}. "
          f"fc=3 → ec={fc3_ec}/{fc3_ec+fc3_noec}")

# PART 2: For the MINIMUM-fc ternary (fc=3), is it the one that fails?
print(f"\n{'='*60}")
print("Which ternary fails when one fails?")
failing_proc = Counter()
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    for t in ternary:
        if not has_entry_conflict_at(ms, n, word, cycle, t):
            fc = Counter(word)
            failing_proc[(t, fc[t])] += 1

print(f"  Failing ternary (proc, fc):")
for (t, fc_val), cnt in sorted(failing_proc.items()):
    print(f"    P{t} fc={fc_val}: fails {cnt} times")

# PART 3: Phase analysis for fc=6 ternary
print(f"\n{'='*60}")
print("Phase analysis for fc=6 ternary")

fc6_phase_movers = Counter()  # (# movers per phase, has_phase_ec)
for word in words[:20000]:  # sample
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)

    for t in ternary:
        if fc[t] != 6:
            continue
        bL, bR = (t-1)%n, (t+1)%n
        for k in range(3):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            mover_count = sum(1 for s in steps if word[s] == t)
            # Check phase entry conflict
            m_lr = set()
            nm_lr = set()
            for s in steps:
                lr = (cycle[s][bL], cycle[s][bR])
                if word[s] == t:
                    m_lr.add(lr)
                else:
                    nm_lr.add(lr)
            has_phase_ec = bool(m_lr & nm_lr)
            fc6_phase_movers[(mover_count, has_phase_ec)] += 1

print(f"  (movers_per_phase, phase_ec):")
for (mc, ec), cnt in sorted(fc6_phase_movers.items()):
    print(f"    {mc} movers, ec={ec}: {cnt}")

# PART 4: Can we prove fc=6 → ec analytically?
# fc=6 means 2 movers per phase. Each phase has 2 mover (L,R) values.
# For no ec: both mover (L,R) values must be absent from nonmover (L,R).
# With 4 possible (L,R) in {0,1}^2: need 2 values for movers, 2 for nonmovers.
# This means movers use exactly 2 corners and nonmovers use the other 2.
# Is this achievable given the walk structure?

print(f"\n{'='*60}")
print("ANALYTICAL ARGUMENT: fc=6 → entry conflict")
print()
print("With 2 movers per phase of sandwiched T (context {0,1}^2):")
print("  Movers contribute ≤ 2 distinct (L,R) values per phase")
print("  Nonmovers contribute ≤ 4 - (mover values) = 2 or 3 values")
print()
print("For no entry conflict: mover (L,R) ∩ nonmover (L,R) = ∅")
print("  → movers use 2 corners, nonmovers use the other 2 corners")
print("  → EVERY nonmover step is at one of exactly 2 corners")
print()
print("But the (L,R) trajectory is a walk on {0,1}^2 driven by")
print("neighbor firings. With J+K direction changes, the trajectory")
print("visits multiple corners. For nonmovers to use only 2 corners,")
print("the trajectory (excluding mover stays) must oscillate between 2.")

# Check: in the fc=6 phases, how many distinct mover (L,R) values?
print(f"\n  Empirical: mover (L,R) set sizes for fc=6 ternary phases:")
mover_lr_sizes = Counter()
for word in words[:20000]:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)
    for t in ternary:
        if fc[t] != 6:
            continue
        bL, bR = (t-1)%n, (t+1)%n
        for k in range(3):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            m_lr = set()
            for s in steps:
                if word[s] == t:
                    m_lr.add((cycle[s][bL], cycle[s][bR]))
            mover_lr_sizes[len(m_lr)] += 1

for sz, cnt in sorted(mover_lr_sizes.items()):
    print(f"    {sz} distinct mover (L,R): {cnt}")

print(f"\n  If movers use 2 distinct (L,R): 2 corners for movers,")
print(f"  2 for nonmovers. The walk must separate perfectly.")
print(f"  If movers use 1 (L,R): all nonmovers avoid 1 corner.")
print(f"  Possible if d_k is small enough.")

print(f"\nTime: {time.time()-t0:.1f}s")
