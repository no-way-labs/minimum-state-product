#!/usr/bin/env python3
"""Coupling between sandwiched and non-sandwiched ternary FR.

When sandwiched (P1,P3) both fail FR, what forces non-sandwiched (P5,P6) to succeed?
The coupling goes through fire count constraints on shared binary neighbors.
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

def phase_jk_parities(ms, n, word, cycle, p):
    """Get (J,K) per phase and parity info."""
    ell = len(word)
    bL, bR = (p-1)%n, (p+1)%n
    result = []
    for k in range(ms[p]):
        steps = [s for s in range(ell) if cycle[s][p] == k]
        J = sum(1 for s in steps if word[s] == bL)
        K = sum(1 for s in steps if word[s] == bR)
        dur = len(steps)

        # FR check
        mover_lr, nonmover_lr = set(), set()
        for s in steps:
            lr = (cycle[s][bL], cycle[s][bR])
            if word[s] == p:
                mover_lr.add(lr)
            else:
                nonmover_lr.add(lr)
        has_fr = bool(mover_lr & nonmover_lr)

        # Return check: J ≡ 0 mod m_bL AND K ≡ 0 mod m_bR
        is_return = (J % ms[bL] == 0) and (K % ms[bR] == 0)

        result.append({'k':k, 'J':J, 'K':K, 'dur':dur, 'fr':has_fr, 'ret':is_return})
    return result

print("=" * 70)
print("COUPLING ANALYSIS: SANDWICHED vs NON-SANDWICHED")
print("=" * 70)

n, ms = 7, [2, 3, 2, 3, 2, 3, 3]
max_len = 24

t0 = time.time()
words = enumerate_mover_words(ms, n, max_len)
print(f"Words: {len(words)} ({time.time()-t0:.1f}s)")

# Find cycles where sandwiched BOTH fail and nsand BOTH fail
sand_fail_nsand_ok = []
nsand_fail_sand_ok = []
both_fail = []
total = 0

fc_when_sand_fail = Counter()
fc_when_nsand_fail = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    total += 1

    # Check FR at each ternary
    p1_fr = has_entry_conflict_at(ms, n, word, cycle, 1)
    p3_fr = has_entry_conflict_at(ms, n, word, cycle, 3)
    p5_fr = has_entry_conflict_at(ms, n, word, cycle, 5)
    p6_fr = has_entry_conflict_at(ms, n, word, cycle, 6)

    sand_ok = p1_fr or p3_fr
    nsand_ok = p5_fr or p6_fr

    fc = Counter(word)

    if not sand_ok and nsand_ok:
        sand_fail_nsand_ok.append((word, cycle, fc))
        fc_key = tuple(fc.get(p, 0) for p in range(n))
        fc_when_sand_fail[fc_key] += 1
    elif sand_ok and not nsand_ok:
        nsand_fail_sand_ok.append((word, cycle, fc))
        fc_key = tuple(fc.get(p, 0) for p in range(n))
        fc_when_nsand_fail[fc_key] += 1
    elif not sand_ok and not nsand_ok:
        both_fail.append((word, cycle, fc))

print(f"Total: {total}")
print(f"Sand fail + NSand OK: {len(sand_fail_nsand_ok)}")
print(f"NSand fail + Sand OK: {len(nsand_fail_sand_ok)}")
print(f"BOTH fail (BUG if >0): {len(both_fail)}")

# PART 1: Analyze fire counts when sandwiched fails
print(f"\n{'='*60}")
print("WHEN SANDWICHED (P1,P3) BOTH FAIL:")
print(f"  Total: {len(sand_fail_nsand_ok)} cycles")

if sand_fail_nsand_ok:
    print(f"\n  Fire count distributions:")
    for fc_key, cnt in sorted(fc_when_sand_fail.items(), key=lambda x: -x[1])[:10]:
        print(f"    fc={list(fc_key)}: {cnt}")

    # Analyze phase structure at P5 and P6 for these cycles
    p5_jk_here = Counter()
    p6_jk_here = Counter()
    p5_which_phase_fr = Counter()  # which phase of P5 has FR

    for word, cycle, fc in sand_fail_nsand_ok[:200]:
        phases5 = phase_jk_parities(ms, n, word, cycle, 5)
        phases6 = phase_jk_parities(ms, n, word, cycle, 6)

        for ph in phases5:
            p5_jk_here[(ph['J'], ph['K'])] += 1
            if ph['fr']:
                p5_which_phase_fr[ph['k']] += 1

        for ph in phases6:
            p6_jk_here[(ph['J'], ph['K'])] += 1

    print(f"\n  P5 (J,K) when sand fails:")
    for (J,K), cnt in sorted(p5_jk_here.items()):
        ret = "RET" if J % ms[4] == 0 and K % ms[6] == 0 else ""
        print(f"    J={J}, K={K}: {cnt}  {ret}")

    print(f"\n  P6 (J,K) when sand fails (bL=P5(3), bR=P0(2)):")
    for (J,K), cnt in sorted(p6_jk_here.items()):
        ret = "RET" if J % ms[5] == 0 and K % ms[0] == 0 else ""
        print(f"    J={J}, K={K}: {cnt}  {ret}")

    print(f"\n  P5 which phase has FR: {dict(p5_which_phase_fr)}")

# PART 2: Analyze fire counts when non-sandwiched fails
print(f"\n{'='*60}")
print("WHEN NON-SANDWICHED (P5,P6) BOTH FAIL:")
print(f"  Total: {len(nsand_fail_sand_ok)} cycles")

if nsand_fail_sand_ok:
    print(f"\n  Fire count distributions:")
    for fc_key, cnt in sorted(fc_when_nsand_fail.items(), key=lambda x: -x[1])[:10]:
        print(f"    fc={list(fc_key)}: {cnt}")

    p1_jk_here = Counter()
    p3_jk_here = Counter()
    p1_which_phase_fr = Counter()

    for word, cycle, fc in nsand_fail_sand_ok[:200]:
        phases1 = phase_jk_parities(ms, n, word, cycle, 1)
        phases3 = phase_jk_parities(ms, n, word, cycle, 3)

        for ph in phases1:
            p1_jk_here[(ph['J'], ph['K'])] += 1
            if ph['fr']:
                p1_which_phase_fr[ph['k']] += 1

        for ph in phases3:
            p3_jk_here[(ph['J'], ph['K'])] += 1

    print(f"\n  P1 (J,K) when nsand fails (bL=P0(2), bR=P2(2)):")
    for (J,K), cnt in sorted(p1_jk_here.items()):
        ret = "RET" if J % 2 == 0 and K % 2 == 0 else ""
        print(f"    J={J}, K={K}: {cnt}  {ret}")

    print(f"\n  P3 (J,K) when nsand fails:")
    for (J,K), cnt in sorted(p3_jk_here.items()):
        ret = "RET" if J % 2 == 0 and K % 2 == 0 else ""
        print(f"    J={J}, K={K}: {cnt}  {ret}")

    print(f"\n  P1 which phase has FR: {dict(p1_which_phase_fr)}")

# PART 3: Fire count coupling
print(f"\n{'='*60}")
print("FIRE COUNT COUPLING ANALYSIS")

# For ALL cycles, tabulate (fc[0], fc[2], fc[4]) = binary fire counts
# and the failure pattern
fc_binary_vs_pattern = Counter()
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    fc = Counter(word)
    fc_b = (fc.get(0,0), fc.get(2,0), fc.get(4,0))

    p1_fr = has_entry_conflict_at(ms, n, word, cycle, 1)
    p3_fr = has_entry_conflict_at(ms, n, word, cycle, 3)
    p5_fr = has_entry_conflict_at(ms, n, word, cycle, 5)
    p6_fr = has_entry_conflict_at(ms, n, word, cycle, 6)

    pattern = ('P1' if p1_fr else '-', 'P3' if p3_fr else '-',
               'P5' if p5_fr else '-', 'P6' if p6_fr else '-')
    fc_binary_vs_pattern[(fc_b, pattern)] += 1

# Show which binary fc's allow sandwiched-fail
print(f"\n  Binary fire counts when P1 AND P3 fail:")
for (fc_b, pattern), cnt in sorted(fc_binary_vs_pattern.items(), key=lambda x: -x[1]):
    if pattern[0] == '-' and pattern[1] == '-':
        print(f"    fc_binary={fc_b}: pattern={pattern}, count={cnt}")

print(f"\n  Binary fire counts when P5 AND P6 fail:")
for (fc_b, pattern), cnt in sorted(fc_binary_vs_pattern.items(), key=lambda x: -x[1]):
    if pattern[2] == '-' and pattern[3] == '-':
        print(f"    fc_binary={fc_b}: pattern={pattern}, count={cnt}")

# PART 4: Does the binary fire count DETERMINE the failure pattern?
print(f"\n{'='*60}")
print("DO BINARY FIRE COUNTS PREDICT FAILURE?")

fc_binary_to_patterns = {}
for (fc_b, pattern), cnt in fc_binary_vs_pattern.items():
    if fc_b not in fc_binary_to_patterns:
        fc_binary_to_patterns[fc_b] = Counter()
    fc_binary_to_patterns[fc_b][pattern] += cnt

for fc_b in sorted(fc_binary_to_patterns.keys()):
    patterns = fc_binary_to_patterns[fc_b]
    total_here = sum(patterns.values())
    if total_here < 10:
        continue
    sand_fail = sum(v for p, v in patterns.items() if p[0] == '-' and p[1] == '-')
    nsand_fail = sum(v for p, v in patterns.items() if p[2] == '-' and p[3] == '-')
    print(f"  fc_b={fc_b}: {total_here} cycles, "
          f"sand_fail={sand_fail} ({100*sand_fail/total_here:.0f}%), "
          f"nsand_fail={nsand_fail} ({100*nsand_fail/total_here:.0f}%)")

print(f"\nTotal: {time.time()-t0:.1f}s")
