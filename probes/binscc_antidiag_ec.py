#!/usr/bin/env python3
"""For cycles where ALL fc=3 ternary are all anti-diagonal:
What mechanism forces EC? Focus on n=8 (k=4, all fc=3).

KEY OBSERVATION: On the alternating ring, the walk alternates B-T.
Between two T-firings (within a phase), the walk can't pass through T.
To visit BOTH bL and bR, the walk must traverse the ring (~2k-2 steps).

This means: in short phases, the walk visits ONLY ONE neighbor.
If J>0 and K>0 in a phase: the walk TRAVERSED THE RING.

For anti-diagonal phases with both J,K>0: the walk entered from one side
and traversed to the other. The ENTRY DIRECTION determines whether EC holds.

Check: does the walk's entry direction correlate with EC?
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

# n=8 analysis
print("=" * 70)
print("n=8: ANTI-DIAGONAL CYCLES — EC MECHANISM")
print("=" * 70)

n, ms = 8, [2,3,2,3,2,3,2,3]
t0 = time.time()
words = enumerate_mover_words(ms, n, 24)
sandwiched = [1, 3, 5, 7]

antidiag_cycles = []
total = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    total += 1
    ell = len(word)
    fc = Counter(word)

    all_antidiag = True
    for t in sandwiched:
        if fc[t] != 3:
            all_antidiag = False
            break
        bL, bR = (t-1)%n, (t+1)%n
        for k in range(3):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            if J % 2 == K % 2:  # both even → NOT anti-diagonal
                all_antidiag = False
                break
        if not all_antidiag:
            break

    if all_antidiag:
        antidiag_cycles.append((word, cycle))

print(f"Total: {total}, Anti-diagonal: {len(antidiag_cycles)} ({time.time()-t0:.1f}s)")

# For each anti-diagonal cycle: find which ternary has EC and what phase causes it
ec_phase_jk = Counter()
ec_entry_dir = Counter()  # entry direction at EC-giving phase

for word, cycle in antidiag_cycles:
    ell = len(word)
    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n
        for k in range(3):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            M = sum(1 for s in steps if word[s] == t)

            # Check phase EC
            m_lr, nm_lr = set(), set()
            for s in steps:
                lr = (cycle[s][bL], cycle[s][bR])
                if word[s] == t:
                    m_lr.add(lr)
                else:
                    nm_lr.add(lr)
            if m_lr & nm_lr:
                ec_phase_jk[(J, K)] += 1

                # Entry direction: where did the mover come from?
                mover_step = [s for s in steps if word[s] == t][0]
                prev_step = (mover_step - 1) % ell
                if word[prev_step] == bL:
                    ec_entry_dir[('from_bL', J, K)] += 1
                elif word[prev_step] == bR:
                    ec_entry_dir[('from_bR', J, K)] += 1
                else:
                    ec_entry_dir[('other', J, K)] += 1

print(f"\nEC-giving phase (J,K) in anti-diagonal cycles:")
for (J, K), cnt in sorted(ec_phase_jk.items(), key=lambda x: -x[1]):
    print(f"  ({J},{K}): {cnt}")

print(f"\nEntry direction at EC phase:")
for (dir, J, K), cnt in sorted(ec_entry_dir.items(), key=lambda x: -x[1])[:15]:
    print(f"  {dir} ({J},{K}): {cnt}")

# KEY: For (2,1) phase with EC: is bR ALWAYS the first neighbor to fire?
print(f"\n{'='*70}")
print("FIRST NEIGHBOR FIRING IN EC-GIVING ANTI-DIAGONAL PHASES")
print("=" * 70)

first_fire = Counter()  # who fires first in the phase: bL or bR
for word, cycle in antidiag_cycles:
    ell = len(word)
    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n
        for k in range(3):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)

            m_lr, nm_lr = set(), set()
            for s in steps:
                lr = (cycle[s][bL], cycle[s][bR])
                if word[s] == t:
                    m_lr.add(lr)
                else:
                    nm_lr.add(lr)
            has_ec = bool(m_lr & nm_lr)

            # Who fires first?
            first = None
            for s in steps:
                if word[s] == bL:
                    first = 'bL'
                    break
                elif word[s] == bR:
                    first = 'bR'
                    break
            first_fire[(J, K, first, has_ec)] += 1

print(f"(J,K,first_fire,has_ec):")
for (J, K, ff, ec), cnt in sorted(first_fire.items()):
    print(f"  ({J},{K}) first={ff} ec={ec}: {cnt}")

# Simpler view: for anti-diagonal phases, does first_fire=same_side_as_higher_count → EC?
print(f"\n{'='*70}")
print("DIRECTION HYPOTHESIS: EC ↔ first fire comes from the LESS-firing side")
print("=" * 70)

dir_hyp = Counter()
for word, cycle in antidiag_cycles:
    ell = len(word)
    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n
        for k in range(3):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            if J == 0 or K == 0:
                continue  # skip zero-side phases

            m_lr, nm_lr = set(), set()
            for s in steps:
                lr = (cycle[s][bL], cycle[s][bR])
                if word[s] == t:
                    m_lr.add(lr)
                else:
                    nm_lr.add(lr)
            has_ec = bool(m_lr & nm_lr)

            # Who fires first? And who fires more?
            first = None
            for s in steps:
                if word[s] == bL:
                    first = 'bL'
                    break
                elif word[s] == bR:
                    first = 'bR'
                    break

            if J > K:
                more_side = 'bL'
            elif K > J:
                more_side = 'bR'
            else:
                more_side = 'equal'

            if first == more_side:
                dir_hyp[('first=more', has_ec)] += 1
            elif more_side == 'equal':
                dir_hyp[('equal', has_ec)] += 1
            else:
                dir_hyp[('first=less', has_ec)] += 1

print(f"Direction hypothesis:")
for (cat, ec), cnt in sorted(dir_hyp.items()):
    print(f"  {cat}: ec={ec}: {cnt}")
