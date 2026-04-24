#!/usr/bin/env python3
"""RA12 FINAL SUMMARY: Complete EC mechanism characterization.

PROVED: 100% of cycles have intra-phase EC at some processor.

Architecture for n=7:
- 6544 cycles (95.8%): EC at sandwiched t via double+NN mechanism
  (every fc=3 cycle has at least one phase with double same-side + non-neighbor)
- 288 cycles (4.2%): fc(t)=6, EC at other ternary procs

Now verify:
1. Is double+NN universal for fc(t)=3 at sandwiched t across architectures?
2. What is the EXACT condition that guarantees double same-side firing?
3. Can we prove it analytically?

ANALYTICAL ARGUMENT SKETCH:
For sandwiched t with fc(t)=3, each phase has exactly 1 mover step.
The phase is a contiguous interval of steps (between consecutive t-firings).
Within the phase, the walk traverses the ring.

For the (1,M) phase with M non-mover steps:
- The walk enters from a t-neighbor (previous step was a neighbor firing)
- The walk exits through t (the mover step)
- In between: the walk wanders, possibly firing tL and tR multiple times

For M >= 2: the walk must traverse at least 2 non-mover steps.
The step before the mover fires a t-neighbor (sm-1 fires tL or tR).

Claim: if ANY phase has >= 2 same-side neighbor firings, then that phase
has non-neighbor non-mover steps and gives EC.

Why >= 2 same-side firings?
The walk is a ring walk. To fire the same neighbor twice, the walk must
leave that neighbor and return. This creates intermediate steps that are
not at t's neighbors -> non-neighbor non-mover steps!

Actually that's the key: if tR fires at step s_a and s_b (s_a < s_b < sm):
Between s_a and s_b, the walk went tR -> somewhere -> tR.
Since it's a ring walk, it went tR -> tR+1 or tR-1.
If tR-1 = t: then it went to t, but t doesn't fire (this is the (1,1) phase).
  Actually t fires at sm. If the walk goes to t from tR at step s_a+1,
  and fires, then that's the mover step (sm = s_a+1). But then s_b wouldn't exist.
So: the walk goes tR -> tR+1 (not t).
tR+1 is NOT a neighbor of t (since t's neighbors are tL=t-1 and tR=t+1,
and tR+1 = t+2, which is only a neighbor of t if n <= 3).

So step s_a+1 fires tR+1, which is a non-neighbor of t.
This is a non-neighbor non-mover step in the phase!

And it comes BETWEEN the two tR firings.
By the return mechanism: at s_a+1, R has been toggled (R = 1-R_m),
but L is unchanged (L = L at s_a). After s_b, R returns to R at s_a.

Wait, the question is what L is at s_a+1.
L = c[tL] at step s_a+1. Has tL been fired since the start of the phase?
That depends on the walk.

HMPH. The argument needs more care for L.

Let me just verify computationally that double+NN universally implies EC,
and that fc(t)=3 universally implies double same-side in some phase.
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

# ===== VERIFY: fc(t)=3 at sandwiched t -> double same-side in some phase =====
print("=" * 70)
print("VERIFY: fc=3 at sandwiched t -> double same-side in some phase")
print("=" * 70)

for n, ms, max_len, label in [
    (5, [2,2,2,3,2], 16, "n=5"),
    (7, [2,2,2,3,2,3,3], 24, "n=7"),
    (7, [2,2,2,3,3,2,3], 24, "n=7b"),
]:
    print(f"\n{'='*70}")
    print(f"  {label}: ms={ms}")
    print(f"{'='*70}")

    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [t for t in range(n)
                  if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

    total = 0
    has_double_in_some_phase = 0
    no_double_anywhere = 0
    no_double_examples = []

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue

        ell = len(word)
        fc = Counter(word)

        for t in sandwiched:
            if fc[t] != 3:
                continue
            total += 1

            tL = (t - 1) % n
            tR = (t + 1) % n

            found_double = False
            for pv in range(3):
                phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
                t_nonmover = [s for s in phase_steps if word[s] != t]

                nL = sum(1 for s in t_nonmover if word[s] == tL)
                nR = sum(1 for s in t_nonmover if word[s] == tR)

                if nL >= 2 or nR >= 2:
                    found_double = True
                    break

            if found_double:
                has_double_in_some_phase += 1
            else:
                no_double_anywhere += 1
                if len(no_double_examples) < 3:
                    no_double_examples.append((word, t))

    print(f"fc=3 instances at sandwiched t: {total}")
    print(f"  Has double same-side in some phase: {has_double_in_some_phase} ({100*has_double_in_some_phase/max(1,total):.1f}%)")
    print(f"  No double same-side anywhere: {no_double_anywhere}")

    if no_double_examples:
        print(f"\n  No-double examples:")
        for word, t in no_double_examples:
            cycle = build_cycle(ms, n, word)
            ell = len(word)
            tL = (t - 1) % n
            tR = (t + 1) % n
            print(f"    word_len={ell}, t={t}")
            for pv in range(3):
                phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
                t_nonmover = [s for s in phase_steps if word[s] != t]
                nL = sum(1 for s in t_nonmover if word[s] == tL)
                nR = sum(1 for s in t_nonmover if word[s] == tR)
                nO = len(t_nonmover) - nL - nR
                print(f"      Phase {pv}: tL={nL}, tR={nR}, other={nO}")

# ===== COUNTING ARGUMENT =====
print("\n" + "=" * 70)
print("COUNTING: Why double same-side is guaranteed")
print("=" * 70)

# For sandwiched t with fc(t)=3:
# Each phase has 1 mover step.
# Total neighbor firings across all phases = fc(tL) + fc(tR) = 2 + 2 = 4
# (since m_{tL}=m_{tR}=2, fc must be a multiple of 2; min is 2)
# Wait: fc(tL) and fc(tR) must be multiples of m_{tL}=2 and m_{tR}=2.
# So fc(tL) >= 2, fc(tR) >= 2. Total neighbor firings >= 4.
#
# These 4+ neighbor firings are distributed among 3 phases.
# By pigeonhole: at least one phase has >= ceil(4/3) = 2 neighbor firings.
# But 2 neighbor firings could be 1 tL + 1 tR (no double same-side!).
#
# Actually: total fc(tL) + fc(tR) = 4. Distributed in 3 phases.
# Pigeonhole gives at least one phase with >= 2 total neighbor firings.
# But this could be (1,1) — one tL, one tR.
#
# To get double same-side: need some phase with >= 2 tL or >= 2 tR.
# This fails if: every phase has at most 1 tL and at most 1 tR.
# With fc(tL)=2 and fc(tR)=2: distribute 2 tL-firings in 3 phases
# and 2 tR-firings in 3 phases, each at most 1 per phase.
# This IS possible: e.g., phase 0 gets (1,1), phase 1 gets (1,1), phase 2 gets (0,0).
#
# So pigeonhole alone doesn't work.
# But: the (0,0) phase has NO neighbor firings.
# In that phase: only the mover step + non-neighbor steps.
# The mover step fires t, and no neighbors fire in the phase.
# This means: the walk enters the phase, does not fire any t-neighbor,
# and exits by firing t.
# Ring walk: step before mover is at a t-neighbor.
# So sm-1 fires a t-neighbor — but that's in this phase!
# Contradiction: phase 2 has (0,0) neighbor firings but sm-1 fires a neighbor.
#
# Wait, sm-1 IS a neighbor firing. So it MUST be counted.
# So every phase has at least 1 neighbor firing from the sm-1 step.
# That means: 4 neighbor firings, 3 phases, each phase has >= 1.
# By pigeonhole: at least one phase has >= 2. Still only (1,1) possible.

# WAIT: what about the step AFTER the previous mover?
# The previous mover step fires t. The next step (first step of this phase)
# fires a t-neighbor (ring walk). So the first step of each phase also
# fires a neighbor!
#
# So each phase has at least 2 neighbor firings: the first step and the last (sm-1).
# Total: >= 6 neighbor firings across 3 phases.
# But actual total = fc(tL) + fc(tR) = 4.
#
# That's a contradiction! Unless the first step of one phase is the same
# as the last step of the previous phase... no, steps are different.

# Let me recount. The walk around the cycle is:
# ... -> t fires (phase boundary) -> neighbor fires -> ... -> neighbor fires -> t fires -> ...
# Each "neighbor fires" at the boundary counts toward one phase.
# The step RIGHT AFTER t fires belongs to the NEXT phase (t's value just changed).
# The step RIGHT BEFORE t fires belongs to the CURRENT phase.
#
# So: the first step of each phase (right after previous t-firing) fires a neighbor.
# The last non-mover step of each phase (right before this t-firing) fires a neighbor.
# Are these the SAME neighbor firing? Only if the phase has exactly 2 steps
# (the neighbor-fire and the t-fire).
#
# If the phase has > 2 steps: first and last neighbor firings are different.
# So each phase with > 2 steps contributes >= 2 to the neighbor count.
#
# How many neighbor firings total?
# fc(tL) + fc(tR) = 4 minimum (2+2).
#
# If all 3 phases contribute >= 2: total >= 6 > 4. Contradiction!
# So at most 2 phases can have >= 2 neighbor firings.
# The third phase must have only 1 neighbor firing (= 2 steps: neighbor + mover).
#
# Actually wait: a phase with 2 steps has 1 non-mover step (the neighbor).
# That's a (M, N) = (1, 1) distribution: 1 mover, 1 non-mover.
# The non-mover IS the neighbor firing. It's both the first and last nm step.
# So 1 neighbor firing, not 2.
#
# Phase with 3 steps: nm1 + nm2 + mover. nm1 is first (neighbor), nm2 is last (neighbor).
# These could be the same neighbor or different neighbors.
# 2 neighbor firings from this phase.
#
# So: phases with 2 steps contribute 1 neighbor firing each.
# Phases with >= 3 steps contribute >= 2.
# Let k phases have 2 steps, (3-k) phases have >= 3 steps.
# Total neighbor firings >= k*1 + (3-k)*2 = 6 - k.
# Must have 6 - k <= total fc(tL) + fc(tR) = 4, so k >= 2.
#
# So: at least 2 phases have exactly 2 steps (1 nm, 1 mover).
# The third phase has all the remaining steps.
#
# fc(tL) + fc(tR) = 4. Two 2-step phases contribute 1 each = 2.
# Remaining 2 neighbor firings go to the third phase.
# Third phase has 2 neighbor firings. Could be (2,0), (0,2), or (1,1).
# If (2,0) or (0,2): DOUBLE SAME-SIDE in the third phase. Done!
# If (1,1): both sides fire once in the third phase. No double.

# So the question reduces to: in the "big" phase (3rd phase),
# can the 2 neighbor firings be (1 tL, 1 tR) instead of (2 tL) or (2 tR)?

# YES! This is possible. The walk enters from one side, crosses through,
# and comes back from the other side.

# Check: how often does this happen?
print("Phase size distribution for fc=3 at sandwiched t:")

n = 7
ms = [2, 2, 2, 3, 2, 3, 3]
max_len = 24

words = enumerate_mover_words(ms, n, max_len)
sandwiched = [t for t in range(n)
              if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

phase_size_dist = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    ell = len(word)
    fc = Counter(word)

    for t in sandwiched:
        if fc[t] != 3:
            continue
        tL = (t - 1) % n
        tR = (t + 1) % n

        sizes = []
        for pv in range(3):
            phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
            sizes.append(len(phase_steps))

        phase_size_dist[tuple(sorted(sizes))] += 1

print(f"Phase size distribution (sorted):")
for sizes, cnt in sorted(phase_size_dist.items(), key=lambda x: -x[1]):
    print(f"  {sizes}: {cnt}")

# ===== BIG PHASE NEIGHBOR PATTERN =====
print("\nBig phase (largest) neighbor pattern:")

big_phase_pattern = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    ell = len(word)
    fc = Counter(word)

    for t in sandwiched:
        if fc[t] != 3:
            continue
        tL = (t - 1) % n
        tR = (t + 1) % n

        # Find biggest phase
        best_pv = max(range(3), key=lambda pv: len([s for s in range(ell) if cycle[s][t] == pv]))

        phase_steps = [s for s in range(ell) if cycle[s][t] == best_pv]
        t_nonmover = [s for s in phase_steps if word[s] != t]

        nL = sum(1 for s in t_nonmover if word[s] == tL)
        nR = sum(1 for s in t_nonmover if word[s] == tR)
        nO = len(t_nonmover) - nL - nR

        big_phase_pattern[(nL, nR, nO)] += 1

print("Big phase (tL, tR, other):")
for pat, cnt in sorted(big_phase_pattern.items(), key=lambda x: -x[1]):
    has_double = pat[0] >= 2 or pat[1] >= 2
    print(f"  {pat}: {cnt} {'[DOUBLE]' if has_double else ''}")
