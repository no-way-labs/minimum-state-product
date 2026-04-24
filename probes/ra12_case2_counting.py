#!/usr/bin/env python3
"""RA12 COUNTING PROOF: Why double same-side is guaranteed.

SETUP: sandwiched ternary t with fc(t)=3, neighbors tL, tR are binary (fc=2 each).

Phase structure: 3 phases, each with exactly 1 mover step.
Ring walk constraint: sm-1 fires a t-neighbor, and s_{m+1} fires a t-neighbor
(where s_{m+1} is the first step of the next phase).

KEY CLAIM: In a ring walk, the step BEFORE t fires is always a t-neighbor,
AND the step AFTER t fires is always a t-neighbor.

So each phase boundary contributes:
- Last nm step of phase A fires a t-neighbor (belongs to phase A)
- First nm step of phase B fires a t-neighbor (belongs to phase B)

Each phase has >= 1 neighbor firing (its last nm step fires a neighbor).
If a phase has >= 2 nm steps: the first nm step (from previous boundary)
is ALSO a neighbor firing (different step). So >= 2 neighbor firings.

But wait: a phase with exactly 2 steps (1 nm + 1 mover) has its single nm
step being both the "first" and "last" nm step. So 1 neighbor firing.

Phase with 3+ steps: first and last nm steps are different -> >= 2 neighbor firings.

Total neighbor firings = fc(tL) + fc(tR) = 2 + 2 = 4.

Let k = number of 2-step phases (only 1 nm step).
Then (3-k) phases have >= 3 steps -> >= 2 neighbor firings each.
Total >= k*1 + (3-k)*2 = 6-k.
Since total = 4: 6-k <= 4, so k >= 2.

So at least 2 phases have exactly 2 steps. The third phase gets:
4 - 2 = 2 remaining neighbor firings. These could be:
(a) 2 tL, 0 tR
(b) 0 tL, 2 tR
(c) 1 tL, 1 tR

For (a) or (b): DOUBLE SAME-SIDE. Done.
For (c): need more analysis.

In case (c): the big phase has 1 tL and 1 tR firing, both at nm steps.
Question: are these the ONLY neighbor firings in the big phase?
Yes! (total = 4, 2 used by small phases, 2 left for big phase = 1 tL + 1 tR)

But the big phase has many nm steps. The first and last nm are neighbors.
What about the rest? They must be non-neighbors of t.

The walk enters the big phase by firing a t-neighbor (first nm step).
Then wanders through non-t-neighbors.
Then fires the other t-neighbor.
Then wanders more through non-t-neighbors.
Then fires t (mover step).

Wait: the walk enters from one side (say tR), wanders, then must return
to fire tL (the other neighbor), then wanders, then returns to fire tR or tL
again... but we said only 1 tL and 1 tR!

So the walk fires tR (entry), wanders to fire tL, then must return to fire t.
But to fire t, the walk must come from a t-neighbor. The last nm step fires
a t-neighbor. That's the SECOND neighbor firing. So:
- First nm: fires one of {tL, tR}
- Some later nm: fires the other of {tL, tR}
- Last nm (= sm-1): fires a t-neighbor. But we've used both neighbor firings!

AH: the last nm fires a t-neighbor, but that IS one of the two.
The first nm fires neighbor A, some middle nm fires neighbor B,
and the last nm fires neighbor A or B again -- but that would be a THIRD
neighbor firing! Contradiction with (c) having only 2 neighbor firings!

UNLESS: the "first nm" and the "last nm" are among the 2 neighbor firings.
Let me re-examine:

Phase has steps: [nm_1, nm_2, ..., nm_M, mover]
- nm_1: first step after previous t-firing -> fires a t-neighbor (ring walk from t)
- nm_M: step before mover -> fires a t-neighbor (ring walk to t)
- Between nm_1 and nm_M: other steps (non-neighbor of t, mostly)

nm_1 fires a neighbor (1 neighbor firing).
nm_M fires a neighbor (1 neighbor firing, possibly the same one).
In case (c): total = 2 neighbor firings = nm_1 + nm_M. No others!

So nm_1 fires one neighbor, nm_M fires the other (or the same).
If nm_1 fires tL and nm_M fires tR: (1,1) case.
If nm_1 fires tR and nm_M fires tL: (1,1) case.
If nm_1 fires tL and nm_M fires tL: (2,0) case = DOUBLE! Contradiction with (c).
If nm_1 fires tR and nm_M fires tR: (0,2) case = DOUBLE! Contradiction with (c).

Wait! If nm_1 and nm_M BOTH fire the same neighbor, that's case (a) or (b),
not (c). So in case (c), nm_1 fires one side and nm_M fires the other.

So case (c) is: entry from side A, exit through side B.
No double same-side in the big phase.

But: the big phase has at least 3 steps (since 2 small phases take 4 steps,
leaving L-4 >= 2n-4 steps for the big phase; for n>=5, that's >=6 steps).
With only 2 neighbor firings (nm_1 and nm_M), all intermediate nm steps
are non-neighbor steps.

Can this actually happen? Let me verify.
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

# ===== Verify the phase boundary structure =====
print("=" * 70)
print("VERIFY: First and last nm steps are always neighbor firings")
print("=" * 70)

for n, ms, max_len, label in [
    (5, [2,2,2,3,2], 16, "n=5"),
    (7, [2,2,2,3,2,3,3], 24, "n=7"),
]:
    print(f"\n{label}: ms={ms}")

    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [t for t in range(n)
                  if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

    total_phases = 0
    first_is_neighbor = 0
    last_is_neighbor = 0

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

            # Find the 3 mover steps for t
            t_mover_steps = sorted([s for s in range(ell) if word[s] == t])
            if len(t_mover_steps) != 3:
                continue

            for i, sm in enumerate(t_mover_steps):
                # Phase starts after previous mover step
                prev_sm = t_mover_steps[(i - 1) % 3]

                # Non-mover steps in this phase
                nm_steps = []
                s = (prev_sm + 1) % ell
                while s != sm:
                    nm_steps.append(s)
                    s = (s + 1) % ell

                if len(nm_steps) == 0:
                    continue  # degenerate

                total_phases += 1

                # First nm step
                if word[nm_steps[0]] in (tL, tR):
                    first_is_neighbor += 1

                # Last nm step
                if word[nm_steps[-1]] in (tL, tR):
                    last_is_neighbor += 1

    print(f"Total phases: {total_phases}")
    print(f"First nm is neighbor: {first_is_neighbor}/{total_phases}")
    print(f"Last nm is neighbor: {last_is_neighbor}/{total_phases}")

# ===== Verify the phase size distribution =====
print("\n" + "=" * 70)
print("VERIFY: At least 2 phases have exactly 2 steps")
print("=" * 70)

for n, ms, max_len, label in [
    (5, [2,2,2,3,2], 16, "n=5"),
    (7, [2,2,2,3,2,3,3], 24, "n=7"),
]:
    print(f"\n{label}:")

    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [t for t in range(n)
                  if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

    min_small_phases = Counter()

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue

        ell = len(word)
        fc = Counter(word)

        for t in sandwiched:
            if fc[t] != 3:
                continue

            t_mover_steps = sorted([s for s in range(ell) if word[s] == t])
            if len(t_mover_steps) != 3:
                continue

            sizes = []
            for i, sm in enumerate(t_mover_steps):
                prev_sm = t_mover_steps[(i - 1) % 3]
                nm_count = 0
                s = (prev_sm + 1) % ell
                while s != sm:
                    nm_count += 1
                    s = (s + 1) % ell
                sizes.append(nm_count + 1)  # +1 for mover

            n_small = sum(1 for sz in sizes if sz == 2)
            min_small_phases[n_small] += 1

    print(f"Number of 2-step phases: {dict(sorted(min_small_phases.items()))}")

# ===== BIG PHASE ANALYSIS: entry/exit sides =====
print("\n" + "=" * 70)
print("BIG PHASE: Entry and exit sides")
print("=" * 70)

n = 7
ms = [2, 2, 2, 3, 2, 3, 3]
max_len = 24

words = enumerate_mover_words(ms, n, max_len)
sandwiched = [t for t in range(n)
              if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

entry_exit = Counter()
big_phase_details = Counter()

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

        t_mover_steps = sorted([s for s in range(ell) if word[s] == t])
        if len(t_mover_steps) != 3:
            continue

        for i, sm in enumerate(t_mover_steps):
            prev_sm = t_mover_steps[(i - 1) % 3]

            nm_steps = []
            s = (prev_sm + 1) % ell
            while s != sm:
                nm_steps.append(s)
                s = (s + 1) % ell

            if len(nm_steps) < 2:
                continue

            # Entry (first nm) and exit (last nm)
            first_m = word[nm_steps[0]]
            last_m = word[nm_steps[-1]]

            entry = 'L' if first_m == tL else ('R' if first_m == tR else '?')
            exit_ = 'L' if last_m == tL else ('R' if last_m == tR else '?')

            entry_exit[(entry, exit_)] += 1

            # Count all neighbor firings in the phase
            nL = sum(1 for s in nm_steps if word[s] == tL)
            nR = sum(1 for s in nm_steps if word[s] == tR)
            nO = len(nm_steps) - nL - nR

            big_phase_details[(entry, exit_, nL, nR, nO)] += 1

print("Entry/Exit pattern for phases with >= 2 nm steps:")
for pat, cnt in sorted(entry_exit.items(), key=lambda x: -x[1]):
    print(f"  entry={pat[0]}, exit={pat[1]}: {cnt}")

print("\nDetailed (entry, exit, tL_fires, tR_fires, other):")
for pat, cnt in sorted(big_phase_details.items(), key=lambda x: -x[1]):
    has_double = pat[2] >= 2 or pat[3] >= 2
    print(f"  {pat}: {cnt} {'[DOUBLE]' if has_double else ''}")
