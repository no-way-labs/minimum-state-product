#!/usr/bin/env python3
"""RA12 PARITY PROOF: Why same-side entry/exit is guaranteed.

KEY: Each phase boundary fires t. The step after t fires a neighbor.
The step before t fires a neighbor.

At each t-firing: the walk arrives from side A and departs to side B.
- Arrives from side A means: sm-1 fires A
- Departs to side B means: sm+1 fires B (this is the ENTRY of the next phase)

So: exit of phase i = arrival side = word[sm_i - 1] ∈ {tL, tR}
    entry of phase (i+1 mod 3) = departure side = word[sm_i + 1] ∈ {tL, tR}

These can be the SAME or DIFFERENT side.

For 3 phase boundaries (3 t-firings):
Each gives a pair (arrival_side, departure_side) = (exit_i, entry_{i+1}).

OBSERVATION: entry of phase i = departure side at boundary (i-1).
exit of phase i = arrival side at boundary i.

The sequence of sides around the 3 boundaries forms a pattern.
Let's encode: L=0, R=1. At each boundary, we have (arrival, departure) ∈ {0,1}^2.

For the big phase to have same-side entry/exit:
entry = exit, i.e., departure(prev_boundary) = arrival(this_boundary).

This means: at the boundary between the big phase and the next phase,
arrival_side = departure_side at the previous boundary.

Hmm, this is getting circular. Let me just check the PARITY of side changes.

At each of the 3 boundaries, the walk arrives from some side and departs to some side.
If arrive=depart (same side), call it "bounce".
If arrive≠depart (cross), call it "cross".

The entry/exit pattern of each phase is:
phase i: entry = depart(bound i-1), exit = arrive(bound i).
Same-side if depart(bound i-1) = arrive(bound i).

Now: cross boundaries change the "current side", bounces keep it.
Starting from any side, after 3 boundaries, we return to the start (cycle).
So: the number of "cross" boundaries must be EVEN (0 or 2).

If 0 crosses (all bounces): every phase has same entry/exit = same-side. 3 double phases.
If 2 crosses: two phases have cross entry/exit (different sides), one phase has same-side.

So: there's always at least 1 phase with same-side entry/exit!
And same-side implies double same-side (entry fires one neighbor, exit fires the same).

THIS IS THE PROOF!
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

# ===== VERIFY PARITY ARGUMENT =====
print("=" * 70)
print("PARITY PROOF: Bounce/Cross at phase boundaries")
print("=" * 70)

for n, ms, max_len, label in [
    (5, [2,2,2,3,2], 16, "n=5"),
    (7, [2,2,2,3,2,3,3], 24, "n=7"),
]:
    print(f"\n{'='*70}")
    print(f"  {label}: ms={ms}")
    print(f"{'='*70}")

    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [t for t in range(n)
                  if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

    cross_count_dist = Counter()

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

            n_crosses = 0
            for sm in t_mover_steps:
                arrive = word[(sm - 1) % ell]  # step before t fires
                depart = word[(sm + 1) % ell]  # step after t fires
                if arrive != depart:
                    n_crosses += 1

            cross_count_dist[n_crosses] += 1

    print(f"Number of crosses at 3 boundaries:")
    for n_cross, cnt in sorted(cross_count_dist.items()):
        print(f"  {n_cross} crosses: {cnt}")

    # Verify: always even
    odd_crosses = sum(cnt for n_cross, cnt in cross_count_dist.items() if n_cross % 2 == 1)
    print(f"  Odd number of crosses: {odd_crosses} (should be 0)")

# ===== VERIFY: same-side boundary implies double same-side in that phase =====
print("\n" + "=" * 70)
print("VERIFY: same-side entry/exit -> double same-side neighbor firing")
print("=" * 70)

for n, ms, max_len, label in [
    (5, [2,2,2,3,2], 16, "n=5"),
    (7, [2,2,2,3,2,3,3], 24, "n=7"),
]:
    print(f"\n{label}:")

    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [t for t in range(n)
                  if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

    same_side_phases = 0
    same_side_double = 0
    same_side_no_double = 0

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

                # Entry: step after prev_sm (first nm)
                entry = word[(prev_sm + 1) % ell]
                # Exit: step before sm (last nm)
                exit_ = word[(sm - 1) % ell]

                if entry == exit_:  # same-side
                    same_side_phases += 1

                    # Check double same-side
                    nm_steps = []
                    s = (prev_sm + 1) % ell
                    while s != sm:
                        nm_steps.append(s)
                        s = (s + 1) % ell

                    nL = sum(1 for s in nm_steps if word[s] == tL)
                    nR = sum(1 for s in nm_steps if word[s] == tR)

                    if nL >= 2 or nR >= 2:
                        same_side_double += 1
                    else:
                        same_side_no_double += 1

    print(f"  Same-side entry/exit phases: {same_side_phases}")
    print(f"    With double same-side: {same_side_double}")
    print(f"    Without double: {same_side_no_double}")

# ===== ALSO: For same-side double, verify non-neighbor step between =====
print("\n" + "=" * 70)
print("VERIFY: Double same-side -> non-neighbor nm between")
print("=" * 70)

n = 7
ms = [2, 2, 2, 3, 2, 3, 3]
max_len = 24

words = enumerate_mover_words(ms, n, max_len)
sandwiched = [t for t in range(n)
              if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

double_total = 0
double_has_nn_between = 0
double_no_nn_between = 0

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

            # Check for double same-side
            side_steps = {}
            for side in [tL, tR]:
                side_steps[side] = [s for s in nm_steps if word[s] == side]

            for side in [tL, tR]:
                if len(side_steps[side]) >= 2:
                    double_total += 1
                    # Non-neighbor between first and second?
                    s_first = side_steps[side][0]
                    s_second = side_steps[side][1]
                    between = []
                    s = (s_first + 1) % ell
                    while s != s_second:
                        if word[s] not in (tL, tR, t):
                            between.append(s)
                        s = (s + 1) % ell
                    if between:
                        double_has_nn_between += 1
                    else:
                        double_no_nn_between += 1

print(f"Double same-side instances: {double_total}")
print(f"  Non-neighbor step between firings: {double_has_nn_between}")
print(f"  No non-neighbor between: {double_no_nn_between}")

# ===== VERIFY: the complete chain: same-side -> double -> nn between -> EC =====
print("\n" + "=" * 70)
print("COMPLETE CHAIN: same-side entry/exit -> EC at t")
print("=" * 70)

def has_ec_at_proc(word, cycle, ms, n, p):
    ell = len(word)
    pL = (p - 1) % n
    pR = (p + 1) % n
    mover_ctx = set()
    nonmover_ctx = set()
    for s in range(ell):
        ctx = (cycle[s][pL], cycle[s][p], cycle[s][pR])
        if word[s] == p:
            mover_ctx.add(ctx)
        else:
            nonmover_ctx.add(ctx)
    return bool(mover_ctx & nonmover_ctx)

for n, ms, max_len, label in [
    (5, [2,2,2,3,2], 16, "n=5"),
    (7, [2,2,2,3,2,3,3], 24, "n=7"),
    (7, [2,2,2,3,3,2,3], 24, "n=7b"),
]:
    print(f"\n{label}: ms={ms}")

    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [t for t in range(n)
                  if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

    total_fc3 = 0
    has_same_side = 0
    has_same_side_and_ec = 0
    has_ec_at_t = 0

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

            total_fc3 += 1

            t_mover_steps = sorted([s for s in range(ell) if word[s] == t])
            if len(t_mover_steps) != 3:
                continue

            found_same = False
            for i, sm in enumerate(t_mover_steps):
                prev_sm = t_mover_steps[(i - 1) % 3]
                entry = word[(prev_sm + 1) % ell]
                exit_ = word[(sm - 1) % ell]
                if entry == exit_:
                    found_same = True
                    break

            if found_same:
                has_same_side += 1

            ec = has_ec_at_proc(word, cycle, ms, n, t)
            if ec:
                has_ec_at_t += 1
            if found_same and ec:
                has_same_side_and_ec += 1

    print(f"  Total fc=3: {total_fc3}")
    print(f"  Has same-side phase: {has_same_side} ({100*has_same_side/max(1,total_fc3):.1f}%)")
    print(f"  Has EC at t: {has_ec_at_t} ({100*has_ec_at_t/max(1,total_fc3):.1f}%)")
    print(f"  Same-side AND EC: {has_same_side_and_ec}")
    print(f"  Same-side but no EC: {has_same_side - has_same_side_and_ec}")
