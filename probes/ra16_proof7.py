#!/usr/bin/env python3
"""
RA16 Part 7: The proof via excursion direction.

INSIGHT from Part 6: each binary b with fc=2 has two excursions.
Each excursion goes to one side (if short) or both sides (if long).

With >= 3 binary procs, even if one binary b has long excursions,
the OTHER binary procs might have short excursions.

KEY STRUCTURAL OBSERVATION:
In a zero-winding walk, the walk goes CW and CCW an equal number of steps.
The walk's "runs" (maximal monotone subsequences) alternate direction.

Consider the binary procs b_1, b_2, b_3 (at least 3). Each fires exactly
2 times (if at minimum fc). The walk visits each exactly twice.

Between b's two visits to b_i, the walk makes an excursion. If the
excursion goes to the LEFT of b_i, it doesn't reach the RIGHT side
(if short). Since the ring has n >= 9 procs and the binary procs are
spaced out (at least some are far apart), the excursions of different
binary procs are likely on different sides.

Actually, the key might be: the 3 binary procs split the ring into arcs.
If they're at positions a, b, c (on C_n), the arcs have lengths that sum
to n. With n >= 9, at least one arc has length >= 3 (since 9/3 = 3).
A binary proc adjacent to a long arc...

Let me try a DIFFERENT approach entirely.

PROOF BY EXHAUSTION OF EXCURSION DIRECTIONS:

For binary b with fc = 2, define:
- dir1(b) = direction the walk goes at b's first firing (CW or CCW)
- dir2(b) = direction the walk goes at b's second firing (CW or CCW)

If dir1(b) ≠ dir2(b) (one CW, one CCW): one excursion goes left and one goes right.
If the shorter excursion has length < n-2: it's one-sided.

If dir1(b) = dir2(b) (both CW or both CCW): the walk passes through b in the
same direction both times. The excursions both go in the same direction... no.
Actually the excursion direction depends on where the walk goes AFTER b fires.

Wait. Let me redefine. When b fires at step s_1:
- Step s_1 - 1: walk was at neighbor A of b. Walk moved to b.
- Step s_1: b fires.
- Step s_1 + 1: walk moves to neighbor B of b.
The "departure direction" is B. The "arrival direction" is A.

If A = left(b) and B = right(b): walk came from left, goes right = "passing through CW"
If A = right(b) and B = left(b): walk came from right, goes left = "passing through CCW"
If A = left(b) and B = left(b): walk came from left, returns left = "turnaround at b, bouncing left"
If A = right(b) and B = right(b): walk came from right, returns right = "turnaround at b, bouncing right"

The departure direction at firing k determines the excursion direction.
Excursion after firing 1: goes in departure direction of firing 1.

TURNAROUND AT BINARY: if the walk bounces (A = B), b fires but the walk
stays on one side. The excursion after this firing goes to the same side
as the arrival.

Let me classify all cases:
- Firing 1: departs LEFT. Excursion 1 goes LEFT.
- Firing 2: arrives from LEFT (end of excursion 1 which went LEFT).
  - Departs LEFT (turnaround): excursion 2 also goes LEFT.
  - Departs RIGHT (passes through): excursion 2 goes RIGHT.

If excursion 1 goes LEFT and excursion 2 goes RIGHT:
- LEFT side fires 0 in excursion 2 (if short enough)
- RIGHT side fires 0 in excursion 1 (if short enough)
This is the "one excursion per side" case.

If both excursions go LEFT:
- RIGHT side fires 0 in BOTH excursions. right(b) fires 0 TOTAL. But fc(right(b)) >= 2.
  CONTRADICTION! right(b) fires at least 2 times total but fires 0 in all excursions.
  Wait: excursions are between b's firings. The walk's total steps = CL.
  All steps are in excursion 1, excursion 2, or at b (the 2 firings).
  So right(b) fires only during excursions (not at b-firings).
  If right(b) fires 0 in both excursions: fc(right(b)) = 0. But fc >= 2. CONTRADICTION.

  Unless excursions go LEFT but are long enough to wrap around and reach right(b).
  If excursion length >= n-2, the walk CAN reach the other side.

So: if b has a SHORT excursion (length < n-2), it must be one-sided, and the
other excursion must go the OTHER direction (to avoid the fc >= 2 contradiction).

THEOREM SKETCH:
1. With B >= 3 binary procs, each fc = 2, total binary fires = 2B.
2. CL = 3n - B + extra. For minimum: CL = 3n - B (each proc fires exactly m_p).
   But some fc >= 3, so CL >= 3n - B + 1.
3. Binary b has 2 excursions, total length CL - 2.
4. Shorter excursion: length <= floor((CL - 2)/2).
5. For CL = 3n - B + 1, shorter excursion <= floor((3n - B - 1)/2).
   For B = 3: floor((3n - 4)/2) = floor(3n/2 - 2).
   For n = 9: floor(11.5) = 11. n - 2 = 7. 11 > 7. NOT SHORT.

So the "short excursion" argument doesn't directly work for the minimum CL case
at n = 9. The excursion might be long.

But computationally it works 100% at n = 7. Let me check what's actually happening.
"""
import sys, os
from collections import Counter, defaultdict

sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', buffering=1)

def enumerate_zw_gap_words(ms, n, max_cl):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config, winding):
        if len(word) > max_cl:
            return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                if winding == 0 and any(fc[p] >= 3 for p in range(n)):
                    cw = sum(1 for i in range(len(word)-1) if (word[i]+1)%n == word[i+1])
                    if cw > 0 and cw < len(word) - 1:
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
            d = 1 if (last+1)%n == nxt else -1
            word.append(nxt)
            dfs(word, nf, tuple(nc), winding + d)
            word.pop()
    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first), 0)
    return results


# For each binary b with fc=2, classify arrival/departure at each firing
print("=" * 70)
print("ARRIVAL/DEPARTURE CLASSIFICATION AT BINARY FIRINGS")
print("=" * 70)

ms = [2,2,2,3,3,3,3]
n = 7
words = enumerate_zw_gap_words(ms, n, 24)
binary_pos = set(i for i in range(n) if ms[i] == 2)

pattern_counter = Counter()
for w in words:
    fc = Counter(w)
    CL = len(w)

    for b in binary_pos:
        if fc[b] != 2:
            continue
        fires = [k for k, m in enumerate(w) if m == b]

        patterns = []
        for s in fires:
            # Arrival: which neighbor did we come from?
            prev_step = (s - 1) % CL
            prev_mover = w[prev_step]
            arrival = 'L' if prev_mover == (b - 1) % n else 'R'

            # Departure: which neighbor do we go to?
            next_step = (s + 1) % CL
            next_mover = w[next_step]
            departure = 'L' if next_mover == (b - 1) % n else 'R'

            patterns.append(f"{arrival}{departure}")

        pattern_counter[tuple(patterns)] += 1

print(f"\nBinary firing patterns (arrival, departure):")
for pattern, cnt in sorted(pattern_counter.items(), key=lambda x: -x[1]):
    print(f"  {pattern}: {cnt}")

# Now: for the "good" binary procs (those that provide the phase),
# what's their arrival/departure pattern?
print("\n" + "=" * 70)
print("PROVIDER BINARY: arrival/departure pattern")
print("=" * 70)

provider_pattern = Counter()
for w in words:
    fc = Counter(w)
    CL = len(w)
    firing_steps = defaultdict(list)
    for k, m in enumerate(w):
        firing_steps[m].append(k)

    for b in binary_pos:
        if fc[b] != 2:
            continue
        fires_b = firing_steps[b]

        for t in [(b-1)%n, (b+1)%n]:
            if fc[t] < 2:
                continue
            steps_t = firing_steps[t]
            other_nbr = (t-1)%n if (t+1)%n == b else (t+1)%n

            for pi in range(len(steps_t)):
                a = steps_t[pi]
                s = steps_t[(pi+1) % len(steps_t)]
                bf = 0
                of_ = 0
                if s > a:
                    for k in range(a+1, s):
                        if w[k] == b: bf += 1
                        if w[k] == other_nbr: of_ += 1
                else:
                    for k in range(a+1, CL):
                        if w[k] == b: bf += 1
                        if w[k] == other_nbr: of_ += 1
                    for k in range(0, s):
                        if w[k] == b: bf += 1
                        if w[k] == other_nbr: of_ += 1

                if bf == 2 and of_ == 0:
                    # Found provider. Check arrival/departure pattern at b.
                    patterns = []
                    for fs in fires_b:
                        prev_mover = w[(fs-1) % CL]
                        next_mover = w[(fs+1) % CL]
                        arr = 'L' if prev_mover == (b-1)%n else 'R'
                        dep = 'L' if next_mover == (b-1)%n else 'R'
                        patterns.append(f"{arr}{dep}")
                    provider_pattern[tuple(patterns)] += 1
                    break
            else:
                continue
            break
        else:
            continue
        break

print(f"\nProvider binary patterns:")
for pattern, cnt in sorted(provider_pattern.items(), key=lambda x: -x[1]):
    print(f"  {pattern}: {cnt}")

# KEY: what fraction of binary procs are TURNAROUND points?
# A turnaround: arrival and departure same side (LL or RR)
print("\n" + "=" * 70)
print("TURNAROUND ANALYSIS")
print("=" * 70)

turnaround_count = Counter()
for w in words:
    fc = Counter(w)
    CL = len(w)

    for b in binary_pos:
        if fc[b] != 2:
            continue
        fires = [k for k, m in enumerate(w) if m == b]

        is_turnaround = [False, False]
        for idx, s in enumerate(fires):
            prev_mover = w[(s-1) % CL]
            next_mover = w[(s+1) % CL]
            if prev_mover == next_mover:  # Same side = turnaround
                is_turnaround[idx] = True

        turnaround_count[tuple(is_turnaround)] += 1

print(f"  Turnaround patterns (fire1, fire2):")
for pattern, cnt in sorted(turnaround_count.items(), key=lambda x: -x[1]):
    print(f"    {pattern}: {cnt}")
