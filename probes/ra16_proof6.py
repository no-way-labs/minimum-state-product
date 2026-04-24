#!/usr/bin/env python3
"""
RA16 Part 6: New proof approach.

KEY FINDING: the provider t often has fc(t) = 2, not fc(t) >= 3.

NEW INSIGHT: We don't need t to have fc >= 3. The theorem just needs
SOME t with SOME phase where:
- binary neighbor fires even >= 2
- other neighbor fires 0

The "other neighbor fires 0" is the hard part. When does this happen?

WALK TOPOLOGY ARGUMENT:
A phase of t (between two firings of t) = the walk leaves t, visits procs,
returns to t. If the phase is one-sided, one neighbor fires 0.

A phase of length L is one-sided if L < n-2 (walk can't reach both sides).

For t with fc(t) = 2: TWO phases, total length CL - 2.
Shorter phase: length <= floor((CL-2)/2).
Need this < n-2, i.e., CL < 2n - 2. But CL >= 2n. Fails.

So for fc(t) = 2 at the minimum CL, both phases have length >= n-1.
The walk CAN visit both neighbors.

But the data shows it works anyway! So the one-sidedness must come from
a different mechanism at fc(t) = 2.

Let me look at the SPECIFIC mechanism: when t has fc(t) = 2 and a binary
neighbor b has both fires in one phase of t with the other side silent.

What's happening: b fires 2 times, both in one phase of t. The other
phase of t has b firing 0 times. The binary's fires are CONCENTRATED on
one side, and the other side of t is silent in that phase.

KEY: the binary b is BETWEEN t and the silent region. The walk, during
the phase where b fires twice, stays on b's side. It bounces between
b and farther procs on b's side.

Actually, let me look at it from b's perspective.

b fires at steps s1, s2 (fc=2).
EXCURSION 1: steps [s1+1, s2-1]. Walk goes from b to one side, bounces, returns.
EXCURSION 2: steps [s2+1, s1-1] (wrapping). Walk goes from b to one side, bounces, returns.

If excursion 1 goes LEFT and excursion 2 goes RIGHT:
- In excursion 1: procs on the LEFT fire. RIGHT side fires 0.
- In excursion 2: procs on the RIGHT fire. LEFT side fires 0.

Now: t is a neighbor of b. Say t = left(b). Then in excursion 2 (goes RIGHT),
t fires 0 times. And the entire excursion 2 is within a phase of t.
In that phase, b fires... wait, b fires at s2 (start of excursion 2) and at s1
(end of excursion 2, wrapping). So both b-fires bracket excursion 2.
The excursion 2 is between s2 and s1, so b fires AT s2 and s1 but not
in between. t doesn't fire in excursion 2.

Hmm, the phase of t INCLUDES b's fires. Let me be precise.

The phase of t goes from one firing of t to the next. If t's fires are at
steps u1 and u2, then one phase is (u1, u2) exclusive and the other is (u2, u1).

For b's fires at s1, s2 to both be in phase (u1, u2): we need
u1 < s1 < s2 < u2 (or the cyclic version).

If the walk in excursion 1 (s1 to s2) goes LEFT (toward t = left(b)):
the walk visits t at some point in excursion 1. So t fires in excursion 1.
This means t fires BETWEEN s1 and s2.

If the walk in excursion 2 (s2 to s1) goes RIGHT (away from t = left(b)):
the walk doesn't visit t in excursion 2. So t doesn't fire in excursion 2.
But t fires in excursion 1 (between s1 and s2).

With fc(t) = 2 and both t-fires in excursion 1: the excursion 2 interval
is WITHIN a phase of t (from t's second fire in excursion 1 to t's first
fire in the next cycle). Wait, that's getting confusing.

Let me just think about it sequentially:
- s1: b fires
- ... (excursion 1, goes LEFT through t) ...
  - u1: t fires (first time)
  - ... (more stuff on left side) ...
  - u2: t fires (second time)
  - ... (returns to b) ...
- s2: b fires
- ... (excursion 2, goes RIGHT, t doesn't fire) ...
- s1 (next cycle)

So t's phases are:
Phase A: from u1 to u2, containing middle of excursion 1.
Phase B: from u2 to u1 (wrapping), containing end of excursion 1, s2, excursion 2, s1, start of excursion 1.

In Phase B: b fires at s2 and s1. That's 2 fires. Even, >= 2.
And t's other neighbor: if t = left(b), t's other neighbor = left(t) = b-2.
Does b-2 fire in Phase B?

Phase B goes from u2 to u1 (wrapping). It includes:
- End of excursion 1 (from u2 to s2): walk is returning to b from the left side.
  The walk might visit b-2 during this part.
- s2: b fires (the walk is at b).
- Excursion 2 (s2 to s1): walk goes RIGHT from b. Doesn't visit left side at all.
  b-2 fires 0 times here.
- s1: b fires.
- Start of excursion 1 (s1 to u1): walk goes LEFT from b toward t.
  The walk passes through t (at u1), so it visits b-2? Only if it goes far enough.

Hmm, the walk from s1 goes left: b -> t = b-1 -> possibly b-2.
If t fires at u1 and u1 = s1 + 1 (walk goes straight to t and t fires):
then the start of excursion 1 from s1 to u1 is just 1 step (b fires at s1,
then t fires at s1+1). In Phase B, this portion is from s1 to u1, which is
just 1 step. b-2 = left(t) fires 0 in this 1 step.

Similarly: end of excursion 1 from u2 to s2. How many steps? If the walk
bounces back from the left side and returns through t to b:
The walk goes ... -> t -> b -> (s2: b fires). So from u2 to s2, the walk
goes from left side back to b. This could visit b-2 along the way.

This is getting complicated. Let me approach it differently with a cleaner argument.

CLEAN ARGUMENT ATTEMPT:
======================

Consider the DIRECTIONS of the walk at each step.
The walk is a cyclic sequence of adjacent procs on C_n.
At each step, the walk moves CW (+1) or CCW (-1).

A "turnaround" occurs when the direction changes.
Between turnarounds, the walk goes in one direction (a "run").

Zero winding means: sum of all direction steps = 0. So number of CW steps =
number of CCW steps = CL/2 (if CL is even).

Now, at each turnaround, the walk reverses direction. The proc at the turnaround
fires twice: once as the walk arrives, once as the walk departs in the new direction.
Wait, no. The mover word is w_0, w_1, ..., w_{CL-1}. At step k, proc w_k fires.
Step k+1: proc w_{k+1} fires. If w_{k+1} = w_k - 1 and w_k = w_{k-1} + 1
(arrived from left, depart to left = turnaround at w_k going from CW to CCW):
then w_k fires at step k only.

Actually turnarounds happen when w_{k-1} and w_{k+1} are the SAME neighbor
of w_k. That means w_k fires, and the walk departs in the opposite direction
from arrival. w_k fires just once at step k (not twice).

RUNS: a maximal sequence of consecutive CW or CCW steps.
In a CW run: w_i, w_i+1 = w_i + 1, w_i+2 = w_i + 2, ...
In a CCW run: w_i, w_i+1 = w_i - 1, ...

Each run visits a "segment" of the ring.

Now: the walk is a sequence of runs, alternating CW and CCW (since between
runs there's a turnaround). Zero winding means CW distance = CCW distance.

For binary proc b: b fires fc(b) times. Each firing is at a specific step
in some run. b can be:
1. At a turnaround point (direction reverses at b)
2. In the interior of a run (passing through b)
3. At the start/end of a run (but not a turnaround — this is the first/last step of the cycle)

For a binary b with fc = 2: b is visited exactly twice by the walk.
These two visits split into: at turnarounds, in runs, etc.

CLAIM: if binary b has fc = 2, then in at least one of its excursions,
the walk stays on one side. Equivalently: one excursion doesn't cross b
(which is trivially true since b fires at the endpoints of the excursion, not
in the middle).

Actually wait. The excursion BETWEEN b's two firings: the walk goes from b
to one neighbor, visits some procs, returns to b. Does the walk stay on one
side of b in this excursion?

For the excursion to cross from one side of b to the other, the walk would
need to pass through b. But b doesn't fire in the excursion interior.
The walk is a sequence of adjacent movers. To get from left(b) to right(b)
without b firing, the walk must go the LONG way around (n-2 steps minimum).

If the excursion has < n-2 steps: stays on one side. Guaranteed.
If the excursion has >= n-2 steps: MIGHT go around.

COMPUTATIONAL CHECK: at n=7 and n=9, for fc=2 binary, do excursions
ever go to both sides?
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


print("=" * 70)
print("EXCURSION ONE-SIDEDNESS FOR FC=2 BINARY")
print("=" * 70)

for ms, n, max_cl in [
    ([2,2,2,3,3,3,3], 7, 24),
]:
    print(f"\nms={ms}, n={n}")
    words = enumerate_zw_gap_words(ms, n, max_cl)

    binary_pos = set(i for i in range(n) if ms[i] == 2)

    both_onesided = 0
    one_onesided = 0
    neither_onesided = 0
    total_excursions = 0

    for w in words:
        fc = Counter(w)
        CL = len(w)

        for b in binary_pos:
            if fc[b] != 2:
                continue
            fires_b = [k for k, m in enumerate(w) if m == b]
            s1, s2 = fires_b
            left_b = (b-1) % n
            right_b = (b+1) % n

            # Excursion 1: (s1, s2) exclusive
            # Excursion 2: (s2, s1) wrapping

            onesided = [False, False]

            for exc_idx, (es, ee) in enumerate([(s1, s2), (s2, s1)]):
                if ee > es:
                    movers = [w[k] for k in range(es+1, ee)]
                else:
                    movers = [w[k] for k in range(es+1, CL)] + [w[k] for k in range(0, ee)]

                left_fires = movers.count(left_b)
                right_fires = movers.count(right_b)
                onesided[exc_idx] = (left_fires == 0) or (right_fires == 0)
                total_excursions += 1

            if onesided[0] and onesided[1]:
                both_onesided += 1
            elif onesided[0] or onesided[1]:
                one_onesided += 1
            else:
                neither_onesided += 1

    total_binary_instances = both_onesided + one_onesided + neither_onesided
    print(f"  Binary instances (fc=2): {total_binary_instances}")
    print(f"  Both excursions one-sided: {both_onesided} ({100*both_onesided/total_binary_instances:.1f}%)")
    print(f"  One excursion one-sided: {one_onesided} ({100*one_onesided/total_binary_instances:.1f}%)")
    print(f"  Neither one-sided: {neither_onesided} ({100*neither_onesided/total_binary_instances:.1f}%)")


# Check: when NEITHER excursion is one-sided, what's happening?
print("\n" + "=" * 70)
print("NEITHER-ONESIDED EXCURSION DETAILS")
print("=" * 70)

for ms, n, max_cl in [
    ([2,2,2,3,3,3,3], 7, 24),
]:
    print(f"\nms={ms}, n={n}")
    words = enumerate_zw_gap_words(ms, n, max_cl)
    binary_pos = set(i for i in range(n) if ms[i] == 2)

    neither_details = []
    for w in words:
        fc = Counter(w)
        CL = len(w)
        for b in binary_pos:
            if fc[b] != 2:
                continue
            fires_b = [k for k, m in enumerate(w) if m == b]
            s1, s2 = fires_b
            left_b = (b-1) % n
            right_b = (b+1) % n

            for es, ee in [(s1, s2), (s2, s1)]:
                if ee > es:
                    movers = [w[k] for k in range(es+1, ee)]
                else:
                    movers = [w[k] for k in range(es+1, CL)] + [w[k] for k in range(0, ee)]

                left_fires = movers.count(left_b)
                right_fires = movers.count(right_b)
                if left_fires > 0 and right_fires > 0:
                    if len(neither_details) < 3:
                        neither_details.append({
                            'word': w, 'b': b, 'exc': (es, ee),
                            'exc_len': len(movers),
                            'left_fires': left_fires, 'right_fires': right_fires,
                            'movers': movers
                        })

    print(f"  Neither-onesided excursion examples: {len(neither_details)}")
    for d in neither_details:
        print(f"    b={d['b']}, exc=[{d['exc'][0]}..{d['exc'][1]}), len={d['exc_len']}")
        print(f"    left({d['b']})={(d['b']-1)%n} fires {d['left_fires']}, right({d['b']})={(d['b']+1)%n} fires {d['right_fires']}")
        print(f"    movers: {d['movers']}")
        # Check: does the walk go around the ring?
        visited = set(d['movers'])
        print(f"    visited procs: {sorted(visited)}, n-2 others = {n-2}")


# KEY NEW TEST: For EVERY binary b with fc=2, check if b has at least
# one excursion where its fires are on the SAME SIDE as a neighbor t,
# and the other neighbor of t fires 0 in the containing phase of t.
print("\n" + "=" * 70)
print("FOR EACH WORD: does SOME binary b have an excursion where")
print("  - excursion is one-sided (toward side A)")
print("  - the phase of side_B containing the excursion has side_B's other neighbor silent?")
print("=" * 70)

for ms, n, max_cl in [
    ([2,2,2,3,3,3,3], 7, 24),
]:
    print(f"\nms={ms}, n={n}")
    words = enumerate_zw_gap_words(ms, n, max_cl)
    binary_pos = set(i for i in range(n) if ms[i] == 2)

    success = 0
    for w in words:
        fc = Counter(w)
        CL = len(w)
        firing_steps = defaultdict(list)
        for k, m in enumerate(w):
            firing_steps[m].append(k)

        found = False
        for b in binary_pos:
            if fc[b] != 2:
                continue
            fires_b = [k for k, m in enumerate(w) if m == b]
            s1, s2 = fires_b

            for side_B in [(b-1)%n, (b+1)%n]:
                side_A = (b+1)%n if side_B == (b-1)%n else (b-1)%n

                # Check each phase of side_B
                if fc[side_B] < 2:
                    continue
                steps_sB = firing_steps[side_B]
                other_of_sB = (side_B-1)%n if (side_B+1)%n == b else (side_B+1)%n

                for pi in range(len(steps_sB)):
                    a = steps_sB[pi]
                    s = steps_sB[(pi+1) % len(steps_sB)]

                    # Count b fires and other_of_sB fires in this phase
                    bf = 0
                    of_ = 0
                    if s > a:
                        for k in range(a+1, s):
                            if w[k] == b: bf += 1
                            if w[k] == other_of_sB: of_ += 1
                    else:
                        for k in range(a+1, CL):
                            if w[k] == b: bf += 1
                            if w[k] == other_of_sB: of_ += 1
                        for k in range(0, s):
                            if w[k] == b: bf += 1
                            if w[k] == other_of_sB: of_ += 1

                    if bf == 2 and of_ == 0:
                        found = True
                        break
                if found:
                    break
            if found:
                break
        if found:
            success += 1

    print(f"  Success: {success}/{len(words)} ({100*success/len(words):.1f}%)")
