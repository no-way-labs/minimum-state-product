#!/usr/bin/env python3
"""
RA16 Part 4: The walk-based proof.

KEY INSIGHT FROM COMPUTATION:
- At n=7, the theorem holds 100%
- The (1,1,0) distribution occurs but other (b,t) pairs provide the good phase
- With >=3 binary, there are many (b,t) choices

PROOF APPROACH:
Phase One-Sidedness Lemma: If a phase has length < n-2, the walk stays on one side.

Short Phase Lemma: For any proc t with fc(t) >= 3, at least one phase has
length <= floor((CL - fc(t)) / fc(t)).

Combined: if floor((CL - fc(t)) / fc(t)) < n-2, then t has a short one-sided phase.
In that phase, one neighbor fires 0.

Now: for the OPPOSITE side, we need a phase where a binary neighbor fires >= 2.
Since b's total fires = fc(b) and SOME phase has b firing 0 (short one-sided phase
on the other side), the remaining phases have b firing fc(b) >= 2.

But wait: we need these fc(b) fires to be in A SINGLE phase with the other
neighbor silent. The fires might spread across multiple phases.

NEW APPROACH: Use the walk's local structure near binary procs.

Consider a binary proc b with fc(b) = 2. b fires at steps s1 and s2.
Between s1 and s2 (the "excursion"), the walk goes from b to some neighbor,
wanders, and returns to b.

CLAIM: If the excursion length < n-2, the excursion stays on one side of b.
(Same argument as phase one-sidedness.)

If the excursion goes to the LEFT side of b:
- b-1 fires some number of times (>= 1 since the walk is on that side)
- b+1 fires 0 times (the walk doesn't reach there)

Now consider proc t = b+1 (right neighbor of b). In the interval [s1, s2),
b fires once (at s1) and b-1 = t-2 side fires some times. But the walk is
on the LEFT side of b, so it DOESN'T reach t+1 either (if excursion is short).
Actually t = b+1, so the walk is on the b-1 side, which is the t-2 side.
The walk doesn't reach b+1 = t at all during the excursion (except b fires at s1
and s2, which means the walk is at b, not at t).

Hmm wait. t = b+1. Is the walk ever at t during [s1, s2)? The walk starts at b
(fires at s1), goes left, stays on the left side, returns to b (fires at s2).
The walk never visits t = b+1 in this interval. So t doesn't fire in [s1, s2).

Now this means: the interval [s1, s2) is inside a PHASE of t (between two
consecutive firings of t). Because t doesn't fire in [s1, s2).

And in this phase of t, b fires at s1 (but s1 might be the phase start, i.e.,
t fires just before s1... no, s1 is when b fires, not t).

Let me reconsider. A phase of t is between two consecutive firings of t.
In that phase, b fires twice (both s1 and s2) IF the phase contains both s1 and s2.
But also, b fires 0 times in other phases of t.

Actually: if the walk doesn't visit t during [s1, s2), and [s1, s2) has length < n-2,
then [s1, s2) is contained within a single phase of t (no firing of t occurs in [s1, s2)).

And in this phase of t, both of b's firings (s1 and s2) occur.
Also: b-1's neighbor is b+1 (which is t). The other neighbor of t is t+1.
Does t+1 fire in this phase of t?

The walk in [s1+1, s2-1] is on the b-1 side. Step s2 is at b. Step s2+1 goes
to either b-1 or b+1 = t. If it goes to t, then t fires (this ends or starts
something). If it goes to b-1, the walk is still on the left side.

But the phase of t extends beyond [s1, s2]. Before s1 and after s2, the walk
might visit t+1. So t+1 could fire in the phase of t.

Hmm. Let me just carefully check: does the short excursion guarantee that
the phase of t containing it has t+1 silent?

No. The phase of t is LONGER than [s1, s2). The phase starts when t last fired
before s1, and ends when t next fires after s2 (or between). The walk might
visit t+1 in the parts of the phase outside [s1, s2).

So the one-sided excursion of b doesn't directly give us a one-sided phase of t.
But it gives us that both of b's fires are in one phase of t.

Then the question: does the OTHER neighbor of t fire 0 in that phase?

DIFFERENT APPROACH: Find t with a short one-sided phase where a binary
neighbor is on the active side and fires >= 2.

Forget about trying to get b's fires concentrated. Instead:

1. Find t with fc(t) >= 3 and a short phase (length < n-2).
2. In that phase, the walk goes to one side. Say left side.
3. The right neighbor of t fires 0 (silent).
4. The left neighbor of t fires >= 1 in this phase.
5. We need: left neighbor is binary AND fires even >= 2.

Issue: the left neighbor fires >= 1 but might fire just 1 time (odd).

When does left(t) fire exactly 1 time in a short phase?
If the phase is very short (length 1 or 2), left(t) fires 1.
If the phase is longer but still < n-2, left(t) might fire multiple times.

Actually: in a short one-sided phase of t, the walk goes:
t fires, walk goes to left(t), bounces around on the left side, returns to
left(t), and then t fires again. The walk visits left(t) each time it
"bounces back" from going further left.

If the walk is: t, left(t), t (phase length 1): left(t) fires 1 time. Odd.
If: t, left(t), left(t)-1, left(t), t (length 3): left(t) fires 2 times. Even!
If: t, left(t), left(t)-1, ..., left(t), t (length >= 3): left(t) fires >= 2?

Actually: in a "bounce" pattern, the walk goes t -> left(t) -> left(t)-1 -> ... -> left(t) -> t.
Each time the walk returns to left(t), it either goes to left(t)-1 or to t.
left(t) fires each time the walk visits it (except possibly at phase boundaries).

In a short one-sided phase:
- Walk goes: t fires at step a. Step a+1: mover = left(t) or right(t).
  Say left(t). Step a+2: mover = left(t)-1 or t. If t: phase ends (length 1,
  left fires 1). If left(t)-1: continues.
  Step a+3: mover = left(t)-2 or left(t). If left(t): goes back. Then step a+4:
  mover = t or left(t)-1. If t: phase ends. Left fires 2. Even!

So the PARITY of left(t)'s fires in the phase depends on the bounce structure.

OBSERVATION: left(t) fires at the first step (walk enters from t).
             left(t) fires at the last step before the walk returns to t (walk returns to left(t) then goes to t).
So left(t) fires at both the first and last step of the phase (if the phase
has length >= 2). That's at least 2 firings. And actually, for the walk to
return to t, the step before the return must be at a neighbor of t, i.e.,
at left(t) (since the walk is on the left side). So left(t) fires at step
s-1 (just before t fires at step s).

So: left(t) fires at steps a+1 and s-1 at minimum (first and last of phase).
That's >= 2 if a+1 < s-1, i.e., phase_len >= 3.

If phase_len = 1: left(t) fires at step a+1 = s-1. Once. fc=1. BAD.
If phase_len = 2: left(t) fires at a+1 and either a+2 = s-1 (if left(t) fires
twice) or a+2 is left(t)-1 and s-1 = a+2... hmm. Let me be precise.

Phase has steps a+1, a+2, ..., s-1. Length = s - a - 1 (or with wraparound).
Step a+1: mover = left(t) (one-sided, goes left).
Step s-1: mover must be a neighbor of t = left(t) or right(t). Since one-sided
on left, step s-1 mover = left(t).

So if phase_len >= 2: left(t) fires at a+1 and s-1. If a+1 != s-1 (len >= 2):
left(t) fires at least 2 times. The question: is this count always EVEN?

left(t) fires at a+1, possibly at intermediate steps, and at s-1.
Total fires of left(t) = ?

The walk path is: left(t), X, X, ..., X, left(t) where X's are in {left(t)-1, left(t), left(t)-2, ...}.
Each visit to left(t) is a firing. The walk enters left(t) from one side
and exits to one side.

The walk enters left(t) from t (at step a+1) and exits to either t (ending phase)
or left(t)-1.
After going to left(t)-1, it bounces around and returns to left(t).
From left(t), it exits to t (ending phase) or left(t)-1 again.

So left(t)'s fire count = 1 (entry) + number of returns from left(t)-1.
Each "return" adds 1. Total = 1 + R where R = number of bounces off the left.

If R = 0: fire count = 1. Phase length = 1 (walk goes left(t) then immediately t).
If R = 1: fire count = 2. Even!
If R = 2: fire count = 3. Odd!

So the parity of left(t)'s fires = parity of 1 + R. For even: R must be odd.

Hmm, so we can't guarantee even fire count at left(t).

BUT: we need left(t) to be BINARY (m=2). For binary, fc(left(t)) must be
even (multiple of m=2). So if left(t) is binary, its TOTAL fire count is even.
In this one phase, left(t) fires some number of times. In other phases of t,
left(t) fires the remaining times. Total = even.

If left(t) fires an odd number in this phase, it fires an odd number in the
remaining phases (since total is even). But that doesn't help us.

KEY QUESTION: can we find a phase where a binary neighbor fires an EVEN
number >= 2?

Since binary's total fire count is even (= 2, 4, 6, ...), and it fires
across multiple phases of t, the sum of fires across phases is even.
If t has >= 3 phases, and binary fires in some subset...

If binary fires in exactly 1 phase: the count in that phase = fc(binary), which
is even >= 2. DONE!

If binary fires in exactly 2 phases: counts (a, b) with a+b = fc(binary) = even.
If a and b are both even: both phases work (if >= 2).
If a and b are both odd: neither phase has even count. BAD.

If binary fires in >= 3 phases: at least one has count = 0 (by pigeonhole if
binary fires in fewer phases than exist), and the rest must sum to fc(binary).

So the problematic case is when binary fires in exactly 2 phases of t,
with odd counts in each (e.g., 1+1 = 2).

CAN WE AVOID THIS? With >= 3 binary procs and >= 3 phases, can we always
find a (b,t) pair avoiding the (1,1) split?

Let me check computationally.
"""
import sys, os
from collections import Counter, defaultdict

sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', buffering=1)

def enumerate_zw_gap_words(ms, n, max_cl=None):
    if max_cl is None:
        max_cl = 3 * n + 4
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


def check_excursion_approach(word, ms, n):
    """
    For each binary b with fc(b) = 2:
    Consider the two "excursions" of b (between consecutive firings).
    Each excursion stays on one side if length < n-2.
    If an excursion is short and one-sided, both of b's fires are NOT in the same
    excursion... wait, no. The excursion is BETWEEN b's fires, not containing them.

    Let me re-think.

    b fires at s1 and s2. Between s1 and s2 (exclusive), the walk is somewhere.
    Step s1: walk at b. Step s1+1: walk at b-1 or b+1.
    Step s2-1: walk at b-1 or b+1 (to reach b at step s2).
    Step s2: walk at b.

    "Excursion 1": steps s1+1, ..., s2-1
    "Excursion 2": steps s2+1, ..., s1-1 (wrapping around)

    If excursion 1 is short (< n-2 steps), it stays on one side.
    If it goes LEFT of b: all movers in excursion 1 are in {b-1, b-2, ..., b+2}
    avoiding b+1 (the OTHER side). Actually, going left means the walk can reach
    b-1, b-2, ..., but not b+1 (which would require n-2 steps).

    Wait: "left" and "right" depend on ring labeling. Let me just say:
    The walk goes to one neighbor at step s1+1 (say A = b-1 or b+1).
    It returns to the OTHER neighbor or the SAME neighbor at step s2-1.

    Actually the walk returns to a neighbor of b at step s2-1, and then b fires at s2.
    The walk could return to the same side (A) or the other side.
    If excursion length < n-2, the walk stays on side A. So it returns on side A.

    Then: in excursion 1, only side-A neighbors of b participate.
    In excursion 2 (the rest of the cycle), the walk must account for
    all the firing of side-B neighbors.

    Now: consider t = b's neighbor on side A. In excursion 1, t fires.
    t is adjacent to b. Does t fire during excursion 2?
    Not necessarily. If ALL of t's fires are in excursion 1, then
    excursion 1 is a complete phase segment for t.

    But I'm overcomplicating this. Let me try a cleaner approach.
    """
    return None


# CLEAN APPROACH: for each binary b with fc(b) = 2, check:
# are both firings in the same phase of some adjacent proc t?
# And if so, does the other neighbor of t fire 0 in that phase?

print("=" * 70)
print("EXCURSION ANALYSIS: binary b, fc(b)=2, short excursion")
print("=" * 70)

for ms, n, max_cl in [
    ([2,2,2,3,3], 5, 20),
    ([2,2,2,3,3,3,3], 7, 24),
]:
    print(f"\nms={ms}, n={n}, n-2={n-2}")
    words = enumerate_zw_gap_words(ms, n, max_cl)
    if not words:
        continue

    binary_pos = [i for i in range(n) if ms[i] == 2]

    total = len(words)
    has_short_onesided_excursion = 0
    has_concentrated_binary = 0

    fail_words = []

    for w in words:
        fc = Counter(w)
        CL = len(w)

        found_good = False

        for b in binary_pos:
            if fc[b] != 2:
                continue
            # b fires at exactly 2 steps
            fires_b = [k for k, m in enumerate(w) if m == b]
            s1, s2 = fires_b

            # Excursion 1: (s1, s2) exclusive
            exc1_len = s2 - s1 - 1
            # Excursion 2: wraps around
            exc2_len = CL - s2 - 1 + s1

            for exc_start, exc_end, exc_len in [(s1, s2, exc1_len), (s2, s1, exc2_len)]:
                if exc_len < n - 2:
                    # This excursion is short, so one-sided
                    # The walk goes from b (at exc_start) to one neighbor, stays on that side
                    if exc_len == 0:
                        continue
                    # First step of excursion
                    first_mover = w[(exc_start + 1) % CL]
                    side_A = first_mover  # neighbor of b where walk goes
                    side_B = (b - 1) % n if side_A == (b + 1) % n else (b + 1) % n

                    # In this excursion, side_B fires 0 times (too short to reach it)
                    # Check: is side_A or side_B adjacent to some proc t with fc(t) >= 3?

                    # Now: the excursion [exc_start+1, exc_end-1] is WITHIN a phase of side_B
                    # (since side_B doesn't fire in this interval).
                    # But actually, does side_B fire in the excursion? Let me verify.
                    side_B_fires = 0
                    if exc_end > exc_start:
                        for k in range(exc_start + 1, exc_end):
                            if w[k] == side_B:
                                side_B_fires += 1
                    else:
                        for k in range(exc_start + 1, CL):
                            if w[k] == side_B:
                                side_B_fires += 1
                        for k in range(0, exc_end):
                            if w[k] == side_B:
                                side_B_fires += 1

                    # NOW: consider t = side_B. b is on one side of t... wait, b might not be
                    # adjacent to side_B. Actually b IS adjacent to both side_A and side_B
                    # (they're its neighbors). But t = side_B is adjacent to b.

                    # Hmm, we need to think about this differently.
                    # We want t adjacent to b, with a phase of t containing both b-fires.

                    # For t adjacent to b: t = side_A or t = side_B.
                    # Does side_A have a phase containing both b-fires?
                    # side_A fires in the excursion. Between two of its firings, b fires 0 times.
                    # So b's fires (at exc_start and exc_end) are OUTSIDE the excursion.
                    # Actually b fires AT exc_start and exc_end, which are the boundaries.

                    # Let me try t = side_B (the neighbor of b that doesn't participate in excursion).
                    # side_B fires 0 times in the excursion. So the excursion (including b's fires
                    # at its endpoints) is contained within a single phase of side_B.
                    # And in that phase, b fires 2 times (at exc_start and exc_end) and the
                    # OTHER neighbor of side_B is... side_B has neighbors b and some other proc.
                    # Wait: side_B is a neighbor of b. side_B's other neighbor is (side_B - 1) or (side_B + 1),
                    # whichever is NOT b.

                    if side_B_fires == 0:
                        # Great! side_B doesn't fire in the excursion.
                        # So this excursion is within a phase of side_B.
                        # b fires 2 times in this phase of side_B (at start and end of excursion).
                        # But does the OTHER neighbor of side_B fire 0 in this phase?
                        # The phase of side_B might extend BEYOND the excursion.
                        # We need to check the full phase of side_B.
                        pass

            # SIMPLER: just check if both of b's fires are in one phase of an adjacent proc,
            # with the other neighbor silent in that phase.
            for t in [(b-1)%n, (b+1)%n]:
                if fc[t] < 2:
                    continue
                firing_steps_t = [k for k, m in enumerate(w) if m == t]

                for pi in range(len(firing_steps_t)):
                    a = firing_steps_t[pi]
                    s = firing_steps_t[(pi + 1) % len(firing_steps_t)]

                    # Check: both b-fires in this phase?
                    b_fires_in = 0
                    other_nbr = (t-1)%n if (t+1)%n == b else (t+1)%n
                    other_fires = 0

                    if s > a:
                        for k in range(a+1, s):
                            if w[k] == b: b_fires_in += 1
                            if w[k] == other_nbr: other_fires += 1
                    else:
                        for k in range(a+1, CL):
                            if w[k] == b: b_fires_in += 1
                            if w[k] == other_nbr: other_fires += 1
                        for k in range(0, s):
                            if w[k] == b: b_fires_in += 1
                            if w[k] == other_nbr: other_fires += 1

                    if b_fires_in == 2 and other_fires == 0:
                        found_good = True
                        break
                if found_good:
                    break
            if found_good:
                break

        if found_good:
            has_concentrated_binary += 1
        else:
            fail_words.append(w)

    print(f"  Total: {total}, concentrated+silent: {has_concentrated_binary} ({100*has_concentrated_binary/total:.1f}%)")
    print(f"  Failures (fc(b)=2 only): {len(fail_words)}")

    # For failures, check if there's a binary with fc > 2 that works
    rescued = 0
    for w in fail_words:
        fc = Counter(w)
        CL = len(w)
        found = False
        for b in binary_pos:
            if fc[b] < 2:
                continue
            for t in [(b-1)%n, (b+1)%n]:
                if fc[t] < 2:
                    continue
                firing_steps_t = [k for k, m in enumerate(w) if m == t]
                for pi in range(len(firing_steps_t)):
                    a = firing_steps_t[pi]
                    s = firing_steps_t[(pi + 1) % len(firing_steps_t)]
                    other_nbr = (t-1)%n if (t+1)%n == b else (t+1)%n
                    b_f = 0
                    o_f = 0
                    if s > a:
                        for k in range(a+1, s):
                            if w[k] == b: b_f += 1
                            if w[k] == other_nbr: o_f += 1
                    else:
                        for k in range(a+1, CL):
                            if w[k] == b: b_f += 1
                            if w[k] == other_nbr: o_f += 1
                        for k in range(0, s):
                            if w[k] == b: b_f += 1
                            if w[k] == other_nbr: o_f += 1
                    if b_f >= 2 and b_f % 2 == 0 and o_f == 0:
                        found = True
                        break
                if found:
                    break
            if found:
                break
        if found:
            rescued += 1

    print(f"  Rescued by fc(b)>2 binary: {rescued}")
    print(f"  TRUE failures: {len(fail_words) - rescued}")

    if len(fail_words) - rescued > 0:
        print(f"  TRUE failure examples (n=5 only, n>=9 should be fine):")
        for w in fail_words[:2]:
            fc = Counter(w)
            print(f"    CL={len(w)}, fc={dict(fc)}")
