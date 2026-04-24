#!/usr/bin/env python3
"""
RA16 Part 3: The proof argument.

PROOF STRATEGY:
==============

Claim: In a zero-winding cycle on C_n (n >= 9) with >= 3 binary procs,
all fc >= 2, some fc >= 3, cwStepCount > 0, no safe proc, sub-threshold:
there exists t and a phase of t where one neighbor is binary+active (even >= 2),
other neighbor is silent (fires 0).

Key Lemma (Phase One-Sidedness):
  If phase length < n-2, the phase is one-sided (one neighbor fires 0).

  Proof: In a phase of t, the walk starts at t and ends at t. The first
  step goes to one neighbor (say left). To reach the right neighbor,
  the walk must go all the way around: left(t), left(left(t)), ..., right(t).
  That's n-2 steps minimum (and the walk must also return to the neighborhood
  of t). If phase length < n-2, the walk cannot reach the other neighbor.

  Wait, more precisely: phase_len is the number of firing steps between
  consecutive firings of t. The walk is at t at step a, fires t. Next step
  (a+1) fires some neighbor of t. Steps a+1 through s-1 are the phase
  interior (s is the next firing of t). At step s, the walk fires t again.
  So step s-1 fires a neighbor of t (the walk returns to t at step s).

  If the walk goes to left(t) at step a+1, and reaches right(t) at some
  step, it must traverse n-2 intermediate procs. This requires >= n-2 steps.
  So if the phase has < n-2 steps, it stays on the left side.

Pigeonhole for short phases:
  With fc(t) = F >= 3, there are F phases. Total phase steps = CL - F.
  Some phase has length <= (CL - F) / F.

  For this to be < n-2, we need (CL - F) / F < n-2, i.e., CL < F(n-1).
  With F = 3: CL < 3(n-1) = 3n-3.

  CL = sum fc(p). Since fc(p) >= m_p for all p, CL >= sum(m_p).
  With >= 3 binary (m=2) and rest ternary (m=3): CL >= 2*3 + 3*(n-3) = 3n-3.
  So CL >= 3n-3. And we need CL < 3n-3. CONTRADICTION if CL = 3n-3.

  Hmm. If CL = 3n-3 exactly and fc(t) = 3, then avg phase = (3n-6)/3 = n-2.
  Not strictly less than n-2. Need to be more careful.

  If CL = 3n-3 and fc(t) = 3: phases have lengths summing to 3n-6.
  Average = n-2. Pigeonhole: SOME phase has length <= n-2 (not strictly <).

  If phase length = n-2 exactly, can the walk visit both neighbors?
  It needs n-2 steps to go from left(t) all the way to right(t). But it
  also needs to be at a neighbor of t at the LAST step of the phase.
  So it needs to START at left(t), go n-2 steps to right(t), and the
  phase ends with t firing after right(t) fires. That's exactly n-2 steps
  and the walk goes monotonically around the ring. NO BACKTRACKING.

  In n-2 steps from left(t): left(t), left(left(t)), ..., right(t).
  That visits every proc except t exactly once. It's a one-directional sweep.

  Can this happen in a zero-winding cycle with fc >= 2 everywhere?
  Yes potentially, but this is a very specific structure.

  Actually wait: even in this case, the OTHER neighbor (right(t)) fires
  exactly 1 time (at the end). And the LEFT neighbor fires 1 time (at the start).
  Neither is 0 fires. So this phase is NOT one-sided!

  But is this achievable? Let's check: the phase goes t -> left -> left-1 -> ... -> right.
  That's n-2 intermediate steps, each going CW. The movers in the phase are:
  left(t), left(t)-1, ..., right(t)+1, right(t). That's n-2 movers.
  Left fires 1 time. Right fires 1 time. Everyone in between fires 1 time.

  So a phase of length exactly n-2 CAN visit both neighbors, but each fires only 1 time.

  REFINEMENT: we need phase length <= n-3 to guarantee one-sidedness.

  Pigeonhole: some phase has length <= floor((CL-F)/F).
  For CL = 3n-3, F = 3: floor((3n-6)/3) = n-2.
  For CL = 3n-2, F = 3: floor((3n-5)/3) = floor(n - 5/3) = n-2.
  For CL = 3n-1, F = 3: floor((3n-4)/3) = floor(n - 4/3) = n-2 for n >= 3.

  Hmm, hard to get below n-2 with F=3.

  What if F >= 4? Then for CL = 3n-3:
  floor((3n-7)/4). For n=9: floor(20/4) = 5. n-3 = 6. 5 < 6. WORKS!

  But we need fc(t) >= 4 at some proc t for this. We only know fc >= 3 at some proc.

  Wait... fc(t) >= 3 means exactly fc(t) = 3, 4, 5, or 6.
  If fc(t) = 3 and CL = 3n-3: phases average n-2, might all be exactly n-2.

  Let me check: with 3 phases each of length n-2, they account for 3(n-2) = 3n-6 steps.
  Plus 3 firings of t: total CL = 3n-3. Consistent.

  In each phase, the walk does a monotone sweep of length n-2 visiting ALL other procs.
  But zero-winding requires these sweeps to cancel out. If each sweep goes the same
  direction, total winding = 3 * direction * (n-2)/(n) ... hmm actually winding is
  based on net displacement. Each sweep from t goes around once? No.

  Actually: each phase starts at t and ends at t. The walk displacement within
  each phase is 0 (starts and ends at t). So each phase contributes 0 net winding.
  The zero-winding constraint is satisfied trivially for each phase.

  Wait, the WINDING is defined differently. Let me reconsider.

  The winding number counts how many times the walk goes around the ring.
  Each CW step contributes +1, each CCW step contributes -1. Zero winding
  means the sum is 0.

  In a phase that goes: t fires, walk goes CW to left(t), CW to left(t)-1,
  ... all the way to right(t), then t fires. That's n-1 CW steps (including
  t firing at start → left is step a+1, which is CW). No wait, this is wrong.

  Let me reconsider. At step a, mover is t. At step a+1, mover could be
  (t-1) or (t+1). Let's say it's (t-1) [go CCW]. Then the walk goes
  CCW: t-1, t-2, ..., eventually reaches t+1 after n-2 steps. That's
  n-2 CCW steps. Then at step s, mover is t again (t+1 → t is CCW).
  So the phase has n-2 CCW steps + the t→t-1 step and the t+1→t step.

  Actually wait. The mover sequence is: ..., t, t-1, t-2, ..., t+1, t, ...
  Steps: a=t fires, a+1=t-1 fires, a+2=t-2 fires, ..., a+(n-2)=t+1 fires, a+(n-1)=t fires.
  From mover t to mover t-1: that's going CCW (direction = (t-1) - t = -1 mod n).
  From t-1 to t-2: CCW.
  ...
  From t+2 to t+1: CCW.
  From t+1 to t: CCW.

  So all n-1 transitions in this segment are CCW. Winding contribution = -(n-1).
  For 3 such phases all going CCW: total winding = -3(n-1). NOT zero.

  For zero winding, the 3 phases must alternate directions or have some other pattern.
  If 2 phases go CCW and 1 goes CW: winding = -2(n-1) + (n-1) = -(n-1) ≠ 0.
  This doesn't easily cancel.

  So a cycle with 3 phases of length exactly n-2 is very constrained.

  KEY INSIGHT: For the length n-2 case (where both neighbors fire exactly once),
  the walk is a monotone sweep. But zero-winding requires cancellation. The
  cancellation means that across all phases, the net winding is zero. This
  creates strong constraints.

  But actually: we don't need ALL phases to be one-sided. We just need ONE
  phase where a BINARY neighbor provides even >= 2 fires and the other side
  is silent.

  Alternative approach: use the >= 3 binary procs directly.

ALTERNATIVE ARGUMENT:
====================

Consider all binary procs. There are B >= 3 of them. Each fires fc(b) times
(even, >= 2). Total binary fires = sum of fc(b) >= 2B >= 6.

Now consider any proc t adjacent to a binary proc b. If fc(t) >= 3,
t has >= 3 phases. b fires fc(b) times across these phases.

By pigeonhole: some phase of t has b firing <= floor(fc(b) / fc(t)) times.
If fc(b) < fc(t), some phase has b firing 0 times.

But we want the OPPOSITE: some phase where b fires >= 2 and the other
neighbor fires 0. We need b's fires to CONCENTRATE in one phase.

Since fc(b) >= 2 and fc(t) >= 3, by pigeonhole some phase has b firing 0,
and since total fc(b) >= 2, the remaining phases have b firing >= 2 total.
But we need some SINGLE phase to have b firing >= 2. If b fires once in
each of two phases, that's 1 per phase (not >= 2).

Hmm. Let me reconsider.

If fc(b) = 2 and fc(t) = 3: b fires 2 times across 3 phases.
By pigeonhole, at least one phase has b firing 0.
The other 2 phases have b firing a total of 2. Either (2,0) or (1,1).
If (2,0): some phase has b firing 2 (good, even >= 2) and another has 0.
If (1,1): no phase has b firing >= 2. BAD.

So pigeonhole alone doesn't guarantee b fires >= 2 in one phase.
We need to use walk structure.

CRITICAL WALK CONSTRAINT:
When b fires, the walk is at b. Before and after b fires, the walk is at
a neighbor of b. Since t is adjacent to b (say t = b+1), and b's other
neighbor is b-1:

b's first firing: walk comes from t or b-1, fires b, then goes to t or b-1.
b's second firing: same.

If b fires in two DIFFERENT phases of t:
- Phase i: walk is at b (fires b). Before: walk was at neighbor of b.
  After: walk goes to neighbor of b. Phase i includes b firing.
  Wait, a phase of t is between two consecutive firings of t.
  b fires WITHIN the phase (not at the boundary).

  If b fires in phase i and phase j (different phases), then:
  In phase i, the walk at some point is at b (fires it), then moves to
  a neighbor of b. Before reaching b, the walk was at a neighbor of b.

  Since t is a neighbor of b, in each phase, the walk either:
  (a) comes from the t-side to b, fires b, goes to b-1 side. Or
  (b) comes from the b-1 side to b, fires b, goes to t side. Or
  (c) comes from t, fires b, goes back to t. Or
  (d) comes from b-1, fires b, goes back to b-1.

Now: within a ONE-SIDED phase of t (short phase), the walk stays on one
side of t. If the walk is on the b-side, it can reach b and fire it.
If the walk is on the other side, it cannot reach b (since t is between
them and t doesn't fire in its own phase).

So within a one-sided phase of t where the walk goes to the b-side,
b can fire. In a one-sided phase going to the other side, b fires 0.

Now the KEY: for b's two firings to be in TWO different phases of t,
TWO phases must go to the b-side. But the walk direction determines
which side. If two phases go to the b-side, the zero-winding constraint
says we need "return" phases going the other way. With fc(t) = 3:
three phases. If 2 go to b-side and 1 goes to other side: b fires
at most once per b-side phase (but could fire twice total), and
the other-side phase has b firing 0. But we need the one-sided phase
on the OTHER side to have b's fires on it... no, the other-side phase
is where the walk goes AWAY from b, so b fires 0 there.

Hmm, this is getting complicated. Let me just verify computationally whether
the (1,1) distribution actually occurs at n >= 7.
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


print("=" * 70)
print("BINARY FIRE DISTRIBUTION ACROSS PHASES OF ADJACENT fc>=3 PROC")
print("=" * 70)

for ms, n, max_cl in [
    ([2,2,2,3,3], 5, 20),
    ([2,2,2,3,3,3,3], 7, 24),
]:
    print(f"\nms={ms}, n={n}")
    words = enumerate_zw_gap_words(ms, n, max_cl)
    if not words:
        continue

    binary_pos = set(i for i in range(n) if ms[i] == 2)

    # For each (b, t) pair where b is binary and t is adjacent to b with fc(t)>=3,
    # find how b's fires distribute across t's phases.
    dist_counter = Counter()  # distribution pattern -> count
    bad_dist_words = []  # words where ALL binary-adjacent-fc3 pairs have (1,1,...) distribution

    for w in words:
        fc = Counter(w)
        CL = len(w)
        firing_steps = defaultdict(list)
        for k, mover in enumerate(w):
            firing_steps[mover].append(k)

        any_good = False  # Is there any (b,t) pair giving a phase with b>=2 and other=0?

        for b in binary_pos:
            for t in [(b-1)%n, (b+1)%n]:
                if fc[t] < 3:
                    continue
                steps_t = firing_steps[t]

                # Count b fires in each phase of t
                b_fires_per_phase = []
                other_nbr = (t-1)%n if (t+1)%n == b else (t+1)%n
                other_fires_per_phase = []

                for phase_idx in range(len(steps_t)):
                    a = steps_t[phase_idx]
                    s = steps_t[(phase_idx + 1) % len(steps_t)]

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

                    b_fires_per_phase.append(b_f)
                    other_fires_per_phase.append(o_f)

                pattern = tuple(sorted(b_fires_per_phase, reverse=True))
                dist_counter[pattern] += 1

                # Check if any phase has b >= 2 AND other = 0
                for i in range(len(b_fires_per_phase)):
                    if b_fires_per_phase[i] >= 2 and b_fires_per_phase[i] % 2 == 0 and other_fires_per_phase[i] == 0:
                        any_good = True
                        break
                if any_good:
                    break
            if any_good:
                break

        if not any_good:
            bad_dist_words.append(w)

    print(f"  Total words: {len(words)}")
    print(f"  Words without good phase (any binary-adj-fc3 pair): {len(bad_dist_words)}")
    print(f"\n  Binary fire distribution patterns (sorted desc):")
    for pattern, cnt in sorted(dist_counter.items(), key=lambda x: -x[1])[:15]:
        print(f"    {pattern}: {cnt}")

    if bad_dist_words:
        print(f"\n  Sample bad words:")
        for w in bad_dist_words[:3]:
            fc = Counter(w)
            print(f"    CL={len(w)}, fc={dict(fc)}, word={w}")
            # Show details
            for b in binary_pos:
                for t in [(b-1)%n, (b+1)%n]:
                    if fc[t] < 3:
                        continue
                    steps_t = firing_steps_fn = [k for k, m in enumerate(w) if m == t]
                    other_nbr = (t-1)%n if (t+1)%n == b else (t+1)%n
                    for pi in range(len(steps_t)):
                        a = steps_t[pi]
                        s = steps_t[(pi+1) % len(steps_t)]
                        if s > a:
                            bfires = sum(1 for k in range(a+1,s) if w[k]==b)
                            ofires = sum(1 for k in range(a+1,s) if w[k]==other_nbr)
                        else:
                            bfires = sum(1 for k in range(a+1,len(w)) if w[k]==b) + sum(1 for k in range(0,s) if w[k]==b)
                            ofires = sum(1 for k in range(a+1,len(w)) if w[k]==other_nbr) + sum(1 for k in range(0,s) if w[k]==other_nbr)
                        print(f"      b={b},t={t}: phase {pi} [{a}..{s}): b fires {bfires}, other({other_nbr}) fires {ofires}")
