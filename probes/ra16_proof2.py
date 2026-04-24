#!/usr/bin/env python3
"""
RA16 Part 2: Structural analysis of the walk for n >= 9.

Key observation from Part 1: the theorem FAILS at n=5 for some words.
But it requires n >= 9. Let me understand WHY n >= 9 helps.

The core structural insight: in a zero-winding walk on C_n with fc >= 2
everywhere and some fc >= 3, binary procs create "reflection points" in the walk.

When the walk passes through a binary proc b, b's state flips (0↔1). Since
fc(b) is even (multiple of m_b = 2), b returns to its original state.

KEY STRUCTURAL FACT: Consider the walk between two consecutive firings of
a binary proc b. This "excursion" starts at b, goes out in one direction,
and must return to b. If the excursion goes LEFT from b, it visits procs
b-1, b-2, ... but cannot visit b+1 without passing through b (and b doesn't
fire in the interior of the excursion). WAIT: the walk moves on the ring,
and it CAN go all the way around without revisiting b... unless n is large
enough.

Hmm. Actually on a ring of size n, going from b, you can reach b+1 by going
CW (through b-1... all the way around). So "one-sided" isn't topological.

BUT: sub-threshold constraint limits cycle length! CL <= some bound.
With sub-threshold product and all fc >= 2: CL = sum fc(p) >= 2n.
The sub-threshold product is < 4*3^(n-2).

Actually let me think differently. Let me look at what happens between
consecutive firings of a proc t with fc >= 3. A "phase" of t is the gap
between two consecutive firings. If fc(t) >= 3, there are >= 3 phases.

In each phase, the walk starts at t, moves to a neighbor of t, visits some
procs, and returns to t (where it fires again).

For the walk to visit BOTH neighbors of t in a single phase, it must
start at t, go to one neighbor, traverse some procs, eventually reach
the other neighbor of t, and come back to t. This requires crossing t
itself... but t doesn't fire in its own phase! So how can the walk
cross t?

WAIT: the walk doesn't "cross" t. The walk is a sequence of ring-adjacent
movers. If the walk is at proc t-1, the next mover is either t-2 or t.
If the next mover is t, then t fires (the phase ends). So within a phase
of t, the walk stays on ONE SIDE of t!

This is the key insight. Within a phase of proc t:
- The walk enters t's left or right neighbor (the first step after t fires)
- It cannot reach the other neighbor without t firing (the walk can't "jump over" t)
- It stays on one side of the ring relative to t
- So one neighbor fires 0 times in the phase (the one NOT on the walk's side)

IS THIS TRUE? On a ring, from position t-1, the walk goes to t-2 or t.
If it goes to t, that ends the phase. Otherwise it goes to t-2, then t-3 or t-1.
From t-1, it could go back to t... which ends the phase. So the walk bounces
between t-1, t-2, ... potentially going far, but to reach t+1 it would need
to go all the way around the ring, passing through t+2, t+3, ..., t-1, t...
NO. The ring is a cycle. From position t-2, the walk goes to t-1 or t-3.
To reach t+1, it needs to go t-3, t-4, ..., t+2, t+1.

CAN IT? On C_n, going from t-1 (which is the first step in the phase),
to reach t+1 the walk needs to traverse n-2 procs (going the long way
around, not through t). This requires n-2 steps minimum. But the total
CL might be small enough that this can't happen in a single phase.

Actually WAIT. More carefully: the walk doesn't have to traverse all n-2
procs. It just needs to get to t+1. From t-1, to reach t+1 without going
through t, it must go: t-1 → t-2 → ... → t+2 → t+1. That's n-2 steps.

But the walk can revisit procs! So it could bounce around on the left side
for a while, then decide to go all the way around. But the MINIMUM number
of steps to get from t-1 to t+1 without passing through t is n-2 steps.

In a phase of length L (between two consecutive firings of t), if L < n-2,
then the walk CANNOT reach both neighbors. But if L >= n-2, it could.

For fc(t) >= 3 and CL = sum(fc), we have CL >= 2n (since all fc >= 2).
The average phase length is CL/fc(t) - 1 (excluding the firing step).
Wait: there are fc(t) phases, and the total steps NOT at t is CL - fc(t).
So average phase length is (CL - fc(t)) / fc(t).

If fc(t) = 3: avg phase length = (CL - 3) / 3. For CL = 2n: (2n-3)/3.
For n >= 9: (2*9-3)/3 = 5. But n-2 = 7 for n=9. So avg = 5 < 7.
By pigeonhole, at least one phase has length <= 5 < 7. So that phase
cannot visit both neighbors of t!

Let me verify this computationally.
"""
import sys, os
from collections import Counter, defaultdict

sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', buffering=1)

# Verification: in all zero-winding gap words, does every phase of every
# fc >= 3 proc have the walk on one side?

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


def analyze_phases(word, ms, n):
    """For each proc with fc >= 3, analyze whether each phase is one-sided."""
    fc = Counter(word)
    CL = len(word)
    binary_pos = set(i for i in range(n) if ms[i] == 2)

    firing_steps = defaultdict(list)
    for k, mover in enumerate(word):
        firing_steps[mover].append(k)

    results = []

    for t in range(n):
        if fc[t] < 2:
            continue
        steps_t = firing_steps[t]
        left_t = (t - 1) % n
        right_t = (t + 1) % n

        for phase_idx in range(len(steps_t)):
            a = steps_t[phase_idx]
            s = steps_t[(phase_idx + 1) % len(steps_t)]

            if s > a:
                phase_movers = [word[k] for k in range(a + 1, s)]
            else:
                phase_movers = [word[k] for k in range(a + 1, CL)] + [word[k] for k in range(0, s)]

            left_fires = phase_movers.count(left_t)
            right_fires = phase_movers.count(right_t)
            phase_len = len(phase_movers)

            one_sided = (left_fires == 0) or (right_fires == 0)
            results.append({
                't': t, 'fc_t': fc[t], 'phase': phase_idx,
                'left_fires': left_fires, 'right_fires': right_fires,
                'one_sided': one_sided, 'phase_len': phase_len,
                'left_is_bin': left_t in binary_pos,
                'right_is_bin': right_t in binary_pos,
            })

    return results


# Quick test: at n=5, what fraction of phases are one-sided?
print("=" * 70)
print("PHASE ONE-SIDEDNESS ANALYSIS")
print("=" * 70)

for ms, n, max_cl in [
    ([2,2,2,3,3], 5, 20),
    ([2,2,2,3,3,3,3], 7, 24),
]:
    print(f"\nms={ms}, n={n}")
    words = enumerate_zw_gap_words(ms, n, max_cl)
    if not words:
        print(f"  No words found")
        continue

    total_phases = 0
    one_sided_phases = 0
    two_sided_phases = 0
    # For each word: is there at least one phase that is one-sided with binary active?
    words_with_good_phase = 0
    words_without = 0

    two_sided_details = []

    for w in words:
        phases = analyze_phases(w, ms, n)
        fc = Counter(w)
        binary_pos = set(i for i in range(n) if ms[i] == 2)

        has_good = False
        for ph in phases:
            total_phases += 1
            if ph['one_sided']:
                one_sided_phases += 1
                # Check if the active side is binary with even >= 2
                if ph['left_fires'] == 0:
                    # right is active
                    if ph['right_is_bin'] and ph['right_fires'] >= 2 and ph['right_fires'] % 2 == 0:
                        has_good = True
                elif ph['right_fires'] == 0:
                    # left is active
                    if ph['left_is_bin'] and ph['left_fires'] >= 2 and ph['left_fires'] % 2 == 0:
                        has_good = True
            else:
                two_sided_phases += 1
                if ph['fc_t'] >= 3 and len(two_sided_details) < 5:
                    two_sided_details.append((w, ph))

        if has_good:
            words_with_good_phase += 1
        else:
            words_without += 1

    print(f"  Words: {len(words)}")
    print(f"  Total phases: {total_phases}, one-sided: {one_sided_phases} ({100*one_sided_phases/total_phases:.1f}%), two-sided: {two_sided_phases} ({100*two_sided_phases/total_phases:.1f}%)")
    print(f"  Words with good phase: {words_with_good_phase}/{len(words)} ({100*words_with_good_phase/len(words):.1f}%)")
    print(f"  Words without: {words_without}")

    if two_sided_details:
        print(f"\n  Sample two-sided phases (fc_t >= 3):")
        for w, ph in two_sided_details[:3]:
            print(f"    t={ph['t']}, fc_t={ph['fc_t']}, phase_len={ph['phase_len']}, left_fires={ph['left_fires']}, right_fires={ph['right_fires']}")
            print(f"    n-2 = {n-2}, phase_len >= n-2: {ph['phase_len'] >= n-2}")


# KEY THEOREM INSIGHT:
# In a phase of length < n-2, the walk CANNOT visit both neighbors.
# Proof: the walk starts at one neighbor of t. To reach the other,
# it must go n-2 steps around the ring (the long way, avoiding t).
# So if phase_len < n-2, the phase is one-sided.
#
# Pigeonhole: with fc(t) >= 3, there are >= 3 phases.
# At least one phase has length <= (CL - fc(t)) / fc(t).
# At CL = 2n, fc(t) = 3: length <= (2n - 3)/3.
# For n >= 9: (2*9-3)/3 = 5 < 7 = n-2. WORKS!
#
# But we also need the active side to be binary with even fires >= 2.
# The short phase might have the binary neighbor firing only 0 or 1 times.
# We need ANOTHER phase where binary fires >= 2.

print("\n\n" + "=" * 70)
print("PHASE LENGTH DISTRIBUTION FOR fc >= 3 PROCS")
print("=" * 70)

for ms, n, max_cl in [
    ([2,2,2,3,3], 5, 20),
    ([2,2,2,3,3,3,3], 7, 24),
]:
    print(f"\nms={ms}, n={n}, n-2={n-2}")
    words = enumerate_zw_gap_words(ms, n, max_cl)
    if not words:
        continue

    short_phase_count = 0
    total_fc3_phases = 0

    for w in words:
        phases = analyze_phases(w, ms, n)
        for ph in phases:
            if ph['fc_t'] >= 3:
                total_fc3_phases += 1
                if ph['phase_len'] < n - 2:
                    short_phase_count += 1

    print(f"  fc>=3 phases with length < n-2: {short_phase_count}/{total_fc3_phases} ({100*short_phase_count/total_fc3_phases:.1f}%)")


# Now the REAL QUESTION: does there always exist a BINARY proc whose
# ALL firings are in one phase of its neighbor?
print("\n\n" + "=" * 70)
print("BINARY PROC ALL-IN-ONE-PHASE CHECK")
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
    success = 0
    fail = 0

    for w in words:
        fc = Counter(w)
        firing_steps = defaultdict(list)
        for k, mover in enumerate(w):
            firing_steps[mover].append(k)
        CL = len(w)

        found = False
        for b in binary_pos:
            # Check each neighbor t of b
            for t in [(b-1)%n, (b+1)%n]:
                if fc[t] < 2:
                    continue
                steps_t = firing_steps[t]
                # For each phase of t, count how many times b fires
                for phase_idx in range(len(steps_t)):
                    a = steps_t[phase_idx]
                    s = steps_t[(phase_idx + 1) % len(steps_t)]

                    if s > a:
                        b_fires_in_phase = sum(1 for k in range(a+1, s) if w[k] == b)
                    else:
                        b_fires_in_phase = sum(1 for k in range(a+1, CL) if w[k] == b) + \
                                           sum(1 for k in range(0, s) if w[k] == b)

                    # Does this phase contain ALL of b's fires?
                    if b_fires_in_phase == fc[b]:
                        # Check: the OTHER neighbor of t fires 0 in this phase
                        other = (t - 1) % n if (t + 1) % n == b else (t + 1) % n
                        if s > a:
                            other_fires = sum(1 for k in range(a+1, s) if w[k] == other)
                        else:
                            other_fires = sum(1 for k in range(a+1, CL) if w[k] == other) + \
                                          sum(1 for k in range(0, s) if w[k] == other)

                        if other_fires == 0 and b_fires_in_phase >= 2 and b_fires_in_phase % 2 == 0:
                            found = True
                            break
                if found:
                    break
            if found:
                break

        if found:
            success += 1
        else:
            fail += 1

    print(f"  All-in-one-phase with silent other: {success}/{len(words)} ({100*success/len(words):.1f}%)")
    print(f"  Failures: {fail}")
