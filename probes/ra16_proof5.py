#!/usr/bin/env python3
"""
RA16 Part 5: Verify the core structural lemmas for the proof.

PROOF OUTLINE:
=============

Let n >= 9, >=3 binary procs, all fc >= 2, some fc >= 3, zero winding, cw > 0.

Step 1: Find a binary proc b with fc(b) = 2.
  Claim: at least one binary proc has fc = 2.
  Proof: If ALL binary procs have fc >= 4, then CL >= 4 * B + 3 * (n - B)
  = 3n + B >= 3n + 3. But we also need CL to be achievable. Actually we
  can't just claim fc(b) = 2. Binary procs have fc = even multiple of 2,
  so fc(b) in {2, 4, 6, ...}. Some might have fc = 4.

  BETTER: Count total fires. CL = sum fc(p). With sub-threshold product,
  the multiset has >= 3 binary with product < 4 * 3^(n-2).
  Hmm, CL isn't directly bounded by product. CL depends on the walk.

  Actually: from the Lean code, the theorem doesn't assume fc(b) = 2.
  It says fc(q) >= 3 for some q, and finds a phase where a binary neighbor
  fires even >= 2.

  Let me check: at n=7, do ALL successful cases have a binary with fc=2?

Step 2: Find a short one-sided excursion of b.
  b fires fc(b) times. Between consecutive firings are excursions.
  fc(b) excursions, total length CL - fc(b).
  Shortest excursion: length <= floor((CL - fc(b)) / fc(b)).

  For fc(b) = 2: shortest <= floor((CL - 2) / 2) = floor(CL/2) - 1.
  Need this < n - 2, i.e., floor(CL/2) - 1 < n - 2, i.e., CL < 2n - 1.
  But CL >= 2n (all fc >= 2). So CL >= 2n and we need CL < 2n-1. CONTRADICTION.

  So for fc(b) = 2, the shortest excursion has length >= n - 1.
  That's NOT short enough to guarantee one-sidedness (need < n-2).

  Hmm! So the short excursion argument FAILS for fc(b) = 2.

  Wait: CL = 2n requires fc(p) = m_p for all p (the minimum). But we
  have some fc >= 3, so CL >= 2B + 3*(n-B) + 1 = 3n - B + 1 (at least
  one ternary fires 3 + something extra... actually no, the excess fires
  come from somewhere).

  Let me reconsider. With all fc >= 2 and some fc >= 3:
  CL = sum fc(p) >= sum m_p + (extra fires).
  sum m_p = 2B + 3(n-B) = 3n - B.
  The "extra fires" come from procs where fc > m_p.
  Since some fc >= 3, and for binary procs fc >= 2 = m, and for ternary fc >= 3 = m.
  So the extra fires = sum(fc(p) - m_p) >= 0. But we have some fc >= 3.
  If the fc >= 3 proc is binary: fc >= 4 (next even), so extra >= 2.
  If the fc >= 3 proc is ternary: fc >= 3, which is m_p. So extra could be 0!

  Wait: fc >= 3 at some proc q. If q is ternary, fc(q) >= 3 = m_q, so no extra.
  But fc(q) >= 3 and m_q = 3 means fc(q) >= 3, so fc(q) could be exactly 3.
  Then CL = 3n - B (minimum possible).

  For B = 3: CL = 3n - 3. For n = 9: CL = 24.
  fc(b) = 2 for binary b: excursions have total length CL - 2 = 3n - 5.
  Two excursions, shortest <= floor((3n-5)/2). For n=9: floor(22/2) = 11.
  n - 2 = 7. 11 > 7. NOT short.

  For fc(b) = 4: 4 excursions, total CL - 4 = 3n - 7.
  Shortest <= floor((3n-7)/4). For n=9: floor(20/4) = 5. n-2 = 7. 5 < 7. SHORT!

  But we don't know any binary has fc = 4.

Let me re-examine what happens. Maybe the right approach is to look at it
from the PHASE side (phases of the fc >= 3 proc), not the excursion side.

Step 1': Find proc t with fc(t) >= 3. Guaranteed by assumption.

Step 2': t has fc(t) >= 3 phases. By pigeonhole, at least one phase has
  length <= floor((CL - fc(t)) / fc(t)).

  For fc(t) = 3, CL = 3n - 3: floor((3n-6)/3) = n - 2.
  So shortest phase has length <= n - 2.

  If length <= n - 3: walk cannot visit both neighbors. ONE-SIDED. But we
  showed phase length can be exactly n - 2.

  If length = n - 2: walk CAN visit both neighbors (monotone sweep).

  KEY QUESTION: at n = 9, in CL = 24 cycles with fc(t) = 3, can ALL 3 phases
  have length exactly 8 = n - 2?

  3 phases of length 8 = 24 steps + 3 fires of t = 27. But CL = 24.
  Wait: CL = 24 includes t's fires. Phase lengths sum = CL - fc(t) = 24 - 3 = 21.
  Three phases: 21/3 = 7. So avg length = 7 = n - 2.

  By pigeonhole: at least one phase has length <= 7.
  If all are exactly 7: each can potentially visit both neighbors.
  But 7 = n - 2 = 7 (n=9). A phase of length 7 on a ring of 9 can visit both
  neighbors only if the walk goes monotonically from one neighbor all the way
  to the other (7 steps, visiting 7 procs in between including both neighbors).

  Actually from t, going to left(t), then 7 steps to reach right(t): that's
  visiting left(t), left(t)-1, ..., right(t)+1, right(t). That's 8 procs in 7 steps.
  Wait: 7 steps means 7 movers. Starting from left(t), going CCW for 7 steps:
  left(t), left(t)-1, ..., left(t)-6. left(t)-6 = t-7 = (t-7) mod 9 = t+2.
  Is t+2 = right(t)? right(t) = t+1. No, t+2 ≠ t+1.

  Hmm. To go from left(t) = t-1 to right(t) = t+1 WITHOUT passing through t:
  need to go t-1, t-2, ..., t+2, t+1. That's n-2 = 7 procs visited, taking
  7 steps (each step moves one position). So in 7 steps, the walk reaches right(t).
  The 7 movers are: t-1, t-2, t-3, t-4, t-5, t-6, t-7 = t+2. Wait, that's
  only 7 movers but t-7 = t+2 (mod 9), not t+1.

  t-1 → t-2 → ... → t-7 = t+2 → t-8 = t+1 = right(t). That's 8 steps.

  OH. From left(t) to right(t) avoiding t: the distance is n-2 edges.
  t-1 to t-2: 1 edge. t-2 to t-3: 2 edges from t-1. ... t+1: n-2 edges from t-1.
  So it takes n-2 steps to reach right(t) from left(t).

  Phase length n-2 = 7 (n=9): the walk starts at left(t) and needs 7 steps
  to reach right(t). The walk HAS exactly 7 steps. So in the best case,
  it goes monotonically and reaches right(t) at the LAST step. Then
  right(t) fires once (at the last step) and left(t) fires once (at the first step).

  So in a phase of length exactly n-2, BOTH neighbors fire exactly 1 time.

  This is the pathological case: if EVERY binary neighbor of t fires exactly
  1 time in every phase, we get the (1,1,1) distribution and no phase has
  the binary firing >= 2.

  BUT: can this actually happen? If the walk does a full sweep in each phase,
  alternating direction... the zero-winding constraint limits this.

  Let me check: at n=9, do these "all sweep" cycles exist?
"""
import sys, os
from collections import Counter, defaultdict

sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', buffering=1)

# Check at n=7 and n=9: do cycles exist where some binary b adjacent to
# fc>=3 proc t has fire distribution (1,1,1,...) across all phases of t?

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


# At n=7, check if the (1,1,...) distribution for binary procs happens
print("=" * 70)
print("CHECKING: (1,1,...) distribution at binary-adjacent-fc3 pairs")
print("=" * 70)

for ms, n, max_cl in [
    ([2,2,2,3,3,3,3], 7, 24),
]:
    print(f"\nms={ms}, n={n}")
    words = enumerate_zw_gap_words(ms, n, max_cl)
    if not words:
        print("  No words")
        continue

    binary_pos = set(i for i in range(n) if ms[i] == 2)
    all_even_count = 0
    has_11_pair = 0

    for w in words:
        fc = Counter(w)
        CL = len(w)
        firing_steps = defaultdict(list)
        for k, m in enumerate(w):
            firing_steps[m].append(k)

        any_11 = False
        for b in binary_pos:
            for t in [(b-1)%n, (b+1)%n]:
                if fc[t] < 3:
                    continue
                steps_t = firing_steps[t]
                other_nbr = (t-1)%n if (t+1)%n == b else (t+1)%n

                b_fires_per_phase = []
                for pi in range(len(steps_t)):
                    a = steps_t[pi]
                    s = steps_t[(pi+1) % len(steps_t)]
                    bf = 0
                    if s > a:
                        for k in range(a+1, s):
                            if w[k] == b: bf += 1
                    else:
                        for k in range(a+1, CL):
                            if w[k] == b: bf += 1
                        for k in range(0, s):
                            if w[k] == b: bf += 1
                    b_fires_per_phase.append(bf)

                # Check: is there any phase with b fires >= 2?
                if max(b_fires_per_phase) < 2:
                    # All phases have b fires <= 1. This is the "spread out" case.
                    any_11 = True

        if any_11:
            has_11_pair += 1

    print(f"  Words with (b,t) pair where b fires <= 1 in EVERY phase of t: {has_11_pair}/{len(words)}")

# KEY CHECK: for each word that succeeds at n=7, WHICH (b,t) pair provides the good phase?
# Is it always b with fc(b)=2? Or sometimes fc(b)=4?
print("\n" + "=" * 70)
print("WHICH BINARY PROVIDES THE GOOD PHASE?")
print("=" * 70)

for ms, n, max_cl in [
    ([2,2,2,3,3,3,3], 7, 24),
]:
    print(f"\nms={ms}, n={n}")
    words = enumerate_zw_gap_words(ms, n, max_cl)

    binary_pos = set(i for i in range(n) if ms[i] == 2)
    provider_fc_dist = Counter()  # fc(b) for the provider binary
    provider_t_fc_dist = Counter()  # fc(t) for the provider's adjacent proc

    for w in words:
        fc = Counter(w)
        CL = len(w)
        firing_steps = defaultdict(list)
        for k, m in enumerate(w):
            firing_steps[m].append(k)

        found = False
        for b in sorted(binary_pos, key=lambda x: fc[x]):  # try smallest fc first
            for t in [(b-1)%n, (b+1)%n]:
                if fc[t] < 2:
                    continue
                steps_t = firing_steps[t]
                other_nbr = (t-1)%n if (t+1)%n == b else (t+1)%n
                for pi in range(len(steps_t)):
                    a = steps_t[pi]
                    s = steps_t[(pi+1) % len(steps_t)]
                    bf = 0
                    of = 0
                    if s > a:
                        for k in range(a+1, s):
                            if w[k] == b: bf += 1
                            if w[k] == other_nbr: of += 1
                    else:
                        for k in range(a+1, CL):
                            if w[k] == b: bf += 1
                            if w[k] == other_nbr: of += 1
                        for k in range(0, s):
                            if w[k] == b: bf += 1
                            if w[k] == other_nbr: of += 1
                    if bf >= 2 and bf % 2 == 0 and of == 0:
                        provider_fc_dist[fc[b]] += 1
                        provider_t_fc_dist[fc[t]] += 1
                        found = True
                        break
                if found:
                    break
            if found:
                break

    print(f"  Provider binary fc distribution:")
    for fcval, cnt in sorted(provider_fc_dist.items()):
        print(f"    fc(b) = {fcval}: {cnt}")
    print(f"  Provider t fc distribution:")
    for fcval, cnt in sorted(provider_t_fc_dist.items()):
        print(f"    fc(t) = {fcval}: {cnt}")


# NOW: the critical structural check. In a one-sided phase of t,
# does the binary neighbor ALWAYS fire an even number of times?
# This should follow from walk parity: the walk enters through
# the binary, bounces, and exits through the binary.
print("\n" + "=" * 70)
print("PARITY OF BINARY FIRES IN ONE-SIDED PHASES")
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
    even_count = 0
    odd_count = 0

    for w in words:
        fc = Counter(w)
        CL = len(w)
        firing_steps = defaultdict(list)
        for k, m in enumerate(w):
            firing_steps[m].append(k)

        for t in range(n):
            if fc[t] < 2:
                continue
            steps_t = firing_steps[t]
            left_t = (t-1)%n
            right_t = (t+1)%n

            for pi in range(len(steps_t)):
                a = steps_t[pi]
                s = steps_t[(pi+1) % len(steps_t)]

                lf = 0
                rf = 0
                if s > a:
                    for k in range(a+1, s):
                        if w[k] == left_t: lf += 1
                        if w[k] == right_t: rf += 1
                else:
                    for k in range(a+1, CL):
                        if w[k] == left_t: lf += 1
                        if w[k] == right_t: rf += 1
                    for k in range(0, s):
                        if w[k] == left_t: lf += 1
                        if w[k] == right_t: rf += 1

                # One-sided: exactly one neighbor fires 0
                if lf == 0 and rf > 0:
                    if right_t in binary_pos:
                        if rf % 2 == 0:
                            even_count += 1
                        else:
                            odd_count += 1
                elif rf == 0 and lf > 0:
                    if left_t in binary_pos:
                        if lf % 2 == 0:
                            even_count += 1
                        else:
                            odd_count += 1

    print(f"  One-sided phases with binary active: even fires = {even_count}, odd fires = {odd_count}")
    if even_count + odd_count > 0:
        print(f"  Even fraction: {100*even_count/(even_count+odd_count):.1f}%")
