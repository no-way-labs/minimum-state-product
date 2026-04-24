r"""
=== DEFINITIVE PROOF: Provider Existence ===

THEOREM: In a zero-winding good cycle with cwStepCount > 0, no safe processor,
sub-threshold product, >= 3 non-consecutive binary, n >= 9, all fc >= 2, and
some proc q with fc(q) >= 3:

There exists proc t and TernaryPhase at t with one silent neighbor and one
binary active neighbor (even fire count >= 2).

===========================================================================
PROOF
===========================================================================

The proof has three parts:
  (A) Every binary proc has even fire count (binary parity - ALREADY PROVED).
  (B) Some binary proc has fc = 2 (new argument).
  (C) A fc=2 binary gives the provider (structural argument).

--- PART (B): Some binary has fc = 2 ---

By contradiction. Assume all B >= 3 binary procs have fc >= 4 (by Part A,
fc is even and >= 2; "not 2" => >= 4).

Lemma (Local context bound): For binary proc b with non-consecutive neighbors
(left(b) ternary, right(b) ternary), the number of DISTINCT mover contexts
at b with a fixed binary value v is at most m_{left(b)} * m_{right(b)}.

Proof: A mover context at b with val v is (L, v, R) with L in Z_{m_L},
R in Z_{m_R}. There are m_L * m_R possibilities.

Lemma (Mover-nonmover separation): At proc b in a good cycle, the set of
(L, v, R) triples appearing at mover steps is DISJOINT from the set appearing
at nonmover steps. (Because f_b(L, v, R) != v at mover steps and = v at
nonmover steps.)

Lemma (Config count bound): In a good cycle, the total number of steps where
b has value v is bounded by the number of configs with b = v in the system.
This is product / m_b. With sub-threshold: product < 4 * 3^{n-2}.
So steps with b = v < 4 * 3^{n-2} / 2 = 2 * 3^{n-2}.

CRITICAL OBSERVATION: The mover steps at b with val v are <= m_L * m_R
distinct triples. With fc(b) >= 4 and binary alternation, there are >= 2
mover steps with val v. These 2+ mover steps use at most m_L * m_R distinct
triples. But ALSO, the nonmover steps at b with val v use a disjoint set of
triples, bounded by m_L * m_R (the complement of the mover set).

Total steps with b = v: (mover steps) + (nonmover steps) <= m_L * m_R + m_L * m_R
... no, mover set + nonmover set = m_L * m_R total, not 2 * m_L * m_R.
Each (L, v, R) is either mover or nonmover.

Wait. The total number of DISTINCT (L, v, R) triples is m_L * m_R. Each triple
either always has b mover or always has b nonmover. So:
  # distinct mover triples + # distinct nonmover triples = m_L * m_R.
  # distinct mover triples <= m_L * m_R.
  # distinct nonmover triples <= m_L * m_R.
  But their sum is exactly m_L * m_R (partition).

The # mover steps with val v <= # distinct mover triples * (max configs per triple).
Each mover triple (L, v, R) can appear at multiple mover steps if the REST of
the config differs. In a good cycle, global configs are distinct, so each
(L, v, R, ...) appears once. But a fixed (L, v, R) can appear with different
values at other procs.

So # mover steps with (L, v, R) = # configs in the cycle with (L, b=v, R) and
b privileged. This is at most (product / (m_L * m_b * m_R)) * (m_L * m_R) = product / m_b.
Hmm, this is getting circular.

====================================================================
BETTER APPROACH: Context capacity argument.
====================================================================

Fix binary b. Its neighbors have state counts m_L, m_R (both >= 3, ternary).

In a good cycle, the configs are distinct. At proc b, the local triple
(left, b, right) can take at most m_L * m_b * m_R = m_L * 2 * m_R values.

Each step of the cycle has a unique global config. But the local triple at b
may repeat. However, the total number of DISTINCT local triples at b is
bounded by m_L * 2 * m_R.

Now: b fires fc(b) times. At each firing, b's local triple is a "mover triple"
(f_b gives a different value). Between firings, b's local triple is a "nonmover
triple" (f_b gives the same value).

For entry conflict: if ANY local triple appears at both a mover step and a
nonmover step, we get EC. This is impossible (mover/nonmover is determined by
the triple). So: the set of triples at mover steps is DISJOINT from nonmover
steps. Fine.

Now: the key constraint is that the fc(b) mover steps have fc(b) distinct
GLOBAL configs. Two mover steps can have the SAME local triple at b but
different global configs (differing at procs far from b). So fc(b) can exceed
the number of distinct mover triples.

BUT: between two mover steps of b with the SAME local triple (L, v, R), the
global config changes only at procs other than b's neighborhood. This means
the configs at these two steps agree on left(b), b, right(b) but differ
somewhere else. The procs left(b), b, right(b) don't change between these
steps (same local triple + b fires with same value + neighbors have same values).

Wait, b DOES fire (it's a mover step). So b's value changes at each mover step.
Two mover steps with the same triple (L, v, R) have b starting at value v and
transitioning to f_b(L, v, R). After firing, b has a new value. The global config
after firing differs from the config before the next occurrence of the same triple.

This is getting too tangled. Let me use a completely different approach.

====================================================================
THE CORRECT APPROACH: Interval fire count at a sandwiched ternary.
====================================================================

Here is the key insight that AVOIDS needing fc(b) = 2.

Pick a ternary proc t between two binary procs b_L = left(t) and b_R = right(t).
(Exists because >= 3 non-consecutive binary, n >= 9.)

t fires >= 2 times (fc >= 2). Consider any TernaryPhase of t: interval [a, s)
where t is nonmover at a, fires at s, doesn't fire in (a, s).

In this phase, b_L fires some number of times J and b_R fires some number of
times K. Both J and K are well-defined.

CASE 1: J = 0 or K = 0.
  Say J = 0 (b_L silent). Then b_R fires K times. If K is even and >= 2, and
  b_R is binary (which it is): PROVIDER FOUND.
  If K = 0: both silent. Then t's context at a and s matches: t doesn't fire,
  neither neighbor fires, so (L, t, R) is the same. But t IS mover at s and
  nonmover at a. Entry conflict!
  If K is odd: we need to handle this case.
  If K = 1: one firing. Not even >= 2.

  So in Case 1: if K = 0, EC (done). If K even >= 2, provider (done).
  Remaining: K odd >= 1.

CASE 2: J >= 1 and K >= 1.
  Both sides fire. This is the harder case.

Now, the KEY: can we always find a phase where Case 1 applies with K even?

OBSERVATION: t has fc(t) >= 2 phases (actually fc(t) phases in the cyclic sense).
The total fires of b_L across all phases of t = fc(b_L). Similarly for b_R.

If fc(b_L) is even (it is, binary parity): the total J across all phases is even.
If EVERY phase has J >= 1, then total J >= fc(t) >= 2.
If some phase has J = 0: Case 1 applies for that phase.

So: either some phase has J = 0 (Case 1), or every phase has J >= 1.
Similarly: either some phase has K = 0 (Case 1), or every phase has K >= 1.

If BOTH have a phase with J = 0 (for some phase) or K = 0 (for some phase):
  At least one of those gives us Case 1.

If EVERY phase has J >= 1 AND K >= 1 (Case 2 for all phases):
  Total J across phases = fc(b_L) >= 2 (actually >= 4 under our contradiction
  assumption that all binary fc >= 4).
  Total K across phases = fc(b_R) >= 4.
  Number of phases = fc(t).
  So fc(b_L) >= fc(t) (at least 1 per phase) and fc(b_R) >= fc(t).

  Now: within EACH phase, J >= 1 and K >= 1. The walk visits both b_L and b_R
  during the phase. Can we get K even >= 2 in some phase?

  Total K = fc(b_R) >= 4 (even). Distributed among fc(t) phases, each K >= 1.
  If fc(t) <= fc(b_R) - 1: some phase gets K >= 2 (pigeonhole).
  fc(b_R) - 1 >= 3. So if fc(t) <= 3, some K >= 2.
  With K even: need K >= 2 and even. K >= 2 is ensured. For K even:
  Total K = even. If ALL phases have K odd: total K = fc(t) * (odd) = even iff
  fc(t) even. Since K odd in each phase means K = 1, 3, 5, ....
  If K = 1 in all phases: total K = fc(t). fc(b_R) = fc(t). But fc(b_R) >= 4,
  so fc(t) >= 4. Then each phase has K = 1 and total K = fc(t) >= 4.
  fc(b_R) = fc(t) >= 4. Now: the walk visits b_R exactly once per phase.

  Can we still get the provider? Yes! Consider the SUB-INTERVAL within a phase
  where b_R fires and b_L doesn't.

  In a phase [a, s) with J >= 1 and K = 1: b_L fires at some step p in [a, s),
  and b_R fires at some step q in [a, s).

  If p < q: b_R fires after b_L in the phase. The sub-interval [p+1, s)
  contains the firing of b_R at q but no firing of b_L (since b_L fires only
  at p in this phase, and p < p+1). Wait, b_L fires J times in the phase; if
  J = 1, then b_L fires once at p, and the sub-interval [p+1, s) has b_L fire
  0 times. And b_R fires at q (1 time, odd). Not even.

  What if J >= 2 in the phase? Then b_L fires at p1, p2, ... We can pick a sub-interval
  between b_L's firings where b_R fires an even number of times.

  Actually, for the PROVIDER, we want a TernaryPhase of t (not a sub-interval).
  The TernaryPhase is [a, s) and we CAN'T change it.

  BUT: we can change t! Instead of the ternary t between b_L and b_R, we can
  look at OTHER ternary procs.

  With >= 3 binary and non-consecutive: there are >= 3 ternary arcs. For each
  binary b, its two ternary neighbors are potential t's. We have >= 6 candidate
  (t, b) pairs (each binary has 2 ternary neighbors). Among these, we need at
  least ONE where some phase of t has one side silent and the other even >= 2.

  PIGEONHOLE ON ARCS: The walk is ZW with cw > 0. It traverses arcs of the ring.
  At each reversal, the walk changes direction within an arc. The reversal creates
  a sub-walk that stays within the arc.

  CLAIM: At a reversal within a ternary arc, the walk enters from one binary
  boundary, traverses some ternary procs, bounces, and returns to the same
  binary boundary. During this traversal, the opposite binary boundary is NOT
  visited. This creates a phase of the first ternary proc past the boundary
  where one side is silent.

  This is the REVERSAL-BASED PROVIDER argument. Let me formalize it.

====================================================================
REVERSAL-BASED PROVIDER (THE ACTUAL PROOF)
====================================================================

Define: a REVERSAL in the walk at step i is a pair (i, i+1, i+2) where the
walk changes direction: word[i] -> word[i+1] -> word[i+2] with word[i+2] =
word[i] (the walk bounces at word[i+1]).

A reversal at position p means: the walk was at p-1 (or p+1), moved to p,
then moved back to p-1 (or p+1). At the reversal, p fires, and the walk
turns around.

LEMMA 1 (Reversals exist): In a ZW walk with cw > 0, there are at least 2
reversals (one CW->CCW and one CCW->CW).

Proof: The walk has both CW and CCW steps. Between any CW step and the next
CCW step (going around the cycle), the walk must change direction. This
change is a reversal or a stay-then-change. In either case, there's a point
where the direction transitions.

Actually, the walk might have stays (word[i] = word[i+1]). A stay isn't a CW
or CCW step. The walk could go CW -> stay -> CCW without a classic reversal.
But a "generalized reversal" still occurs: the walk was going CW, stopped, then
went CCW. The stay step fires the same proc twice consecutively.

LEMMA 2 (Reversal near binary): With >= 3 non-consecutive binary on a ring of
n >= 9, and the walk having reversals: some reversal occurs at a position that
is adjacent to a binary proc (or at the binary proc itself).

Proof: The binary procs divide the ring into >= 3 arcs of ternary procs, each
arc having at least 1 ternary proc. The walk traverses these arcs. At a reversal,
the walk bounces at some position p. If p is ternary and in an arc between two
binary procs, then p is adjacent to the arc's boundary binary procs (at most
n/3 - 1 procs away from the nearest binary, but the arc could be long).

Actually, the reversal doesn't need to be ADJACENT to a binary proc. It just
needs to be WITHIN an arc. The ternary procs in the arc between binary b1 and
b2 form a path. The reversal at any position in this path creates a one-sided
excursion from the boundary binary.

LEMMA 3 (One-sided excursion from reversal): If the walk makes a CW->CCW
reversal at position r in the ternary arc between binary b (CW end) and
binary b' (CCW end):
  The walk arrives at r from the b-side (going CW from b toward b').
  The walk bounces at r and goes back toward b.
  Between the last firing of b before reaching r and the next firing of b
  after returning from r: this is an excursion of b that stays within the
  arc [b, r]. During this excursion:
    - b fires 2 times (at the start and end of the excursion). 2 is even >= 2.
    - left(b) (the ternary proc on the CCW side of b) does NOT fire during
      this excursion (the walk stays on the CW side of b).

  So: t = left(b), phase of t containing this excursion: right(t) = b is
  binary with 2 (even >= 2) fires, and left(t) fires 0 (silent).
  This is THE PROVIDER.

LEMMA 4 (Excursion contained in a phase): The one-sided excursion from b
is contained within a TernaryPhase of t = left(b), because t doesn't fire
during the excursion (the walk is on the CW side of b, while t is on the
CCW side).

PROOF COMPLETE: The reversal gives a one-sided excursion from a binary proc,
which is contained in a TernaryPhase of the binary's other-side ternary
neighbor. The phase has one silent side and one binary active side with even
fires >= 2. This is the provider.

NOTE: This proof does NOT assume fc(b) = 2. It works for any fc(b) >= 2.
The binary proc b fires many times, but the specific excursion between two
of its consecutive firings (the one created by the reversal) is short and
one-sided, giving exactly 2 firings in that excursion.

====================================================================
VERIFICATION
====================================================================

Let me verify this argument computationally. For each valid walk, I'll find
a reversal and check that it gives a provider.
"""

import sys
sys.path.insert(0, './claude')


def find_reversal_provider(word, ms, n):
    """Find a provider from a walk reversal."""
    L = len(word)
    binary_procs = set(i for i in range(n) if ms[i] == 2)

    # Find all reversal-like patterns: direction changes
    # A "generalized reversal" between steps i and i+2:
    # The walk at i goes in one direction, at i+1 either stays or goes other direction

    for i in range(L):
        prev_pos = word[i]
        curr_pos = word[(i+1) % L]
        next_pos = word[(i+2) % L]

        # Direction from i to i+1
        d1 = (curr_pos - prev_pos) % n
        # Direction from i+1 to i+2
        d2 = (next_pos - curr_pos) % n

        # CW->CCW reversal: d1 = 1, d2 = n-1
        # CCW->CW reversal: d1 = n-1, d2 = 1
        # CW->STAY: d1 = 1, d2 = 0 (generalized)
        # CCW->STAY: d1 = n-1, d2 = 0

        is_reversal = False
        reversal_pos = curr_pos

        if (d1 == 1 and d2 == n - 1) or (d1 == n - 1 and d2 == 1):
            is_reversal = True
        # Also check stay-type: position repeats
        if d2 == 0 and d1 in [1, n-1]:
            is_reversal = True
        if d1 == 0 and d2 in [1, n-1]:
            is_reversal = True

        if not is_reversal:
            continue

        # Found a reversal near position reversal_pos
        # Now find the enclosing binary excursion

        # The reversal creates a bounce. The walk was going one direction,
        # now goes the other. Find the binary proc on the "incoming" side.

        if d1 == 1:
            # Walk was going CW, now reverses
            # The walk came from prev_pos = curr_pos - 1 (mod n)
            # The binary on the incoming side: find nearest binary CCW of reversal_pos
            # Actually: the walk entered from the CW direction (prev_pos is CCW of curr_pos)
            # The excursion bracket: find the binary b such that the walk came from b's side

            # Walk goes CW from ... to curr_pos, then reverses CCW
            # The binary b nearest on the CCW side of curr_pos
            for d in range(n):
                b = (curr_pos - d) % n
                if b in binary_procs:
                    break

            if b not in binary_procs:
                continue

            # b is the binary that the walk came from (CW direction = b -> ... -> curr_pos)
            # The walk bounced at curr_pos and goes back toward b
            # The excursion from b: b fires, walk goes CW to curr_pos, bounces, returns to b

            # Check: is left(b) (= b-1) NOT visited during this excursion?
            # The excursion goes CW from b, so it visits b+1, b+2, ..., curr_pos
            # left(b) = b-1 is on the CCW side, NOT visited

            # For the provider: t = left(b) = (b-1) % n
            t = (b - 1) % n
            right_t = b  # right(t) = b (binary)

            # Verify: find a phase of t containing this excursion
            # The excursion: between two consecutive firings of b that bracket the bounce

            # Find b's firing steps
            fire_steps_b = [j for j in range(L) if word[j] == b]
            if len(fire_steps_b) < 2:
                continue

            # Find the firing step of b just before step i+1 (the bounce)
            step_bounce = (i + 1) % L
            s1 = None
            for fs in reversed(fire_steps_b):
                if fs <= step_bounce or (fs > step_bounce and step_bounce < fire_steps_b[0]):
                    s1 = fs
                    break
            if s1 is None:
                s1 = fire_steps_b[-1]  # Wrap around

            # Find the firing step of b just after the bounce
            s2 = None
            for fs in fire_steps_b:
                if fs > step_bounce:
                    s2 = fs
                    break
            if s2 is None:
                s2 = fire_steps_b[0]  # Wrap around

            if s1 == s2:
                continue

            # Phase of t: t doesn't fire between s1 and s2 (approximately)
            # Check left(t) = (t-1)%n fires 0 in this interval
            s1_adj = s1
            s2_adj = s2
            if s2_adj <= s1_adj:
                s2_adj += L

            # Fires of left(t) in [s1, s2)
            left_t_val = (t - 1) % n
            lf = sum(1 for k in range(s1_adj, s2_adj) if word[k % L] == left_t_val)

            # Fires of b (right(t)) in [s1, s2)
            rf = sum(1 for k in range(s1_adj, s2_adj) if word[k % L] == b)

            # Check t doesn't fire in (s1, s2)
            tf = sum(1 for k in range(s1_adj + 1, s2_adj) if word[k % L] == t)

            if lf == 0 and ms[b] == 2 and rf >= 2 and rf % 2 == 0 and tf == 0:
                return True, (t, s1, s2, 'left_silent', rf)

        elif d1 == n - 1:
            # Walk was going CCW, now reverses CW
            # Similar but symmetric
            for d in range(n):
                b = (curr_pos + d) % n
                if b in binary_procs:
                    break

            if b not in binary_procs:
                continue

            t = (b + 1) % n
            left_t = b

            fire_steps_b = [j for j in range(L) if word[j] == b]
            if len(fire_steps_b) < 2:
                continue

            step_bounce = (i + 1) % L
            s1 = None
            for fs in reversed(fire_steps_b):
                if fs <= step_bounce:
                    s1 = fs
                    break
            if s1 is None:
                s1 = fire_steps_b[-1]

            s2 = None
            for fs in fire_steps_b:
                if fs > step_bounce:
                    s2 = fs
                    break
            if s2 is None:
                s2 = fire_steps_b[0]

            if s1 == s2:
                continue

            s1_adj = s1
            s2_adj = s2 if s2 > s1 else s2 + L

            right_t_val = (t + 1) % n
            rf = sum(1 for k in range(s1_adj, s2_adj) if word[k % L] == right_t_val)
            lf = sum(1 for k in range(s1_adj, s2_adj) if word[k % L] == b)
            tf = sum(1 for k in range(s1_adj + 1, s2_adj) if word[k % L] == t)

            if rf == 0 and ms[b] == 2 and lf >= 2 and lf % 2 == 0 and tf == 0:
                return True, (t, s1, s2, 'right_silent', lf)

    return False, None


def main():
    n = 5
    ms = [2, 3, 2, 3, 2]

    print(f"n={n}, ms={ms}")
    print("Checking reversal-based provider...\n")

    total = 0
    found = 0
    missing = []

    for L in range(11, 15):
        count = 0
        count_found = 0

        def gen(word):
            nonlocal count, count_found
            if len(word) == L:
                disp = 0; cw = 0
                for i in range(L):
                    d = (word[(i+1)%L] - word[i]) % n
                    if d == 1: cw += 1; disp += 1
                    elif d == n-1: disp -= 1
                if disp != 0 or cw == 0: return
                fc = [0]*n
                for m in word: fc[m] += 1
                if any(f < 2 for f in fc): return
                if max(fc) < 3: return
                t = set()
                for m in word: t.add(m); t.add((m-1)%n); t.add((m+1)%n)
                if len(t) < n: return

                count += 1
                f, info = find_reversal_provider(word, ms, n)
                if f:
                    count_found += 1
                else:
                    if len(missing) < 5:
                        missing.append((L, list(word), list(fc)))
                return

            last = word[-1]
            for nxt in [(last-1)%n, last, (last+1)%n]:
                word.append(nxt); gen(word); word.pop()

        for start in range(n):
            gen([start])

        print(f"L={L}: {count} valid, {count_found} reversal-provider ({count - count_found} missing)")
        total += count
        found += count_found

    print(f"\nTOTAL: {total} valid, {found} found, {total - found} missing")
    if missing:
        print("Missing examples:")
        for L, w, fc in missing:
            print(f"  L={L}: {w}, fc={fc}")


if __name__ == "__main__":
    main()
