"""
Deep analysis of the provider problem.

The existing approach in CaseObstructionsCore.lean:
  1. Prove ∃ binary b with fc(b) = 2 (pigeonhole: if all binary fc >= 4, EC)
  2. Passthrough binary -> one-sided excursion -> provider

The gap is in step 1: proving binary fc=2 exists.

But actually: step 1 in the LEAN code says:
  "If all binary have fc != 2, then all binary have fc >= 4 (since fc is even).
   A binary proc with fc >= 4 creates entry conflict by pigeonhole."

This pigeonhole argument: binary proc b fires >= 4 times. Binary has 2 states.
At each firing, the context is (L, b_val, R). With b_val in {0,1}, b fires
with val=0 at least twice (pigeonhole), creating two mover steps with same b_val.
If L and R also match at two of these, we get entry conflict.

But L and R can differ! The question is whether L and R can be different enough
at all 4+ firings to avoid a match. With m_L and m_R states for the neighbors,
there are m_L * m_R possible (L,R) pairs. With same b_val and 2+ such firings:
if m_L * m_R < number_of_same_val_firings, pigeonhole gives a match.

For binary b with fc >= 4: at least 2 firings have val=0 and 2 have val=1.
We need 2 firings with same (L, val=0, R) for EC. Number of (L,R) pairs = m_L * m_R.
If m_L * m_R < 2, impossible (m_L, m_R >= 2, so product >= 4). So pigeonhole needs more.

Actually, let me reconsider. In the good cycle, configs are DISTINCT. At each
firing of b with val=0, the full config is different. But two firings of b with
same (L, b=0, R) would give same local context -> entry conflict IF one of them
is also a nonmover step at some OTHER proc with the same local context.

Wait, the entry conflict is at proc b: two steps where b is mover (both have
b fire, so b IS the mover), and the (L, S, R) = (L, 0, R) matches. For entry
conflict we need one MOVER step and one NON-MOVER step with same context.

So the pigeonhole is: among all firings of b with val=0, these are MOVER steps.
We need a NON-MOVER step at b with the same (L, 0, R). The non-mover steps at b
are all steps where b doesn't fire. At such steps, b has some value, and L, R are
some values.

So the argument isn't pure pigeonhole on mover steps. It's about matching a mover
context with a nonmover context.

ALTERNATIVE APPROACH: Instead of proving fc(binary)=2, prove directly that the
provider exists by analyzing the WALK REVERSAL STRUCTURE.

The walk is ZW with cw > 0, so it reverses direction at least twice.
Each reversal creates a "bounce" where the walk visits a proc, goes one way,
comes back.

CLAIM: At a reversal point in the interior of a ternary arc (between two binary
procs), the walk creates an excursion that stays within the arc. This excursion
has the arc's boundary binary proc(s) as the active side(s).

Let me verify this claim computationally at n=9.

Actually, let me take a step back and think about what walk words look like
at n=9 with CL > 2n = 18.

With ZW: cw_steps = ccw_steps. cw + ccw = L - stay_steps. cw = ccw.
L = 2*cw + stay. cw >= 1.

If L = 2n+1 = 19: cw + ccw <= 19, stay >= 0. cw = ccw, so 2*cw + stay = 19.
Since cw >= 1: cw >= 1, stay = 19 - 2*cw.

The walk visits all n=9 procs (fc >= 2 for all, no safe). In a ZW walk that
visits all procs, the walk must go at least from the leftmost to rightmost proc.
On a ring of 9, the walk must traverse at least half the ring in each direction.

Let me think about this differently. The walk on the ring is like a walk on
Z_9 (modular). ZW means net displacement 0 mod 9 AND |net| < 2*9.
So net displacement is 0.

The walk goes both CW and CCW (cw > 0 by hypothesis). It visits all procs.

KEY INSIGHT: The walk partitions into CW runs and CCW runs.
A CW run: consecutive CW steps (movers increasing by 1 mod n).
A CCW run: consecutive CCW steps.
Possibly stay steps in between.

Between a CW run ending at position p and a CCW run starting at position p,
there's a reversal. At the reversal, the walk was at p, going CW, then turns
and goes CCW.

NOW: consider the binary procs on the ring. They divide the ring into arcs of
ternary procs. With >= 3 binary and non-consecutive, each binary has at least
one ternary neighbor on each side.

A CW run from binary b1 to binary b2 (the next binary CW) traverses the
ternary arc between them. If the walk reverses WITHIN this arc (i.e., at a
ternary proc in the interior of the arc), then:

The reversal creates a "mini excursion": the walk goes from p to some q in
the arc, then turns back to p. Between the outward and return visits of p:
- p fires twice (once outward, once return)
- q fires (at the turnaround)
- Procs beyond q don't fire during this excursion

This creates a TernaryPhase for the boundary binary proc:
- The binary fires 2 (even >= 2) during the excursion
- The far-side neighbor doesn't fire (silent)

Actually no. Let me reconsider. The reversal at position r means:
..., r-1, r, r-1, ... (CW then CCW bounce at r)
or ..., r+1, r, r+1, ... (CCW then CW bounce at r)

If r is ternary and in the arc between binary b1 and b2, then the walk bounces
at r. The walk comes from b1's side, reaches r, bounces back toward b1.

For the PROVIDER: we need a proc t with one silent neighbor and one active binary
neighbor with even fires. The bouncing at r doesn't directly give this.

BUT: the walk going from b1 toward b2, reaching r, and bouncing back:
- If the walk started from b1 (b1 fires), goes CW past ternary procs toward b2,
  reaches r, bounces, comes back to b1 (b1 fires again):
  This is an excursion from b1 that stays on the CW side (between b1 and b2).
  In this excursion, b1's CW neighbor fires (it's in the arc), but b1's CCW neighbor
  does NOT fire (the walk stayed CW).

  So: t = b1's CCW neighbor (ternary). Phase: between b1's two firings.
  - left(t) = b1 (binary), fires 2 (even >= 2) in the phase
  - right(t) = next ternary (in the CCW direction), fires 0 (silent)

  WAIT: t = CCW neighbor of b1. left(t) = CCW neighbor of t, right(t) = t's CW
  neighbor = b1. So:
  - right(t) = b1 (binary), fires 2 in the phase
  - left(t) fires 0 (silent) since the walk stayed CW of b1

  This IS the provider!

So the CLAIM: in a ZW walk with cw > 0 and all fc >= 2 and some fc >= 3,
there exists a binary proc b such that some excursion from b stays on one side
AND the binary fires 2 (even) in that excursion.

The excursion fires = 2 because: b fires at the start, the walk goes one way,
comes back, b fires at the end. That's 2 firings of b in the excursion. 2 is even.

The key is: does such a one-sided excursion always exist?

For this, we need: the walk reverses AT LEAST ONCE while traversing an arc
that includes a binary proc at its boundary. Since the walk is ZW with cw > 0,
it MUST reverse (it can't be monotone CW or CCW forever on a ring and return
with net 0). With >= 3 binary procs creating >= 3 arcs, and the walk having
>= 2 reversals, by pigeonhole some reversal is near a binary proc.

Actually, a reversal can be at ANY position, including at a binary proc itself.

Let me verify this argument computationally.
"""
import sys
sys.path.insert(0, './claude')


def find_reversals(word, n):
    """Find reversal points in the walk."""
    L = len(word)
    reversals = []
    for i in range(L):
        prev_i = (i - 1) % L
        next_i = (i + 1) % L
        prev_dir = (word[i] - word[prev_i]) % n
        next_dir = (word[next_i] - word[i]) % n
        # CW = +1 mod n, CCW = -1 mod n = n-1 mod n
        if prev_dir == 1 and next_dir == n - 1:  # was CW, now CCW
            reversals.append((i, 'CW->CCW'))
        elif prev_dir == n - 1 and next_dir == 1:  # was CCW, now CW
            reversals.append((i, 'CCW->CW'))
    return reversals


def find_one_sided_excursion(word, ms, n):
    """Find a one-sided excursion from a binary proc."""
    L = len(word)
    binary_procs = [i for i in range(n) if ms[i] == 2]

    fire_steps = {p: [] for p in range(n)}
    for i, m in enumerate(word):
        fire_steps[m].append(i)

    for b in binary_procs:
        fsteps = fire_steps[b]
        if len(fsteps) < 2:
            continue

        for idx in range(len(fsteps)):
            s1 = fsteps[idx]
            s2 = fsteps[(idx + 1) % len(fsteps)]
            if s2 <= s1:
                s2 += L

            exc = [word[k % L] for k in range(s1 + 1, s2)]
            if not exc:
                continue

            exc_set = set(exc)

            # Check if excursion stays on one side
            cw_side = set()
            ccw_side = set()
            for d in range(1, n):
                cw_side.add((b + d) % n)
                ccw_side.add((b - d) % n)

            if exc_set <= cw_side or exc_set <= ccw_side:
                # One-sided! Check fire counts
                side = "CW" if exc_set <= cw_side else "CCW"

                # b's fires in this phase: always 2 (at s1 and s2)
                # But we need the PHASE around a neighbor t
                # t = neighbor on the NON-excursion side
                if exc_set <= cw_side:
                    t = (b - 1) % n  # CCW neighbor (non-excursion side)
                else:
                    t = (b + 1) % n  # CW neighbor (non-excursion side)

                # Check t doesn't fire in excursion
                t_fires = sum(1 for p in exc if p == t)
                if t_fires == 0:
                    return True, (b, s1 % L, s2 % L, t, side, len(exc))

    return False, None


def comprehensive_check():
    """Check at n=5 with the walk constraint analysis."""
    n = 5
    ms_list = [[2, 3, 2, 3, 2]]

    for ms in ms_list:
        print(f"\nn={n}, ms={ms}")
        total = 0
        has_exc = 0
        has_provider_binary = 0
        no_exc_no_provider = []

        for L in range(11, 16):
            def gen(word):
                nonlocal total, has_exc, has_provider_binary
                if len(word) == L:
                    disp = 0
                    cw = 0
                    for i in range(L):
                        nxt = word[(i + 1) % L]
                        diff = (nxt - word[i]) % n
                        if diff == 1:
                            cw += 1
                            disp += 1
                        elif diff == n - 1:
                            disp -= 1
                    if disp != 0 or cw == 0:
                        return
                    fc = [0] * n
                    for m in word:
                        fc[m] += 1
                    if any(f < 2 for f in fc):
                        return
                    if max(fc) < 3:
                        return
                    touched = set()
                    for m in word:
                        touched.add(m)
                        touched.add((m-1)%n)
                        touched.add((m+1)%n)
                    if len(touched) < n:
                        return

                    total += 1
                    found_exc, info = find_one_sided_excursion(word, ms, n)
                    if found_exc:
                        has_exc += 1
                    else:
                        if len(no_exc_no_provider) < 5:
                            no_exc_no_provider.append((L, list(word), list(fc)))
                    return

                last = word[-1]
                for nxt in [(last - 1) % n, last, (last + 1) % n]:
                    word.append(nxt)
                    gen(word)
                    word.pop()

            for start in range(n):
                gen([start])

        print(f"Total valid walks: {total}")
        print(f"Has one-sided excursion with silent neighbor: {has_exc}")
        print(f"Missing: {total - has_exc}")

        if no_exc_no_provider:
            print(f"\nSample walks without one-sided excursion:")
            for L, w, fc in no_exc_no_provider:
                reversals = find_reversals(w, n)
                print(f"  L={L}: {w}, fc={fc}")
                print(f"    Reversals: {reversals}")

                # Show excursions
                binary_procs = [i for i in range(n) if ms[i] == 2]
                fire_steps = {p: [] for p in range(n)}
                for i, m in enumerate(w):
                    fire_steps[m].append(i)

                for b in binary_procs:
                    fsteps = fire_steps[b]
                    for idx in range(len(fsteps)):
                        s1 = fsteps[idx]
                        s2 = fsteps[(idx+1) % len(fsteps)]
                        if s2 <= s1:
                            s2 += L
                        exc = [w[k%L] for k in range(s1+1, s2)]
                        print(f"    Binary {b} exc [{s1}->{s2%L}]: {exc}")


if __name__ == "__main__":
    comprehensive_check()
