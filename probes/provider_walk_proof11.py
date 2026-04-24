"""
CORRECTED one-sided excursion check.

On the ring Z_n, the two sides of proc b are:
  CW arc from b: positions b+1, b+2, ..., up to the next binary CW
  CCW arc from b: positions b-1, b-2, ..., up to the next binary CCW

But actually, for the provider, "one-sided" means:
  The excursion visits ONLY positions that are accessible from b without
  crossing a specific neighbor.

More precisely: for the provider, we need proc t such that:
  - One neighbor of t (say left_t) fires 0 in the phase
  - The other neighbor (right_t) is binary with even fires >= 2

So "one-sided" for the PROVIDER means: in a phase of t, one neighbor fires 0.
This happens when the walk stays on one side of t during the phase.

But the provider's "t" is typically the neighbor of b (binary), not b itself.
So we should look at it from t's perspective, not b's.

Let me reformulate:

For a ternary proc t between binary b_L = left(t) and some other proc
(could be binary or ternary):
  Phase of t: between step a (t nonmover) and step s (t fires).
  In [a, s), t doesn't fire.

  Provider = phase where one neighbor fires 0 and the other is binary with even fires >= 2.

The walk constraint: in [a, s), the walk doesn't visit t. So the walk
is confined to one side of t at a time (it can only visit one side of t
continuously, since to cross from one side to the other, the walk must pass
through t, but t doesn't fire in [a,s)).

WAIT. That's the key: t doesn't fire in [a, s). So the walk doesn't visit
position t during [a, s). The walk is at positions that are all on ONE SIDE
of t (since the ring minus {t} is a path, and the walk moves +-1, so it
stays connected on one side).

NO: the walk CAN visit both sides of t if it wraps around the ring the long
way. On Z_n minus {t}, the remaining positions form a PATH: t+1, t+2, ..., t-1.
The walk, moving +-1 at each step, stays on this path. The path is connected,
so the walk CAN reach any position. However, all positions on this path are
"on the same side" in the path sense -- but they span BOTH the CW and CCW
sides of t on the original ring.

Hmm. Let me reconsider.

The ring is: ..., t-2, t-1, t, t+1, t+2, ...
Remove t: path is t+1, t+2, ..., t-1 (going CW from t+1 to t-1, length n-1).

For the provider, t has two neighbors: left(t) = t-1, right(t) = t+1.
In the phase [a, s), the walk doesn't visit t. So the walk is on the path
t+1, ..., t-1. Both t+1 and t-1 are on this path (at the two ENDS).

The walk can visit both t+1 and t-1 during the phase (by traversing the path
from one end to the other, which requires n-2 steps). This would mean BOTH
neighbors fire during the phase, and neither is "silent."

For the provider, we need ONE neighbor to be silent (fire 0 in the phase).
This means the walk must STAY on a sub-path that doesn't include one end.

If left(t) = t-1 fires 0 in the phase: the walk never reaches t-1 in [a, s).
So the walk is confined to {t+1, t+2, ..., t-2} (a sub-path not including t-1).
The walk enters from the LEFT of this sub-path (from t, but t doesn't fire, so
the walk was already in the sub-path at step a).

Actually, at step a, the walk is at some position p = word[a] ≠ t. And at
step s, the walk arrives at t (word[s] = t). In [a, s), the walk is at
non-t positions, moving +-1.

For left(t) = t-1 to fire 0: the walk never visits t-1 in [a, s). Since the
walk is on the path t+1, ..., t-1 (removing t), and t-1 is the far end,
the walk must stay in {t+1, ..., t-2}, never reaching the far end.

This is possible when the excursion is "short" -- doesn't traverse the full
path from t+1 to t-1.

OK, let me just redo the computation with a CORRECT definition of one-sided.
"""
import sys
sys.path.insert(0, './claude')


def check_provider_correct_v2(word, ms, n):
    """Correct provider check: for each proc t, each phase [a,s), check
    if one neighbor fires 0 and the other is binary with even fires >= 2."""
    L = len(word)

    fire_steps = {}
    for p in range(n):
        fire_steps[p] = []
    for i, m in enumerate(word):
        fire_steps[m].append(i)

    for t in range(n):
        fsteps = fire_steps[t]
        for s in fsteps:
            prev_fire = -1
            for k in range(s - 1, -1, -1):
                if word[k] == t:
                    prev_fire = k
                    break

            left_t = (t - 1) % n
            right_t = (t + 1) % n

            left_acc = 0
            right_acc = 0

            for a in range(s - 1, prev_fire, -1):
                if word[a] == t:
                    continue
                if word[a] == left_t:
                    left_acc += 1
                elif word[a] == right_t:
                    right_acc += 1

                lf = left_acc
                rf = right_acc

                if lf == 0 and ms[right_t] == 2 and rf >= 2 and rf % 2 == 0:
                    return True, (t, a, s, 'left_silent', rf)
                if rf == 0 and ms[left_t] == 2 and lf >= 2 and lf % 2 == 0:
                    return True, (t, a, s, 'right_silent', lf)

    return False, None


def check_one_sided_excursion_correct(word, ms, n):
    """CORRECT one-sided excursion check.

    An excursion from binary b between consecutive firings s1, s2 is one-sided
    if one neighbor of b does NOT fire during the excursion.

    This is exactly the provider condition for t = the non-firing neighbor:
    - t doesn't fire in (s1, s2) (since the walk stays on one side)
    - b (binary) fires 2 times (at s1 and s2) — but we need the fires in the PHASE.

    Actually, the provider needs: in the phase [a, s) of t, one neighbor fires 0
    and the other is binary with even fires >= 2.

    The excursion from b between s1 and s2:
    - b fires at s1 and s2
    - Neighbor t doesn't fire between s1 and s2 (one-sided)

    For the provider: we need a phase of t where b fires >= 2 (even) and the
    other neighbor of t fires 0. The phase of t is [a, s) where:
    - a: step where t is nonmover, a < s
    - s: step where t fires
    - t doesn't fire in [a, s)

    If t doesn't fire between s1 and s2 (during b's excursion), then the
    ENTIRE interval (s1, s2) is within one "gap" of t (t doesn't fire here).
    If t fires AFTER s2, then there's a phase of t with s > s2 and a <= s1,
    containing the excursion.

    In that phase [a, s):
    - b fires at s1 and s2 (at least 2 times, both in [a, s) if a <= s1)
    - The fire count of b in [a, s) >= 2 and is even (since b fires twice in the excursion, possibly more)
    - The other neighbor of t: could fire anywhere in [a, s)

    For the other neighbor to fire 0, we need a < s1 ideally, so that between
    a and s, the walk is just the excursion from b (which stays on b's side).

    This is getting circular. Let me just check the correct provider definition.
    """
    L = len(word)
    binary_procs = [i for i in range(n) if ms[i] == 2]

    fire_steps = {p: [] for p in range(n)}
    for i, m in enumerate(word):
        fire_steps[m].append(i)

    results = []

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

            left_b = (b - 1) % n
            right_b = (b + 1) % n

            left_fires_exc = sum(1 for p in exc if p == left_b)
            right_fires_exc = sum(1 for p in exc if p == right_b)

            if left_fires_exc == 0:
                results.append((b, s1 % L, s2 % L, 'left_silent', 0, right_fires_exc))
            if right_fires_exc == 0:
                results.append((b, s1 % L, s2 % L, 'right_silent', left_fires_exc, 0))

    return results


def main():
    n = 5
    ms = [2, 3, 2, 3, 2]

    print(f"n={n}, ms={ms}\n")

    # Test specific CE
    word = [1, 0, 1, 0, 1, 2, 3, 4, 3, 4, 3, 2]
    print(f"CE word: {word}")

    # Check excursions
    results = check_one_sided_excursion_correct(word, ms, n)
    print(f"One-sided excursions: {len(results)}")
    for r in results:
        b, s1, s2, side, lf, rf = r
        print(f"  Binary {b} exc [{s1}->{s2}]: {side}, left_fires={lf}, right_fires={rf}")

    # Check provider
    found, info = check_provider_correct_v2(word, ms, n)
    print(f"Binary provider: {found}, {info}")

    print()

    # Now: what is the MINIMAL SUFFICIENT condition?
    # The excursion from binary b between s1 and s2 has one neighbor silent.
    # The excursion fires b at s1 and s2 (count = 2, even, >= 2).
    # But for the PROVIDER at proc t (the silent neighbor):
    #   We need t to fire at some step s > s2 (the firing step of the phase).
    #   And t must be nonmover at some step a <= s1 (the start of the phase).
    #   And t must not fire in [a, s).
    #
    # The issue: if t fires BETWEEN s1 and s2 (which we said it doesn't if silent),
    # good. But t needs to fire SOMEWHERE (fc >= 2). If t fires OUTSIDE the
    # excursion, the phase of t that includes the excursion will have the
    # excursion's firings PLUS potentially other firings. The "other" neighbor
    # might fire outside the excursion too, making it non-silent.
    #
    # KEY: We need the phase of t (between its consecutive firings) to contain
    # the excursion AND have the other neighbor be silent.

    # Let me check: for the CE, why does the provider fail?
    print("=== Detailed phase analysis for CE ===")
    fire_steps = {p: [] for p in range(n)}
    for i, m in enumerate(word):
        fire_steps[m].append(i)

    print(f"Fire steps: {dict(fire_steps)}")

    # Binary 0: fires at [1, 3]
    # Excursion [1->3]: [1] (just proc 1). Left(0) = 4 fires 0, Right(0) = 1 fires 1.
    # So right(0)=1 fires, left(0)=4 is silent.
    # Provider: t = 4 (left of 0), phase needs t=4 to fire with 0 as active binary neighbor.
    # But left(4)=3 and right(4)=0. So we need phase of 4 with right(4)=0 as binary active.
    # Phase of 4: between 4's firings. 4 fires at [7, 9].
    # Phase: a < 7, s = 7 (or 9). In [a, 7), 4 doesn't fire.
    # Firings of 0 in [a, 7): 0 fires at 1, 3.
    # Firings of 3 (left of 4) in [a, 7): 3 fires at 6.
    #
    # For the phase [a=0, s=7]: right(4)=0 fires at 1,3 (2 fires, even >=2).
    #   left(4)=3 fires at 6 (1 fire, NOT 0). So left(4) is NOT silent.
    #
    # For phase [a=3, s=7]: right(4)=0 fires at... hmm, 0 fires at 3, but we need
    # [a,s) = [3, 7). Step 3: mover=0, so 0 fires. Fire count of 0 in [3,7) = 1
    # (only step 3). Not >= 2.
    #
    # For phase [a=4, s=7]: right(4)=0 fires 0 times in [4,7).
    # For phase [a=5, s=7]: same.
    # For phase [a=6, s=7]: same.
    #
    # So the issue: in phases of t=4, either left(4)=3 fires (not silent) or
    # right(4)=0 fires < 2.

    for t in range(n):
        left_t = (t - 1) % n
        right_t = (t + 1) % n
        fsteps = fire_steps[t]
        print(f"\nProc {t} (m={ms[t]}), fires at {fsteps}, left={left_t}(m={ms[left_t]}), right={right_t}(m={ms[right_t]})")

        for s in fsteps:
            prev_fire = -1
            for k in range(s - 1, -1, -1):
                if word[k] == t:
                    prev_fire = k
                    break

            best_phases = []
            left_acc = 0
            right_acc = 0
            for a in range(s - 1, prev_fire, -1):
                if word[a] == t:
                    continue
                if word[a] == left_t:
                    left_acc += 1
                elif word[a] == right_t:
                    right_acc += 1
                lf = left_acc
                rf = right_acc

                is_provider = False
                if lf == 0 and ms[right_t] == 2 and rf >= 2 and rf % 2 == 0:
                    is_provider = True
                if rf == 0 and ms[left_t] == 2 and lf >= 2 and lf % 2 == 0:
                    is_provider = True

                if lf == 0 or rf == 0:
                    best_phases.append((a, s, lf, rf, is_provider))

            if best_phases:
                for a, s, lf, rf, prov in best_phases:
                    p_str = " PROVIDER" if prov else ""
                    print(f"  Phase [{a},{s}): L_fires={lf}, R_fires={rf}{p_str}")


if __name__ == "__main__":
    main()
