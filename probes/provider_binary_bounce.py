"""
Verify: every ZW walk with fc >= 2 and some fc >= 3 has a binary proc
that "bounces" (fires twice consecutively with the walk staying on one side).

A binary bounce at b: the walk is at b, fires b, goes to one side (say right),
comes back, fires b again. This means b fires twice with all intervening movers
on one side.

FORMALLY: binary b fires at steps s_i and s_{i+1} (consecutive). The excursion
[s_i, s_{i+1}] stays on one side. Moreover, the length of the excursion is such
that the neighbor on the excursion side fires an even number of times.

Actually, the "bounce" I need is simpler: between two consecutive firings of
a binary b, the walk stays on one side of b. This means one of b's neighbors
(the one on the other side) fires 0 in this interval.

Then: b's ternary neighbor t on the "other" side has a phase containing this
interval, where b (binary) fires >= 2 (even) and t's other neighbor (far side)
fires 0.

WAIT: The provider is at t (b's neighbor). In the phase of t:
  active side = b (binary, fires even >= 2)
  silent side = far side of t

For the SILENT side to fire 0: the far side of t must not fire during the phase.
This means the walk doesn't reach the far side of t during the phase.

If the walk stays on b's side of t during the phase: the far side is silent. YES!

And b fires at least 2 times in the phase (the two consecutive firings that
bracket the one-sided excursion). 2 is even >= 2. And b is binary. PROVIDER!

So the question reduces to: does every valid walk have a one-sided excursion
from some binary proc?

I already verified this at n=5: ALL 1,042,770 walks have a one-sided excursion.
But my "one-sided" definition was buggy (it was trivially true because the
"sides" covered all non-b procs).

Let me fix this. A one-sided excursion from binary b means: between two
consecutive firings of b, the walk stays on one side of b. "One side" means:
one of b's two neighbors doesn't fire during the excursion.

This is exactly: left(b) fires 0 in the excursion, OR right(b) fires 0.
"""
import sys
sys.path.insert(0, './claude')


def has_provider_via_one_sided_excursion(word, ms, n):
    """Check if any binary has a one-sided excursion that gives a provider."""
    L = len(word)
    binary_procs = [i for i in range(n) if ms[i] == 2]

    fire_steps = {p: [] for p in range(n)}
    for i, m in enumerate(word):
        fire_steps[m].append(i)

    for b in binary_procs:
        fsteps = fire_steps[b]
        if len(fsteps) < 2:
            continue

        left_b = (b - 1) % n
        right_b = (b + 1) % n

        for idx in range(len(fsteps)):
            s1 = fsteps[idx]
            s2 = fsteps[(idx + 1) % len(fsteps)]
            if s2 <= s1:
                s2 += L

            # Excursion: movers in (s1, s2) exclusive
            exc = [word[k % L] for k in range(s1 + 1, s2)]

            # Count neighbor fires in excursion
            left_fires = sum(1 for p in exc if p == left_b)
            right_fires = sum(1 for p in exc if p == right_b)

            # One-sided: one neighbor fires 0
            if left_fires == 0 or right_fires == 0:
                # Now check: does this create a provider?
                # The provider is at t = the SILENT neighbor of b.

                if left_fires == 0:
                    t = left_b  # t = left(b), silent in excursion
                    # Provider at t: right(t) = b is binary, fires >= 2 (s1 and s2),
                    #   even? The fire count of b in the PHASE of t.
                    # Phase of t: [a, s) where a < s1 (or a = some step in excursion)
                    #   and s = next firing of t after s2.
                    # But t doesn't fire during excursion (left_fires = 0).
                    # So the phase of t extends from before s1 to after s2
                    # (containing the entire excursion).

                    # In this phase: b fires at s1 and s2 (2 times, even >= 2).
                    # left(t) = left(left(b)) fires... could be anything.
                    # For the PROVIDER: we need left(t) to be silent (fires 0).
                    # left(t) = (b-2) % n.

                    # Hmm, left(t) could fire during the phase if the phase
                    # extends beyond the excursion. The phase goes from t's
                    # previous firing to t's next firing.

                    # Let's check: does left(t) fire 0 in the EXCURSION?
                    left_t = (t - 1) % n  # = (b - 2) % n
                    left_t_fires_exc = sum(1 for p in exc if p == left_t)

                    # If left_t fires 0 in excursion AND t fires right after
                    # the excursion (at s2+1 or soon after), then the phase
                    # [a, s) with s = t's firing step might have left_t fire 0.

                    # For simplicity, check if the EXCURSION itself gives the
                    # provider (restricting the phase to the excursion).

                    # Actually, the provider needs a TernaryPhase of t.
                    # If t doesn't fire in the excursion (left_fires=0 means
                    # t doesn't fire), then the entire excursion is within one gap.
                    # But the PHASE needs a=nonmover step AND s=mover step (t fires at s).
                    # t must fire at some point outside the excursion.

                    # If t fires at some step outside the excursion, the phase
                    # containing the excursion could be large and include other
                    # firings of left(t).

                    # The CORRECT approach: find a phase of t that contains
                    # EXACTLY the excursion (nothing more).
                    # This requires t to fire just before or just after the excursion.

                    # t = left(b). The walk is at b at step s1 and s2.
                    # After s2, the walk goes somewhere. If it goes to t (left of b),
                    # that means t fires at s2+1. Then the phase [s1, s2+1) contains
                    # the excursion. In this phase:
                    #   b fires 2 times (at s1 and s2), even >= 2, binary. Active!
                    #   left(t) = (b-2)%n fires... depends on the phase content.

                    # But we need to check whether t actually fires at s2+1.
                    # This depends on the walk.

                    # For now, let me just check the FULL provider condition
                    # using the direct phase enumeration.
                    pass

                if right_fires == 0:
                    t = right_b
                    pass

    # Fall back to direct phase check
    return check_provider_direct(word, ms, n)


def check_provider_direct(word, ms, n):
    """Direct provider check (known working version)."""
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
                    return True
                if rf == 0 and ms[left_t] == 2 and lf >= 2 and lf % 2 == 0:
                    return True
    return False


def main():
    """Check one-sided excursion AND direct provider for all walks."""
    n = 5
    ms = [2, 3, 2, 3, 2]
    binary_procs = [i for i in range(n) if ms[i] == 2]

    total = 0
    has_one_sided = 0  # One-sided excursion from binary
    has_provider = 0  # Direct binary provider

    for L in range(11, 14):
        def gen(word):
            nonlocal total, has_one_sided, has_provider
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

                total += 1

                # Check one-sided excursion (correct definition)
                fire_steps = {p: [] for p in range(n)}
                for i, m in enumerate(word): fire_steps[m].append(i)

                found_one_sided = False
                for b in binary_procs:
                    fsteps = fire_steps[b]
                    if len(fsteps) < 2: continue
                    left_b = (b-1) % n
                    right_b = (b+1) % n
                    for idx in range(len(fsteps)):
                        s1 = fsteps[idx]
                        s2 = fsteps[(idx+1)%len(fsteps)]
                        if s2 <= s1: s2 += L
                        exc = [word[k%L] for k in range(s1+1, s2)]
                        lf = sum(1 for p in exc if p == left_b)
                        rf = sum(1 for p in exc if p == right_b)
                        if lf == 0 or rf == 0:
                            found_one_sided = True
                            break
                    if found_one_sided: break

                if found_one_sided:
                    has_one_sided += 1

                # Check direct provider
                if check_provider_direct(word, ms, n):
                    has_provider += 1

                return

            last = word[-1]
            for nxt in [(last-1)%n, last, (last+1)%n]:
                word.append(nxt); gen(word); word.pop()

        for start in range(n):
            gen([start])

    print(f"n={n}, ms={ms}")
    print(f"Total valid walks: {total}")
    print(f"Has one-sided excursion from binary: {has_one_sided} ({has_one_sided/total*100:.1f}%)")
    print(f"Has binary provider: {has_provider} ({has_provider/total*100:.1f}%)")
    print(f"One-sided but no provider: {has_one_sided - has_provider}")
    print(f"Provider but no one-sided: {has_provider - has_one_sided}")


if __name__ == "__main__":
    main()
