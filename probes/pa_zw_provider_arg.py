"""
Try a direct argument based on the "last two b-fires" in the cycle.

Alternative cleaner approach: instead of worrying about which interval of i,
directly look at the mover sequence near a2 (the i-fire step).

The approach from ZeroWinding.lean: palindromic_step_pair_caseA constructs the EC
from the interval data. So we just need to PROVIDE the right interval.

Let me try yet another angle: the "q fires >= 3" hypothesis.

If some proc q fires >= 3 times, then CL >= 2n + 1 (since all fire >= 2 and
q fires >= 3, sum >= 2n + 1).

With CL >= 2n + 1 and >= 3 binary (each firing even >= 2),
total binary fires >= 6. Total ternary fires = CL - binary_fires.

Now, consider any binary proc b adjacent to another binary proc b'.
With >= 3 binary, does such an adjacent pair always exist?

Test: with 3 binary on ring of 9, positions 0,3,6 -> no adjacent pair.
So NO, adjacent binary pair doesn't always exist.

OK, different approach. Consider a ternary proc t adjacent to binary b.
(With >= 3 binary on ring of n >= 5, every ternary proc... no, that's also wrong.)

Actually, EVERY binary proc has two neighbors. We need the argument to work
for b itself as the center proc.

NEW APPROACH: Use b as center proc.
b is binary, fc(b) >= 2 (even). Let L = left(b), R = right(b).
Between consecutive fires of b, look for a step k2 where:
  L fires 0 or binary-even in [k2, a2)
  R fires 0 or binary-even in [k2, a2)
  mover[k2] != b

b has fc(b) >= 2 intervals. We need ONE good k2 in ONE interval.

Since b is binary, its fire count is even. If fc(b) = 2: one big interval and one small
(or two intervals). If fc(b) >= 4: >= 4 intervals.

In each interval, the mover excursion goes away from b and comes back.
The return step (a2-1) has mover adjacent to b: L or R.

If BOTH L and R are binary: then in any suffix, as long as both fire even, we win.
The last 2 steps before a2 have movers from {L, R}.
If both are the same (e.g., both L): L fires 2 (even), R fires 0. WIN.

If L and R are not both binary: one is binary (say L), other is ternary (R).
We need R fires 0 in the suffix.
Take the suffix after the last R-fire: R fires 0. L fires some amount.
Need L (binary) fires even.

If L fires 0: take the suffix after the last fire of L or R (whichever is later).
Then both fire 0. Need mover[k2] != b and some step exists. The step a2-1 has
mover = adjacent to b, so mover = L or R. If both L and R haven't fired... then
a2-1 can't be L or R?? Wait, a2-1 can be L or R regardless of whether they
fired in the interval. The mover AT step a2-1 fires (at proc mover[a2-1]),
which IS L or R.

OH WAIT. The mover at step a2-1 is L or R (by locality). So L or R FIRES at
step a2-1. This means in the suffix [a2-1, a2), at least one of L, R fires.

So "both fire 0" is impossible in ANY suffix containing a2-1.
We need a suffix [k2, a2) where at least a2-1 is included (since a2 is the fire of b).
So at least one of L, R fires at a2-1.

If mover[a2-1] = L (binary): L fires 1 (odd) in [a2-1, a2). R fires 0. Bad (L odd).
If mover[a2-1] = R (ternary): R fires 1 in [a2-1, a2). L fires 0. Bad (R odd, not binary).
  But L fires 0 (even!) and L is binary. R fires 1 but R is ternary: R_ok needs R=0. BAD.

If mover[a2-1] = R and R is binary: R fires 1 (odd). Bad.
If mover[a2-1] = L and L is ternary: can't help.

So k2 = a2-1 never works. What about k2 = a2-2?
mover[a2-2] adj to mover[a2-1]. If mover[a2-1] = L:
  mover[a2-2] in {LL, L, b}. Can't be b (between consec fires of b).
  So mover[a2-2] = L or LL.

  If mover[a2-2] = L: L fires 2 (even), R fires 0. L binary -> 2 even -> WIN!
  If mover[a2-2] = LL: L fires 1 (odd), R fires 0. Bad.

If mover[a2-1] = R:
  mover[a2-2] in {R, RR, b}. Can't be b.
  If mover[a2-2] = R: R fires 2. R binary -> even -> WIN! R ternary -> 2 != 0 -> BAD.
  If mover[a2-2] = RR: R fires 1. Bad.

So WIN happens when the last 2 movers before a2 are both the same binary neighbor.
This is the "double return" pattern.

The question: does some interval of b always have a double binary return?

Hmm, but there's also the possibility that going further back gives us the even count.
Like: L, LL, L (total L = 3 in [a2-3, a2)), or L, LL, LL, L (L=2 in [a2-4, a2)), etc.

Let me just think about whether using b as center always works.
"""
import random
from collections import Counter
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def test_binary_center(mover_word, moduli, n):
    """Use binary proc b as center. Check if EC mechanism works."""
    CL = len(mover_word)
    fc = [0] * n
    for m in mover_word: fc[m] += 1
    if not all(f >= 2 for f in fc): return None
    if not any(f >= 3 for f in fc): return None
    for p in range(n):
        if moduli[p] == 2 and fc[p] % 2 != 0: return None
    cw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == right(mover_word[k], n))
    ccw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == left(mover_word[k], n))
    if cw != ccw or cw == 0: return None
    for k in range(CL):
        if mover_word[(k+1)%CL] not in [mover_word[k], left(mover_word[k],n), right(mover_word[k],n)]:
            return None

    # Try each binary proc as center
    for b in range(n):
        if moduli[b] != 2: continue

        li = left(b, n)
        ri = right(b, n)
        fire_steps = [k for k in range(CL) if mover_word[k] == b]
        if len(fire_steps) < 2: continue

        for idx in range(len(fire_steps)):
            a1 = fire_steps[idx]
            a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
            if a2_raw <= a1: a2_raw += CL
            gap = list(range(a1 + 1, a2_raw))
            if not gap: continue

            li_count = 0
            ri_count = 0
            for k_raw in range(a2_raw - 1, a1, -1):
                k = k_raw % CL
                m = mover_word[k]
                if m == b: continue
                if m == li: li_count += 1
                if m == ri: ri_count += 1

                li_ok = (li_count == 0) or (moduli[li] == 2 and li_count % 2 == 0)
                ri_ok = (ri_count == 0) or (moduli[ri] == 2 and ri_count % 2 == 0)

                if li_ok and ri_ok and m != b:
                    return True

    return False


configs = [
    (5, [2,2,2,3,3]),
    (5, [2,2,2,2,3]),
    (7, [2,2,2,3,3,3,3]),
    (9, [2,2,2,3,3,3,3,3,3]),
    (9, [2,3,3,2,3,3,2,3,3]),
    (9, [2,3,2,3,2,3,3,3,3]),
    (9, [2,2,2,2,3,3,3,3,3]),
]

for n, moduli in configs:
    s, f = 0, 0
    for trial in range(300000):
        word = [random.randint(0, n-1)]
        for _ in range(random.randint(2*n+1, 5*n) - 1):
            curr = word[-1]
            word.append(random.choice([curr, left(curr, n), right(curr, n)]))
        r = test_binary_center(word, moduli, n)
        if r is None: continue
        if r: s += 1
        else: f += 1
    total = s + f
    print(f"n={n}, moduli={moduli}: Valid={total}, Pass={s}, Fail={f}")
