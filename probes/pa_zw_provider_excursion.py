"""
The excursion argument:

Consider binary proc b. It fires fc(b) >= 2 (even) times.
Between consecutive fires of b, the mover makes an "excursion" away from b.
By locality, the excursion starts at a neighbor of b and ends at a neighbor of b.

In the excursion, proc i = right(b) might fire.

Let's think about it from i's perspective:
- i has left neighbor b (binary)
- Between consecutive fires of i at (a1, a2):
  - b fires some number of times F_b
  - The mover makes an excursion from i's neighborhood, goes around, returns

For the EC mechanism, we need k2 in (a1, a2) where in [k2, a2):
  - b fires even times
  - far(i) = right(i) fires 0 times

The simplest case: the "return" to i comes from the b-side.
The mover at a2-1 = b (the step before i fires).
If the mover at a2-2 is also b: b fires 2 times in [a2-2, a2), far fires 0. WIN.

If the mover at a2-2 is NOT b: it's left(b) = LL(i) or b itself.
Actually mover[a2-2] adj to mover[a2-1] = b. So mover[a2-2] in {left(b), b, right(b)}.
right(b) = i, but i doesn't fire. left(b) = LL(i).
So mover[a2-2] = b or LL(i).

If mover[a2-2] = LL(i): we have b-count=1 in [a2-2, a2), not even.
  Continue back: mover[a2-3] adj to LL(i), could be LLL(i) or LL(i) or b.
  If mover[a2-3] = b: b-count=2 in [a2-3, a2), but far might have fired at LL(i).
  Wait, LL(i) is neither b nor far(i)=R(i) (for n>=5). So far fires 0 still!
  b fires 2 in [a2-3, a2). WIN! (assuming mover[a2-3] != i, which is true)

  If mover[a2-3] = LL(i): b-count still 1.
  If mover[a2-3] = LLL(i): still 1.
  The excursion goes further left...

The point: eventually the mover must come back through b to reach i.
As long as f(=R(i)) hasn't fired, when b fires the second time, we win.

But the mover could reach i from the RIGHT (far) side!
Then it passes through f before reaching i, and f-count > 0.

So the question: does the excursion always return from the b side?
Answer: NO, not for every interval. But across ALL intervals of i...

Actually, let me think about it differently.

The TOTAL fires of b in the cycle = fc(b) >= 2 (even).
Distribute these across the fc(i) consecutive fire intervals of i.
In some interval, b fires 0 times. In others, b fires > 0.

For an interval where b fires 0: then b-count stays 0 throughout.
We need f-count = 0 at some k2. Take k2 = a1+1 (the first step after a1).
Then [a1+1, a2) has b-fires=0, f-fires = total f fires in interval.
If f fires 0 in this interval too: both neighbors fire 0. WIN trivially.
If f fires > 0: no good. BUT f is non-binary, so f-fires != 0 means no help.

Wait, but if b-fires = 0 in the whole interval, then in any suffix,
b-fires = 0. We just need f-fires = 0 in SOME suffix.
The smallest suffix with f-fires=0 is [last_f_fire + 1, a2).
In that suffix, b fires 0 (since b fires 0 in the whole interval).
And f fires 0. And there must be at least one step in this suffix
(since a2-1 must be adjacent to i, and if it's not f, it could be b or other).

Hmm wait, if b fires 0 in the interval and the approach at a2-1 is from b:
that's a CONTRADICTION. Approach from b means b fires at a2-1.

If b fires 0 in the interval: the approach must be from f side or a "stay".
Actually approach at a2-1: mover[a2-1] adj to mover[a2] = i.
So mover[a2-1] in {L(i), R(i), i} \ {i} = {b, f} (since i doesn't fire in interval).

If b fires 0: mover[a2-1] = f. So f fires at a2-1.
The suffix [a2-1, a2) has f=1 (bad).
Need to go further back. [k, a2-1) for some k < a2-1 where mover[k] != f, != b.
If such k exists with mover[k] != i: then [k, a2) has f=1 (from a2-1), b=0.
f=1 odd, f not binary -> BAD.

Hmm. So when b fires 0, the approach from f is forced, and f fires at least once,
making the suffix have f > 0. This seems like a problem.

Unless we go to a suffix [k2, a2-1) (not including the f-fire at a2-1).
But then the suffix must end at a2 (the fire of i), and we compare config at k2 vs a2.
Wait no, the EC mechanism requires: step k2 where i is non-mover, and the config at
k2 matches config at a2 (where i IS mover). The matching is of (L, S, R) at proc i.

The config at k2 must match config at a2. The config at a2 is determined by
what's been going on before a2. So we need:
  configAt(k2, b) = configAt(a2, b)  [left of i]
  configAt(k2, i) = configAt(a2, i)  [self]
  configAt(k2, f) = configAt(a2, f)  [right of i]

Since i doesn't fire in (a1, a2), configAt(a2, i) = configAt(a1+1, i) = fixed.
And configAt(k2, i) = same (k2 in (a1, a2)).

For b: configAt(k2, b) = configAt(a2, b) iff b fires even times in [k2, a2).
For f: configAt(k2, f) = configAt(a2, f) iff f fires 0 times (or f binary+even) in [k2, a2).

So we need [k2, a2) not (a1, a2). The step a2-1 IS included.

Let me reconsider the b-fires-0 case:
- mover[a2-1] = f (forced)
- suffix [a2-1, a2): f=1, b=0. f not binary -> BAD.
- suffix [a2-2, a2): f includes a2-1's fire. If mover[a2-2] != f:
  f still 1. b still 0. BAD.
  If mover[a2-2] = f: f=2. Still bad (not binary, 2 != 0).

So in the b-fires-0 case, f fires at least once just before a2, making it
impossible to have a suffix with f=0 AND b=0.

THIS MEANS: we need b to fire >= 2 times in the interval, to make b-count = 2
at some suffix point where f-count is still 0.

So the argument needs: b fires >= 2 in some consecutive fire interval of i.

Since b fires fc(b) >= 2 total across all intervals, and fc(i) >= 2 intervals exist,
b could fire 2 in one interval and 0 in all others. That's fine for us.

But could b fire 1 in two intervals and 0 in the rest? Then no interval has b >= 2.
BUT: b is binary, so fc(b) is EVEN. If b fires across k intervals, the total is even.
Each interval contributes some amount. But individual contributions can be odd.

Actually wait - I need to think about this differently.

Let me just verify: does there always exist an interval of i where b fires >= 2?
"""
import random
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

n = 9
moduli = [2, 2, 2, 3, 3, 3, 3, 3, 3]

found_ge2 = 0
no_ge2 = 0
total = 0

for trial in range(500000):
    word = [random.randint(0, n-1)]
    for _ in range(random.randint(2*n+1, 5*n) - 1):
        curr = word[-1]
        word.append(random.choice([curr, left(curr, n), right(curr, n)]))

    CL = len(word)
    fc = [0] * n
    for m in word: fc[m] += 1
    if not all(f >= 2 for f in fc): continue
    if not any(f >= 3 for f in fc): continue
    for p in range(n):
        if moduli[p] == 2 and fc[p] % 2 != 0: break
    else:
        cw = sum(1 for k in range(CL) if word[(k+1) % CL] == right(word[k], n))
        ccw = sum(1 for k in range(CL) if word[(k+1) % CL] == left(word[k], n))
        if cw != ccw or cw == 0: continue
        ok = True
        for k in range(CL):
            m_curr = word[k]
            m_next = word[(k+1) % CL]
            if m_next != m_curr and m_next != left(m_curr, n) and m_next != right(m_curr, n):
                ok = False; break
        if not ok: continue
        total += 1

        # For each proc with binary neighbor, check if some interval has b >= 2
        any_proc_works = False
        for i in range(n):
            li = left(i, n)
            ri = right(i, n)
            if moduli[li] != 2 and moduli[ri] != 2: continue

            b = li if moduli[li] == 2 else ri

            fire_steps = [k for k in range(CL) if word[k] == i]
            if len(fire_steps) < 2: continue

            for idx in range(len(fire_steps)):
                a1 = fire_steps[idx]
                a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
                if a2_raw <= a1: a2_raw += CL

                b_fires_in_interval = sum(1 for k_raw in range(a1+1, a2_raw)
                                          if word[k_raw % CL] == b)
                if b_fires_in_interval >= 2:
                    any_proc_works = True
                    break
            if any_proc_works: break

        if any_proc_works:
            found_ge2 += 1
        else:
            no_ge2 += 1
            if no_ge2 <= 3:
                print(f"NO interval with b>=2: fc={fc}, word={word}")

print(f"\nTotal: {total}, b>=2 exists: {found_ge2}, never b>=2: {no_ge2}")
