"""
Walk-based argument for Part 1.

The mover sequence is a walk on the ring (by locality). Consecutive movers
are adjacent or equal. This walk visits every proc >= 2 times.

Consider a binary proc b. b is visited (fired) >= 2 times.
After b fires, the mover goes to left(b) or right(b) or stays at b.
Before b fires, the mover was at left(b), right(b), or b.

KEY OBSERVATION: The last step before b fires at a2 is a2-1, with
mover[a2-1] adjacent to b. After b fires at a2, mover[a2+1] adjacent to b.

So the "excursion" between consecutive fires of b looks like:
  b fires at a1 -> mover goes to nbr -> excursion -> mover at nbr -> b fires at a2

The excursion is a walk starting from a neighbor of b and ending at a neighbor of b,
with b not visited in between.

Now: in the excursion, does some neighbor of b get fired twice?

Claim: The excursion has length >= 2 * (n-1) - 1 (since b has fc(b) >= 2 intervals
and CL > 2n, each interval is at least... no, that's not right).

Actually: CL > 2n. b fires fc(b) >= 2 times, creating fc(b) intervals.
Average interval length = CL / fc(b) >= 2n / fc(b).
If fc(b) = 2: average = n. At least one interval has length >= n.

In an interval of length >= n: the mover visits >= n steps (all non-b).
On a ring of n procs, that's enough to visit every proc at least once.
But actually, the mover can stay in place (fire same proc twice).

Hmm, but we know every proc fires >= 2 total, not >= 1 per interval.

Let me think differently.

APPROACH: Use the fact that fc(q) >= 3 for some q.

Take any binary proc b adjacent to q.
(If q is binary, b = q. If q is not binary, maybe its neighbor is binary.)

Actually, first: does q always have a binary neighbor?

With >= 3 binary procs on ring of n >= 9:
If binary procs are at positions B = {b1, b2, b3, ...}, the non-binary procs
form arcs between consecutive binary procs.

q has fc >= 3. q might be binary or not.
If q is binary: q itself has fc >= 3, fc even so fc >= 4.
  q has two neighbors. One might be binary.
  But we don't need adjacent binary -- we need q to be the center proc.

If q is not binary: q is in some arc between two binary procs.
  If the arc has length d (d non-binary procs in a row), q is at most
  floor(d/2) away from a binary proc.
  With 3 binary on 9-ring, arcs have length 2. So q is at most 1 away from binary.
  That means q's neighbor IS binary.

For the general case: with B binary procs, there are B arcs of non-binary procs.
Total non-binary = n - B. Average arc length = (n - B) / B.
With B >= 3 and n >= 9: average = (n-3)/3 <= (n-3)/3.
Max arc length can be up to n - B.

But we don't need EVERY proc to be adjacent to binary. We need at least ONE
proc with fc >= 3 to be adjacent to binary, OR we need the argument to work
through a chain of procs.

Actually, wait. The mechanism doesn't require q to be the center proc.
The center proc can be ANY proc with binary neighbor. We just need fc >= 3
to ensure CL > 2n.

Let me reconsider. The EXISTENCE of some q with fc >= 3 gives CL > 2n.
Then we need some proc i (possibly different from q) with:
  - binary neighbor b
  - some interval of i where b fires >= 2

The key insight: b fires fc(b) >= 2 times. These fires happen in the
excursions between b's own fires. Wait, b fires in its OWN intervals too.
Let me think about neighbor i's perspective.

Take i = right(b). i fires fc(i) >= 2 times.
Between consecutive fires of i, b fires some number of times.
Sum across all intervals = fc(b) >= 2.

We need SOME interval with >= 2.

If fc(i) = 2: two intervals, b fires total fc(b) >= 2.
  Distribution (a, fc(b)-a) with a + (fc(b)-a) = fc(b).
  Some interval has >= ceil(fc(b)/2) >= 1. Need >= 2.
  Happens when fc(b) >= 3, or when distribution is (2, fc(b)-2), etc.
  If fc(b) = 2: distribution is (2,0) or (1,1).
    If (1,1): max = 1. FAIL for this (i, b) pair.

If fc(i) >= 3: intervals >= 3. fc(b) >= 2.
  Average = fc(b)/fc(i). Can be < 1 if fc(b) < fc(i).
  All intervals could have 0 or 1. FAIL.

So for a SPECIFIC (i, b), it can fail.
We need SOME pair to work.

CRUCIAL TEST: When (right(b), b) fails (max = 1), does (left(b), b) succeed?
"""
import random
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def test_both_sides(mover_word, moduli, n):
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

    # For each binary b, check max b-fires in intervals of right(b) and left(b)
    results = {}
    for b in range(n):
        if moduli[b] != 2: continue

        for side_name, i in [('right', right(b, n)), ('left', left(b, n))]:
            fire_steps_i = [k for k in range(CL) if mover_word[k] == i]
            if len(fire_steps_i) < 2: continue

            max_b = 0
            for idx in range(len(fire_steps_i)):
                a1 = fire_steps_i[idx]
                a2_raw = fire_steps_i[(idx + 1) % len(fire_steps_i)]
                if a2_raw <= a1: a2_raw += CL
                gap = list(range(a1+1, a2_raw))
                b_in = sum(1 for k in gap if mover_word[k % CL] == b)
                max_b = max(max_b, b_in)

            results[(b, side_name)] = max_b

    # Check: for each binary b, does at least one side have max >= 2?
    for b in range(n):
        if moduli[b] != 2: continue
        r_max = results.get((b, 'right'), 0)
        l_max = results.get((b, 'left'), 0)
        if max(r_max, l_max) >= 2:
            continue
        # Both sides have max <= 1 for this b
        return (False, b, r_max, l_max, fc)

    return (True,)

n = 5
moduli = [2, 2, 2, 3, 3]
s, f = 0, 0
for trial in range(500000):
    word = [random.randint(0, n-1)]
    for _ in range(random.randint(2*n+1, 5*n) - 1):
        curr = word[-1]
        word.append(random.choice([curr, left(curr, n), right(curr, n)]))
    r = test_both_sides(word, moduli, n)
    if r is None: continue
    if r[0]: s += 1
    else:
        f += 1
        if f <= 5:
            print(f"FAIL: b={r[1]}, right_max={r[2]}, left_max={r[3]}, fc={r[4]}")
print(f"n=5: Valid={s+f}, Pass={s}, Fail={f}")

n = 9
moduli = [2, 2, 2, 3, 3, 3, 3, 3, 3]
s, f = 0, 0
for trial in range(500000):
    word = [random.randint(0, n-1)]
    for _ in range(random.randint(2*n+1, 5*n) - 1):
        curr = word[-1]
        word.append(random.choice([curr, left(curr, n), right(curr, n)]))
    r = test_both_sides(word, moduli, n)
    if r is None: continue
    if r[0]: s += 1
    else:
        f += 1
        if f <= 5:
            print(f"FAIL: b={r[1]}, right_max={r[2]}, left_max={r[3]}, fc={r[4]}")
print(f"n=9: Valid={s+f}, Pass={s}, Fail={f}")
