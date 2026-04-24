"""
Analytical proof construction for Part 1 and Part 2.

PART 1: WHY does SOME (i, b) pair have an interval with b >= 2?

Consider binary proc b. b fires fc(b) >= 2 times at steps s_1, s_2, ..., s_{fc(b)}.
Let i = right(b). Consider i's consecutive fire intervals.

Between consecutive fires of i, b fires some number of times.
The total across all intervals = fc(b) >= 2.

If EVERY interval of i has b-fires <= 1, then total b-fires <= fc(i)
(since each of fc(i) intervals contributes at most 1).
So fc(b) <= fc(i).

Similarly for j = left(b): if every interval of j has b-fires <= 1,
then fc(b) <= fc(j).

So if the claim fails for BOTH i and j: fc(b) <= fc(i) AND fc(b) <= fc(j).
Both neighbors have fc >= fc(b) >= 2.

Now do this for ALL binary procs. If the claim fails for all (proc, binary_nbr) pairs:
For each binary b: fc(right(b)) >= fc(b) and fc(left(b)) >= fc(b).

Sum over all binary procs:
sum_b fc(left(b)) + sum_b fc(right(b)) >= 2 * sum_b fc(b)

But the left/right neighbors of binary procs might overlap (two adjacent binary procs
share a neighbor). This is getting complicated.

Let me try a simpler approach:

CLAIM: With n >= 5, >= 3 binary, all fc >= 2, some fc >= 3,
binary procs fire even >= 2, total CL >= 2n+1:

Total binary fires = sum over binary b of fc(b) >= 3 * 2 = 6
(at least 3 binary, each fires >= 2).

Each binary fire is "adjacent" to the interval of its neighbors.
By next_mover_is_local, when b fires, the previous and next movers
are adjacent to b.

Actually, here's a key insight: between consecutive fires of b,
the mover must make an EXCURSION that goes from a neighbor of b,
around some part of the ring, and returns to a neighbor of b.

If b has a binary neighbor b', then between consecutive fires of b,
b' fires some times. The key: b' fires >= 2 at some point?

Let me try a COMPLETELY different analytical approach.

APPROACH: Use the fc >= 3 proc directly.

Let q be the proc with fc >= 3. Take i = q (use q as center).
q fires >= 3 times. Between consecutive fires of q, look at q's neighbors.

q has two neighbors: L = left(q), R = right(q).
One of them might be binary.

Case A: At least one neighbor of q is binary (say L = left(q) is binary).
  Between consecutive fires of q, L fires some amount.
  q has >= 3 intervals (one for each pair of consecutive fires).
  L fires fc(L) >= 2 total across all intervals.

  If all intervals have L-fires <= 1: total <= fc(q) >= 3.
  fc(L) >= 2 <= 3 = fc(q). So this is possible.

  BUT: q has >= 3 intervals. L fires >= 2 total. By pigeonhole:
  If all have <= 1: total <= number of intervals with >= 1 <= fc(q).
  This is fine. But we need SOME interval with >= 2.

  Alternative: look at WHICH intervals get L-fires.
  L fires in at most fc(L) of the fc(q) intervals.
  But we can't guarantee >= 2 in one interval from this alone.

  HOWEVER: consider L's fire steps. Between consecutive L-fires (L is binary, fc(L) even >= 2),
  q fires some times. Let's count:

  L fires fc(L) times. Between consecutive L-fires, q fires some amount.
  Total q-fires across L's intervals = fc(q) >= 3.
  L has fc(L) >= 2 intervals (since fc(L) >= 2).

  In some interval of L, q fires >= ceil(fc(q)/fc(L)) times.
  If fc(q) >= 3 and fc(L) = 2: ceil(3/2) = 2. So some L-interval has q firing >= 2.

  That means between two consecutive L-fires, q fires >= 2 times.
  The first q-fire in that L-interval: at that q-fire step, consider the interval
  from L's fire to q's fire. In [L_fire, q_first_fire): L fires 1 (at L_fire), q fires 0.

  Wait, this is getting twisted. Let me take a step back and test
  whether the fc>=3 proc always has a binary neighbor.
"""
import random
from collections import Counter
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

n = 9
moduli = [2, 3, 3, 2, 3, 3, 2, 3, 3]  # binary at 0, 3, 6

has_bin_nbr = 0
no_bin_nbr = 0
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
            if word[(k+1)%CL] not in [word[k], left(word[k],n), right(word[k],n)]:
                ok = False; break
        if not ok: continue
        total += 1

        # Find all q with fc >= 3
        q_procs = [p for p in range(n) if fc[p] >= 3]

        # Does SOME q have a binary neighbor?
        any_q_bin_nbr = any(
            moduli[left(q, n)] == 2 or moduli[right(q, n)] == 2
            for q in q_procs
        )

        if any_q_bin_nbr:
            has_bin_nbr += 1
        else:
            no_bin_nbr += 1
            if no_bin_nbr <= 3:
                print(f"NO q with binary nbr: q={q_procs}, fc={fc}")

print(f"\nTotal: {total}, q has bin nbr: {has_bin_nbr}, no: {no_bin_nbr}")
