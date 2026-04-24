"""
Analytical argument verification.

PART 1: Existence of interval with b >= 2 fires.

Setup: ring of n >= 5 procs, >= 3 binary, CL > 2n (since some fc >= 3, all fc >= 2).
Take any binary proc b. fc(b) >= 2 (even).
Let i = right(b) (i is adjacent to b).

Claim: In some consecutive fire interval of i, b fires >= 2 times.

Proof attempt:
  b fires fc(b) >= 2 times total. These fires are distributed across fc(i) intervals of i.
  By pigeonhole, some interval gets >= ceil(fc(b)/fc(i)) fires.
  We need ceil(fc(b)/fc(i)) >= 2, i.e., fc(b) > fc(i).

  But fc(b) might be 2 and fc(i) might be 10. Then average = 0.2, no interval gets 2.

  Actually wait - this pigeonhole argument is wrong. b could fire twice, both in the
  same interval. That gives one interval with 2. OR b fires once in each of two intervals.
  Since fc(b) >= 2, either some interval has >= 2 b-fires, or at least 2 intervals each
  have exactly 1.

  But we NEED some interval with >= 2 b-fires. If b fires exactly 1 in each of two
  intervals, no interval has >= 2. This is a problem!

  HOWEVER: in the fc-exactly-1 case, we need a different argument.

Actually, let me re-examine. When b fires 1 time in some interval of i,
we can't get even b-count > 0. But we CAN get b-count = 0 if we take the
suffix AFTER that b-fire.

Hmm, but b-count = 0 doesn't help because f fires just before a2.

Wait - let me reconsider the problem. We're not restricted to one specific i.
We can choose ANY proc with a binary neighbor. There are many such procs.

Let me reconsider: maybe the argument works by choosing WHICH proc to use.

Key insight: try i = b itself (a binary proc).
Both neighbors of b could be non-binary. But if b has a binary neighbor b',
then between consecutive fires of b, b' fires some times.
Actually, the winning proc doesn't have to be adjacent to b.
The winning proc just needs SOME binary neighbor.

With >= 3 binary procs on the ring:
- Some pair of binary procs are adjacent (by pigeonhole if >= ceil(n/2) binary,
  but not necessarily for 3 binary on 9-ring).
  Actually for 3 binary on 9-ring with no two adjacent (like 0,3,6), no binary pair is adjacent.
  But each binary has non-binary neighbors.

Let me reconsider the approach entirely.
For the case where b = left(i) fires exactly 1 time in EVERY interval of i,
but the approach works anyway through a different mechanism...

Actually, let me check: does the case where b fires exactly 1 in each interval actually occur?
"""
import random
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

n = 5
moduli = [2, 2, 2, 3, 3]

max_b_in_interval_stats = []

for trial in range(300000):
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

        # For each proc i with binary neighbor b, find max b-fires in any interval
        for i in range(n):
            li = left(i, n)
            ri = right(i, n)
            for b in [li, ri]:
                if moduli[b] != 2: continue
                fire_steps = [k for k in range(CL) if word[k] == i]
                if len(fire_steps) < 2: continue

                max_b = 0
                for idx in range(len(fire_steps)):
                    a1 = fire_steps[idx]
                    a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
                    if a2_raw <= a1: a2_raw += CL
                    gap = list(range(a1+1, a2_raw))
                    b_in = sum(1 for k in gap if word[k % CL] == b)
                    max_b = max(max_b, b_in)

                max_b_in_interval_stats.append((max_b, fc[b], fc[i]))

from collections import Counter
print(f"Total (i, b) pairs analyzed: {len(max_b_in_interval_stats)}")
print("\n--- Max b-fires in any interval of i ---")
print(Counter(mb for mb, _, _ in max_b_in_interval_stats).most_common(20))

# Cases where max_b = 1 (b fires at most 1 in every interval)
max1 = [(mb, fb, fi) for mb, fb, fi in max_b_in_interval_stats if mb <= 1]
print(f"\nmax_b <= 1: {len(max1)}/{len(max_b_in_interval_stats)}")
print("fc(b), fc(i) for these:")
print(Counter((fb, fi) for _, fb, fi in max1).most_common(20))

# For max_b = 0 cases
max0 = [(mb, fb, fi) for mb, fb, fi in max_b_in_interval_stats if mb == 0]
print(f"\nmax_b = 0: {len(max0)}")
