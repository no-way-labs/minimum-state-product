"""
Locality-based proof of the Clustering Lemma.

KEY INSIGHT: Between consecutive fires of binary b, the walk STARTS at a
neighbor of b and ENDS at a neighbor of b. Call the start-neighbor the
"departure side" and end-neighbor the "approach side".

For b with fc(b) = 2: two intervals.
Departures: (d1, d2) each in {L, R}
Approaches: (a1, a2) each in {L, R}

Interval 1 goes from d1 to a1. Interval 2 goes from d2 to a2.
(Cyclically: departure 1 starts interval 1, approach 1 ends it;
departure 2 starts interval 2, approach 2 ends it.)

If d1 = a1 = L and d2 = a2 = R:
Interval 1 is L-to-L, interval 2 is R-to-R.
L fires at first step of int1 AND last step of int1.
R fires at first step of int2 AND last step of int2.

In interval 1: L fires >= 2, R fires... depends on walk.
For R to fire in interval 1, walk must reach R side.
By locality, walk starts at L, can only go left (away from b) or back to b.
Walk goes L -> LL -> ... etc. To reach R, must go all the way around.
Interval length must be >= n-1 for this.

If interval 1 has length < n-1: R fires 0 in interval 1!
Then: between b-fires s1 and s2, i = R fires 0. -> Clustering lemma holds!

If BOTH intervals have length >= n-1:
CL = L1 + L2 >= 2(n-1) = 2n-2. Fine for CL > 2n.

But: with 3 binary procs, we have 3 binary with 2 fires each = 6 interval pairs.
For the clustering lemma to FAIL for ALL 3 binary:
Each must have both intervals of length >= n-1.

Total interval length for all 3 binary: sum of 6 intervals = CL * 3
(each step is in one interval of each binary). Wait, no: each step is in
the interval of the binary proc whose consecutive fires bracket it.

Actually, each step belongs to exactly one interval of each binary proc.
But the intervals of different binary procs overlap.

Hmm this is complicated. Let me test: with 3 binary, do we always have
some binary with a short interval (< n-1)?
"""
import random
from collections import Counter
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

n = 9
moduli = [2, 2, 2, 3, 3, 3, 3, 3, 3]

min_interval_stats = []
total = 0

for trial in range(2000000):
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

        # For each binary b, find minimum interval length
        global_min = CL
        for b in range(n):
            if moduli[b] != 2: continue
            fire_steps = [k for k in range(CL) if word[k] == b]
            for idx in range(len(fire_steps)):
                s1 = fire_steps[idx]
                s2 = fire_steps[(idx + 1) % len(fire_steps)]
                if s2 <= s1: s2 += CL
                intv_len = s2 - s1 - 1  # steps in interval (excluding fire steps)
                global_min = min(global_min, intv_len)

        min_interval_stats.append(global_min)

print(f"Total valid: {total}")
print(f"\nGlobal min interval length across all binary:")
print(Counter(min_interval_stats).most_common(20))
print(f"\nMin interval < n-1={n-1}: {sum(1 for m in min_interval_stats if m < n-1)}/{total}")
print(f"Min interval < n: {sum(1 for m in min_interval_stats if m < n)}/{total}")

# If min < n-1, the "short interval" argument works directly
# because the walk can't reach the far side in that interval.
# So the far-side neighbor fires 0 -> clustering lemma.
