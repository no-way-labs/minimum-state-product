"""
Test by contradiction: what structure is forced when no EC exists?

If the mechanism fails for ALL (i, interval) pairs:
For every proc i with binary neighbor b, every interval of i,
scanning backward from a2:
  At every suffix endpoint k, either:
    - f-count > 0 (f has already fired, scanning backward)
    - b-count is odd (binary neighbor fires odd times)
    - mover[k] = i (not a valid k2)

This means: in the f-free suffix (from a2 backward until first f-fire),
b fires odd times at every step, and at the START of the suffix (just past
the f-free boundary), b-count is odd.

Wait, scanning backward:
At step a2-1 (first step backward):
  If mover = b: b-count=1 (odd), f-count=0. MECHANISM SAYS: need b even or f > 0. b odd -> bad.
  If mover = f: f-count=1 > 0. bad (f > 0).

So at the first backward step, either b-count=1 (odd, no EC) or f-count=1 (no EC).

At step a2-2:
  If first step was b (b-count=1):
    If mover[a2-2] = b: b-count=2 (even!), f-count=0. -> EC! This is the double-return.
    If mover[a2-2] = LL(i) (other): b-count=1, f-count=0. Still odd, no EC.
    If mover[a2-2] = f: b-count=1, f-count=1. No EC.

  If first step was f (f-count=1):
    If mover[a2-2] = f: f-count=2, b-count=0. b even -> need f=0, but f=2. No EC (f ternary).
      Wait: b-count=0 IS even! And f-count=2... f_ok needs f fires 0 or binary+even.
      If f is ternary: f-count=2 != 0 -> no good.
      If f is binary: f-count=2 even -> OK! EC!
    If mover[a2-2] = RR(i): f-count=1, b-count=0. b-count even, f-count > 0. No EC.
    If mover[a2-2] = b: f-count=1, b-count=1. Both bad.

So the ONLY way to avoid EC at depth 2 is:
  (a2-1=b, a2-2=LL or a2-2=f) or (a2-1=f, a2-2=RR or a2-2=b)
  Where LL and RR are non-{i,b,f} procs.

The constraint: every approach must NOT have a "double return" from binary side.

With fc(q) >= 3, q has >= 3 intervals. In each, the approach avoids double return.
The approach is always from L or R. If the approach from binary side is always
immediately preceded by a non-binary-side step (preventing double return),
then the structure is very constrained.

Let me count: across all intervals of ALL procs with binary neighbors,
does "no double return" ever force a contradiction with ZW or fc constraints?

Actually, let me try a different approach. The mechanism searches backward
from a2 past depth 2. It can go to any depth. At some depth, b-parity becomes even
while f hasn't fired yet. The question is just whether f fires before b-parity
returns to even.

For this to NEVER work:
In every interval, the FIRST thing that happens (scanning backward from a2)
is that f fires BEFORE b-parity returns to even.

That means: looking forward from a1+1 to a2:
The sequence of b-fires and f-fires is such that after the LAST f-fire,
b fires odd times before reaching a2.

Equivalently: going forward in the interval:
  Let L = last f-fire position in (a1, a2). If no f fires: L = a1.
  b fires some count c_b in (L, a2).
  c_b is odd.

So: in every interval of every proc with binary neighbor, the count of
binary-neighbor fires after the last far-neighbor fire is ODD.

Now, the total b-fires in the interval = (b-fires before last f) + c_b.
c_b is odd.

Over ALL intervals of proc i: sum of c_b's = sum of b-fires after last f in each interval.
The total b-fires across all intervals = fc(b).
But c_b might be less than total b-fires in each interval (some b-fires happen before f).

This doesn't directly give a contradiction.

Let me try to find the contradiction through CL and winding constraints.

Actually, I think the cleanest approach is:

LEMMA (Double Return Pigeonhole):
For proc i with binary left-neighbor b (moduli[b]=2), if fc(i) >= 3,
then some interval of i has the return from b (i.e., mover[a2-1] = b)
with mover[a2-2] = b (double return), giving EC.

Proof sketch:
q has fc >= 3, so >= 3 intervals.
In each interval, mover[a2-1] is L or R (adjacent to q by locality).
By pigeonhole, >= 2 intervals have the same approach side.

If >= 2 intervals have approach from binary side b:
  At the approach step, b fires. Just before: mover[a2-2] is adjacent to b.
  Possible values: L(b), b, R(b) = i. Can't be i (between consec fires of i).
  So mover[a2-2] = b or L(b).

  If for both intervals, mover[a2-2] = L(b): that constrains the path.

  Hmm, this doesn't immediately give double return.

Let me just test: is there an approach that works analytically?
"""
import random
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

# For the comprehensive approach, let me study the DEPTH at which the win occurs
n = 9
moduli = [2, 2, 2, 3, 3, 3, 3, 3, 3]

depth_stats = []
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

        # Find the MINIMUM depth (distance from a2) at which some (i, interval) wins
        min_depth = float('inf')
        for i in range(n):
            li = left(i, n)
            ri = right(i, n)
            if moduli[li] != 2 and moduli[ri] != 2: continue
            fire_steps = [k for k in range(CL) if word[k] == i]
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
                    m = word[k]
                    if m == i: continue
                    if m == li: li_count += 1
                    if m == ri: ri_count += 1

                    li_ok = (li_count == 0) or (moduli[li] == 2 and li_count % 2 == 0)
                    ri_ok = (ri_count == 0) or (moduli[ri] == 2 and ri_count % 2 == 0)

                    if li_ok and ri_ok and m != i:
                        depth = a2_raw - k_raw
                        min_depth = min(min_depth, depth)
                        break

        if min_depth < float('inf'):
            depth_stats.append(min_depth)

from collections import Counter
print(f"Cycles: {len(depth_stats)}")
print("Min depth distribution:")
print(Counter(depth_stats).most_common(20))
print(f"Max min-depth: {max(depth_stats) if depth_stats else 'N/A'}")
print(f"Depth=2 (double return): {sum(1 for d in depth_stats if d == 2)}/{len(depth_stats)}")
