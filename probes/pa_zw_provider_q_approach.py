"""
Q-BASED APPROACH:

Let q be a proc with fc(q) >= 3. q fires >= 3 times.
q has >= 3 consecutive-fire intervals.

In each interval, by locality, the mover enters from a neighbor of q
and exits to a neighbor of q. So left(q) or right(q) fires at the
boundary steps.

Specifically: at step a2 (q fires), the previous step a2-1 has mover
adjacent to q: left(q) or right(q).

So left(q) fires at a2-1 OR right(q) fires at a2-1.

Across fc(q) >= 3 intervals, by pigeonhole, at least 2 intervals have
the SAME approach side (say left(q) approaches at a2-1 in >= 2 intervals).

Now here's the idea: the approach side proc fires at those steps.
If the approach proc is binary, then between two intervals where it approaches,
it fires at least 2 times -> and they might be in the SAME interval of some
other proc.

Actually, let me try yet another angle.

DIRECT Q-APPROACH:
Use q itself as the center proc for EC.
q has >= 3 intervals. In each interval, at least one of L(q), R(q) fires
(at the last step of the interval, by locality).

Key claim: in some interval of q, some neighbor fires >= 2 times,
and the conditions for EC are met.

Let me test: using q as center proc for EC mechanism.
"""
import random
from collections import Counter
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def test_q_center(mover_word, moduli, n):
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

    # Find q with fc >= 3
    for q in range(n):
        if fc[q] < 3: continue

        li = left(q, n)
        ri = right(q, n)

        # Check: does q have a binary neighbor?
        if moduli[li] != 2 and moduli[ri] != 2:
            continue

        fire_steps = [k for k in range(CL) if mover_word[k] == q]

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
                if m == q: continue
                if m == li: li_count += 1
                if m == ri: ri_count += 1

                li_ok = (li_count == 0) or (moduli[li] == 2 and li_count % 2 == 0)
                ri_ok = (ri_count == 0) or (moduli[ri] == 2 and ri_count % 2 == 0)

                if li_ok and ri_ok and m != q:
                    return (True, q, idx)

    return (False,)


configs = [
    (5, [2,2,2,3,3]),
    (7, [2,2,2,3,3,3,3]),
    (9, [2,2,2,3,3,3,3,3,3]),
    (9, [2,3,3,2,3,3,2,3,3]),
    (9, [2,3,2,3,2,3,3,3,3]),
]

for n, moduli in configs:
    s, f = 0, 0
    for trial in range(300000):
        word = [random.randint(0, n-1)]
        for _ in range(random.randint(2*n+1, 5*n) - 1):
            curr = word[-1]
            word.append(random.choice([curr, left(curr, n), right(curr, n)]))
        r = test_q_center(word, moduli, n)
        if r is None: continue
        if r[0]: s += 1
        else: f += 1
    print(f"n={n}, moduli={moduli}: Valid={s+f}, Pass={s}, Fail={f}")
