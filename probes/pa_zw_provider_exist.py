"""
Test the existence argument:

Claim: Under ZW with cw>0, all fc>=2, >=3 binary, some fc>=3, n>=5,
for every ternary proc t adjacent to a binary proc b, consider the
consecutive fire intervals of t. The binary neighbor b fires some number
of times in each interval. We need to find an interval where:
  - b fires even times (possibly 0) in some suffix [k2, a2)
  - the other neighbor fires 0 times in [k2, a2)

Actually, the simpler claim to test first:

Does there ALWAYS exist a proc i (any type) with a consecutive fire pair
(a1, a2) such that a2 - a1 >= 3, and the step at a1+1 has mover != L(i)
and mover != R(i) (i.e., mover is "far"), and mover at a2-1 is L or R?

No, that's too specific. Let me think about this from the winning pattern.

The winning pattern is: in interval [k2, a2) before i's next fire at a2,
each neighbor either doesn't fire or is binary with even fires.

Key structural insight from the data:
1. ALL winners are ternary procs with at least one binary neighbor
2. The binary neighbor fires 0 or even times in the suffix interval
3. The other neighbor fires 0 times in the suffix interval

So the argument should be:
- Take any ternary proc t adjacent to binary proc b (exists since >=3 binary on ring)
- Consider consecutive fires of t
- In the interval between consecutive fires, b fires some number of times
- We need to find a suffix where b fires even and the far neighbor fires 0

Actually, let me test a much simpler version:

Claim: There exists a proc i with consecutive fire pair where, taking
k2 = the step right after the LAST firing of right(i) (or left(i))
in the interval, the remaining suffix has the right properties.

Let me just test: for which proc i does the argument work with the
MINIMAL interval (just the last 2 steps before a2)?
"""
import random
from collections import Counter
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def test_binary_excursion(mover_word, moduli, n):
    """
    Test: for a ternary proc t adjacent to binary b, look at consecutive
    fires of t. In the interval (a1, a2), find a non-mover step k2 where
    the suffix [k2, a2) has b firing even times and far neighbor firing 0.

    The "excursion" idea: between consecutive fires of t, the mover walks
    away from t and comes back. The walk must return through a neighbor.
    If it returns through binary b, then the suffix from the last entry
    of the walk through the "far side" gives the right property.
    """
    CL = len(mover_word)
    fc = [0] * n
    for m in mover_word:
        fc[m] += 1

    if not all(f >= 2 for f in fc): return None
    if not any(f >= 3 for f in fc): return None

    cw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == right(mover_word[k], n))
    ccw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == left(mover_word[k], n))
    if cw != ccw or cw == 0: return None

    for k in range(CL):
        m_curr = mover_word[k]
        m_next = mover_word[(k+1) % CL]
        if m_next != m_curr and m_next != left(m_curr, n) and m_next != right(m_curr, n):
            return None

    # Find all ternary procs adjacent to binary procs
    ternary_with_bin_nbr = []
    for t in range(n):
        if moduli[t] != 3: continue  # ternary only  (actually, mod >= 3)
        if moduli[left(t, n)] == 2 or moduli[right(t, n)] == 2:
            ternary_with_bin_nbr.append(t)

    if not ternary_with_bin_nbr:
        return None  # shouldn't happen with >= 3 binary

    for t in ternary_with_bin_nbr:
        fire_steps = [k for k in range(CL) if mover_word[k] == t]
        if len(fire_steps) < 2: continue

        li = left(t, n)
        ri = right(t, n)
        bin_side = 'L' if moduli[li] == 2 else 'R'
        b = li if bin_side == 'L' else ri
        far = ri if bin_side == 'L' else li

        for idx in range(len(fire_steps)):
            a1 = fire_steps[idx]
            a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
            if a2_raw <= a1: a2_raw += CL

            gap = list(range(a1 + 1, a2_raw))
            if not gap: continue

            # Find the last step in the gap where the far neighbor fires
            last_far_fire = -1
            for k_raw in gap:
                k = k_raw % CL
                if mover_word[k] == far:
                    last_far_fire = k_raw

            # k2 = last_far_fire + 1 (right after far's last fire)
            # If far never fires: k2 = a1 + 1
            if last_far_fire == -1:
                k2_raw = a1 + 1
            else:
                k2_raw = last_far_fire + 1

            if k2_raw >= a2_raw: continue
            k2 = k2_raw % CL
            if mover_word[k2] == t: continue

            interval = [s % CL for s in range(k2_raw, a2_raw)]
            b_fires = sum(1 for k in interval if mover_word[k] == b)
            far_fires = sum(1 for k in interval if mover_word[k] == far)

            assert far_fires == 0, f"far_fires={far_fires}, should be 0 by construction"

            b_ok = (b_fires == 0) or (b_fires % 2 == 0)  # b is binary
            far_ok = True  # far_fires == 0

            if b_ok:
                return (True, f"t={t}, bin_side={bin_side}, b_fires={b_fires}")

    return (False, "no ternary-with-binary-neighbor works")

# Test
configs = [
    (5, [2,2,2,3,3]),
    (7, [2,2,2,3,3,3,3]),
    (9, [2,2,2,3,3,3,3,3,3]),
    (9, [2,3,3,2,3,3,2,3,3]),
    (9, [2,3,2,3,2,3,3,3,3]),
    (11, [2,2,2,3,3,3,3,3,3,3,3]),
]

for n, moduli, in configs:
    print(f"\nn={n}, moduli={moduli}")
    success = 0
    fail = 0
    skip = 0
    fail_details = []

    for trial in range(200000):
        word = [random.randint(0, n-1)]
        for _ in range(random.randint(2*n+1, 4*n) - 1):
            curr = word[-1]
            word.append(random.choice([curr, left(curr, n), right(curr, n)]))

        result = test_binary_excursion(word, moduli, n)
        if result is None:
            skip += 1
        elif result[0]:
            success += 1
        else:
            fail += 1
            if len(fail_details) < 3:
                fail_details.append(result[1])

    total = success + fail
    print(f"Valid: {total}, Success: {success}, Fail: {fail}")
    if fail > 0:
        print(f"Failures: {fail_details}")
