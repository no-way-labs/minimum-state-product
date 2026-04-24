"""
Correct approach: consider ALL procs with at least one binary neighbor.
For such proc i with binary neighbor b on one side and far neighbor f on the other:
- Between consecutive fires of i, find a suffix [k2, a2) where:
  - b fires even times (0, 2, 4, ...)  [binary even -> preserved]
  - f fires 0 times [silence -> preserved]
  - OR f is also binary and fires even times

The strategy: scan backward from a2. Every time b fires, it toggles parity.
After an even number of b-fires from a2, we have even parity.
We need f to have fired 0 times since the last even-parity point of b.

Simplification: take k2 = right after the last f-fire (or a1+1 if f never fires).
Then f fires 0 in [k2, a2). We need b fires even in [k2, a2).

BUT: my earlier test showed this doesn't always work (the "ternary-only" failures).
The problem: b might fire ODD times after f's last fire.

New idea: also consider BINARY procs i with binary neighbors.
If i is binary with binary neighbor b:
- Between consecutive fires of i, b fires some times
- Take k2 = right after the last f-fire
- b fires in [k2, a2) might be odd
- BUT: if i has binary neighbor on BOTH sides (two adjacent binary procs),
  then both neighbors are binary, so we just need even fires from both.

Actually, let me try a different approach entirely.

The "excursion return" argument:
Between consecutive fires of proc i (interval (a1, a2)):
1. Mover starts at a neighbor of i (by locality from a1)
2. Mover walks around the ring
3. Mover returns to a neighbor of i (by locality to a2)

The LAST step before a2 has mover = some neighbor of i (L or R).
Say mover[a2-1] = R(i). Then the "return" is from the right.

Now, in [a2-1, a2), R fires 1 time, L fires 0.
In [a2-2, a2), if mover[a2-2] is also R, then R fires 2 (even!), L fires 0. WIN!

So: do we always have some proc i with TWO consecutive same-side returns?

Let me test this "double return" hypothesis.
"""
import random
from collections import Counter
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def test_double_return(mover_word, moduli, n):
    """
    For each proc i, look at consecutive fires (a1, a2).
    Check if the last 2 steps before a2 are both the SAME neighbor.
    If so, that neighbor fires 2 (even) times, other fires 0 -> EC.
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

    for i in range(n):
        if fc[i] < 2: continue
        fire_steps = [k for k in range(CL) if mover_word[k] == i]

        for idx in range(len(fire_steps)):
            a1 = fire_steps[idx]
            a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
            if a2_raw <= a1: a2_raw += CL

            gap_len = a2_raw - a1 - 1
            if gap_len < 2: continue  # need at least 2 steps in gap

            # Last two steps before a2
            s1 = (a2_raw - 2) % CL  # step a2-2
            s2 = (a2_raw - 1) % CL  # step a2-1

            m1 = mover_word[s1]
            m2 = mover_word[s2]

            li = left(i, n)
            ri = right(i, n)

            # Both must be same neighbor of i, and that neighbor is binary
            if m1 == m2 and m1 != i and (m1 == li or m1 == ri):
                nbr = m1
                if moduli[nbr] == 2:
                    return (True, f"proc={i}, double-return at {nbr}")

    return (False, "no double return")

def test_any_even_suffix(mover_word, moduli, n):
    """
    For each proc i with a binary neighbor, check ALL possible suffix lengths.
    Find any suffix [k2, a2) where binary neighbor fires even and other fires 0.
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

    for i in range(n):
        if fc[i] < 2: continue
        li = left(i, n)
        ri = right(i, n)

        # Check if at least one neighbor is binary
        if moduli[li] != 2 and moduli[ri] != 2:
            continue

        fire_steps = [k for k in range(CL) if mover_word[k] == i]

        for idx in range(len(fire_steps)):
            a1 = fire_steps[idx]
            a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
            if a2_raw <= a1: a2_raw += CL

            # Scan backward from a2, tracking parity of each neighbor
            # At each step, check if the suffix works
            b_fires_L = 0
            b_fires_R = 0

            for k_raw in range(a2_raw - 1, a1, -1):
                k = k_raw % CL
                m = mover_word[k]
                if m == i: continue  # shouldn't happen (between consec fires)
                if m == li: b_fires_L += 1
                if m == ri: b_fires_R += 1

                # Check: suffix [k_raw, a2) with these fire counts
                li_ok = (b_fires_L == 0) or (moduli[li] == 2 and b_fires_L % 2 == 0)
                ri_ok = (b_fires_R == 0) or (moduli[ri] == 2 and b_fires_R % 2 == 0)

                if li_ok and ri_ok and m != i:
                    return (True, f"proc={i}, suffix from {k_raw}")

    return (False, "no even suffix found for proc with binary neighbor")


n = 5
moduli = [2, 2, 2, 3, 3]

print("=== Double return test ===")
s, f, sk = 0, 0, 0
for trial in range(200000):
    word = [random.randint(0, n-1)]
    for _ in range(random.randint(2*n+1, 4*n) - 1):
        curr = word[-1]
        word.append(random.choice([curr, left(curr, n), right(curr, n)]))
    r = test_double_return(word, moduli, n)
    if r is None: sk += 1
    elif r[0]: s += 1
    else: f += 1
print(f"n=5: Valid={s+f}, Pass={s}, Fail={f}")

print("\n=== Any-even-suffix test (proc with binary neighbor) ===")
s, f, sk = 0, 0, 0
fail_words = []
for trial in range(200000):
    word = [random.randint(0, n-1)]
    for _ in range(random.randint(2*n+1, 4*n) - 1):
        curr = word[-1]
        word.append(random.choice([curr, left(curr, n), right(curr, n)]))
    r = test_any_even_suffix(word, moduli, n)
    if r is None: sk += 1
    elif r[0]: s += 1
    else:
        f += 1
        if len(fail_words) < 3:
            fail_words.append(word)
print(f"n=5: Valid={s+f}, Pass={s}, Fail={f}")
if fail_words:
    for w in fail_words:
        fc = [0] * n
        for m in w: fc[m] += 1
        print(f"  FAIL: word={w}, fc={fc}")

# Also test n=9
for n, moduli in [(9, [2,2,2,3,3,3,3,3,3]), (9, [2,3,3,2,3,3,2,3,3])]:
    print(f"\n=== Any-even-suffix: n={n}, moduli={moduli} ===")
    s, f, sk = 0, 0, 0
    for trial in range(200000):
        word = [random.randint(0, n-1)]
        for _ in range(random.randint(2*n+1, 4*n) - 1):
            curr = word[-1]
            word.append(random.choice([curr, left(curr, n), right(curr, n)]))
        r = test_any_even_suffix(word, moduli, n)
        if r is None: sk += 1
        elif r[0]: s += 1
        else: f += 1
    print(f"Valid={s+f}, Pass={s}, Fail={f}")
