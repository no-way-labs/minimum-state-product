"""
Test the precise claim:

For proc i with binary neighbor b and far neighbor f:
Between consecutive fires (a1, a2) of i, scanning backward from a2:
- Let P = position of last f-fire (closest to a2), or a1 if f never fires
- In the suffix (P, a2), only b fires among {b, f}, and i never fires
- b fires some count c_b in (P, a2)
- We need c_b to be even at some intermediate step

If c_b is even at step P+1 (i.e., b fires even times in [P+1, a2)), WIN.
We take k2 = P+1 (or the first non-i step after P).

So the question: when f doesn't fire in a suffix, does b fire even times?

The step at a2-1 (approach step) is always b or f (by locality).
If approach is from b: b fires in [a2-1, a2), count=1 (odd).
  The step before might also be b (count=2, even) -> WIN.
  Or might be LL(i) or something else -> b-count stays 1.

If approach is from f: f fires at a2-1. The "no f" suffix is [?, a2-1).
  The step a2-2 must be adjacent to f. It could be f, i (impossible), or RR(i).
  If a2-2 fires RR(i): suffix [a2-2, a2-1) has no b or f fire. b-count=0 (even). WIN.
  If a2-2 fires f: f fires again. The no-f suffix starts before a2-2.

So the approach is:
1. If approach from f, and step before is far (not b, not f, not i): WIN (b=0, f=0)
2. If approach from b, and step before is also b: WIN (b=2 even, f=0)
3. Need to handle the other sub-cases.

Let me categorize ALL winning patterns more carefully.
"""
import random
from collections import Counter
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def categorize_win(mover_word, moduli, n):
    CL = len(mover_word)
    fc = [0] * n
    for m in mover_word:
        fc[m] += 1

    if not all(f >= 2 for f in fc): return None
    if not any(f >= 3 for f in fc): return None
    for p in range(n):
        if moduli[p] == 2 and fc[p] % 2 != 0: return None

    cw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == right(mover_word[k], n))
    ccw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == left(mover_word[k], n))
    if cw != ccw or cw == 0: return None

    for k in range(CL):
        m_curr = mover_word[k]
        m_next = mover_word[(k+1) % CL]
        if m_next != m_curr and m_next != left(m_curr, n) and m_next != right(m_curr, n):
            return None

    categories = []

    for i in range(n):
        if fc[i] < 2: continue
        li = left(i, n)
        ri = right(i, n)
        if moduli[li] != 2 and moduli[ri] != 2: continue

        # Identify binary and far sides
        if moduli[li] == 2 and moduli[ri] == 2:
            sides = [('L', li, ri), ('R', ri, li)]
        elif moduli[li] == 2:
            sides = [('L', li, ri)]
        else:
            sides = [('R', ri, li)]

        fire_steps = [k for k in range(CL) if mover_word[k] == i]

        for bin_label, b, f in sides:
            for idx in range(len(fire_steps)):
                a1 = fire_steps[idx]
                a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
                if a2_raw <= a1: a2_raw += CL

                gap = a2_raw - a1 - 1
                if gap < 1: continue

                # Scan backward, find winning k2
                b_count = 0
                f_count = 0
                won = False
                for k_raw in range(a2_raw - 1, a1, -1):
                    k = k_raw % CL
                    m = mover_word[k]
                    if m == i: continue
                    if m == b: b_count += 1
                    if m == f: f_count += 1

                    b_ok = (b_count % 2 == 0)  # binary: even -> preserved
                    f_ok = (f_count == 0)  # far: zero fires

                    if b_ok and f_ok:
                        # Categorize the win
                        dist = a2_raw - k_raw
                        categories.append((bin_label, dist, b_count, f_count))
                        won = True
                        break

    return categories if categories else None


n = 9
moduli = [2, 2, 2, 3, 3, 3, 3, 3, 3]

all_cats = []
n_valid = 0
for trial in range(300000):
    word = [random.randint(0, n-1)]
    for _ in range(random.randint(2*n+1, 5*n) - 1):
        curr = word[-1]
        word.append(random.choice([curr, left(curr, n), right(curr, n)]))

    result = categorize_win(word, moduli, n)
    if result is None: continue
    n_valid += 1
    all_cats.extend(result)

print(f"n=9, Valid cycles: {n_valid}, Winning combos: {len(all_cats)}")
print("\n--- Distance from k2 to a2 ---")
print(Counter(d for _, d, _, _ in all_cats).most_common(10))
print("\n--- b_count at winning k2 ---")
print(Counter(bc for _, _, bc, _ in all_cats).most_common(10))
print("\n--- (dist, b_count) combos ---")
print(Counter((d, bc) for _, d, bc, _ in all_cats).most_common(20))

# The key question: in the suffix [k2, a2) with f_count=0,
# what determines whether b fires even?
# It's about the local structure near a2.
# If approach from b side: at a2-1, b fires once (odd).
#   Next step a2-2 determines everything.
#   If a2-2 = b: b-count = 2 (WIN at dist=2)
#   If a2-2 = far from i: b-count = 1 (but f-count still 0, b-count odd -> no win yet)
#     BUT: we can take k2 = a2-2 itself! b-count=0 (even), f-count=0.
#     Wait, but mover[a2-2] is far from i (not b, not f, not i).
#     So b-count at a2-2 is: scanning [a2-2, a2): mover at a2-2 is "other", mover at a2-1 is b.
#     b-count = 1 (from a2-1). Still odd.
#     We need to go to k2 BEFORE the b-fire at a2-1, i.e., k2 such that [k2, a2) doesn't
#     include a2-1... no wait, it always includes a2-1.

# Wait I'm confusing myself. Let me re-read the code.
# The scan goes backward from a2-1 to a1+1.
# At each step k_raw, we compute cumulative b-fires and f-fires in [k_raw, a2).
# So at k_raw = a2-1: if mover is b, b_count=1, f_count=0.
# At k_raw = a2-2: if mover is "other", b_count still 1, f_count still 0. No win.
# The win requires b_count=0. That means: NO b fires in [k_raw, a2).
# That requires k_raw to be past ALL b-fires in the interval.

# Actually, b_count=0 means taking k2 where [k2, a2) contains 0 b-fires.
# This means k2 is after the LAST b-fire (and after last f-fire).
# So we need a step after the last b-fire and last f-fire, which is a non-i step.

# Let me re-examine. The approach step (a2-1) is the LAST step before a2.
# If mover[a2-1] = b, then the last b-fire in the interval is at a2-1.
# So there's no step after the last b-fire but before a2 (except a2 itself).
# b_count = 0 requires k2 > a2-1, which is only a2 (the fire step itself). Can't use.

# BUT: b_count=2 is also even! So if there's a second b-fire before a2-1,
# say at position p, then [p, a2) has b_count=2 (even), f_count depends.

# OK, the winning condition is b_count EVEN (not just 0).
# Let me re-examine the patterns.

print("\n\n--- Where b_count > 0 wins happen ---")
gt0 = [(d, bc) for _, d, bc, _ in all_cats if bc > 0]
print(Counter(gt0).most_common(20))
