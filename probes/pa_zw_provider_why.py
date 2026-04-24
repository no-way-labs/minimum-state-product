"""
Understand WHY the binary-neighbor suffix always works.

Key insight to test: Consider a proc i with binary neighbor b (on, say, the left).
The far neighbor is f = right(i).

Between consecutive fires of i (interval (a1, a2)):
Let F_b = total fires of b in (a1, a2)
Let F_f = total fires of f in (a1, a2)

If we scan backward from a2, at each step we toggle the parity of b or f
(or neither, if the mover is far from i).

Claim: there exists k2 in (a1, a2) with mover[k2] != i, such that
in [k2, a2): b fires even (including 0), f fires 0.

This is equivalent to: there exists a suffix where f has fired 0 times
(we haven't reached any f-fire yet, scanning backward) AND b has fired
an even number of times.

Scanning backward from a2:
- We accumulate b-fires and f-fires
- At the start (just before a2), both counts are 0 (even, 0)
- As we go backward, each step either adds 1 to b-count, 1 to f-count,
  or neither

We want a step k2 where f-count = 0 AND b-count is even AND mover[k2] != i.

The LAST step before a2 (step a2-1) must be a neighbor of i (by locality).
So mover[a2-1] is L(i) or R(i) = b or f.

Case 1: mover[a2-1] = b. Then at k2 = a2-1: f-count=0, b-count=1 (odd). BAD.
  Continue scanning: k2 = a2-2. Need mover[a2-2] adjacent to mover[a2-1] = b.
  So mover[a2-2] in {b, left(b), right(b)} = {b, left(b), i}.
  But left(b) might not be i. Actually b = left(i), so right(b) = i, left(b) = left(left(i)).

  Sub-case 1a: mover[a2-2] = b. Now b-count=2 (even), f-count=0.
    If mover[a2-2] != i (TRUE since b != i): this is a WINNER! k2 = a2-2.

  Sub-case 1b: mover[a2-2] = i. But i doesn't fire between consecutive fires.
    IMPOSSIBLE (between consec fires of i, mover is never i).

  Sub-case 1c: mover[a2-2] = left(b) = LL(i). Now b-count=1, f-count=0.
    LL(i) is neither b nor f (unless ring is tiny). So neither counter increments.
    Wait: mover is LL(i), which is not b and not f = right(i).
    So b-count stays 1 (odd), f-count stays 0. BAD (b-count odd).

    Continue to a2-3: mover[a2-3] adj to LL(i).
    This excursion goes AWAY from i into the far side of the ring.
    Eventually must come BACK to fire i at a2.

    The return path must come through b (since the excursion went left through b).
    When it comes back through b, b-count goes to 2 (even). WIN.

    BUT: on the way back, it might pass through f too.
    If f fires on the way back, f-count > 0 when we reach the b-fire.

Case 2: mover[a2-1] = f. Then at k2 = a2-1: f-count=1, b-count=0.
  f-count > 0, so BAD.

  Continue: k2 = a2-2. mover[a2-2] adj to f.
  Sub-case 2a: mover[a2-2] = f. f-count=2, b-count=0.
    f is not binary (it's the far neighbor). If moduli[f] == 2, then f-count=2 is even -> OK.
    But we don't know f is binary. If f is ternary, f-count=2 is not usable.
    HOWEVER: b-count=0 which is even. b is binary. So we need BOTH to be OK:
    li_ok and ri_ok. b-count=0 -> OK. f-count=2 -> only OK if f is binary.

  Sub-case 2b: mover[a2-2] = i. IMPOSSIBLE.
  Sub-case 2c: mover[a2-2] = right(f) = RR(i). Far from i.
    f-count=1, b-count=0. f-count>0, BAD.
    Continues away from i...

So the key difficulty: when the approach is from the f side (Case 2),
f fires and we can't use that suffix.

THE REAL INSIGHT: We can try MULTIPLE consecutive fire intervals.
There are fc(i) >= 2 intervals. In at least one, the return is from the b side!

Actually no - we need something stronger. Let me check:
Does the approach side (b vs f) vary across intervals?
"""
import random
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def analyze_approach_sides(mover_word, moduli, n):
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

    results = []
    for i in range(n):
        if fc[i] < 2: continue
        li = left(i, n)
        ri = right(i, n)
        if moduli[li] != 2 and moduli[ri] != 2: continue

        fire_steps = [k for k in range(CL) if mover_word[k] == i]
        approach_sides = []

        for idx in range(len(fire_steps)):
            a2 = fire_steps[(idx + 1) % len(fire_steps)]
            prev_step = (a2 - 1) % CL
            m = mover_word[prev_step]
            if m == li:
                approach_sides.append('L')
            elif m == ri:
                approach_sides.append('R')
            else:
                approach_sides.append('?')  # shouldn't happen by locality

        results.append((i, approach_sides, moduli[li] == 2, moduli[ri] == 2))

    return results

n = 5
moduli = [2, 2, 2, 3, 3]

approach_stats = []
for trial in range(200000):
    word = [random.randint(0, n-1)]
    for _ in range(random.randint(2*n+1, 5*n) - 1):
        curr = word[-1]
        word.append(random.choice([curr, left(curr, n), right(curr, n)]))

    result = analyze_approach_sides(word, moduli, n)
    if result is None: continue

    for i, sides, l_bin, r_bin in result:
        # Does this proc have an approach from the binary side?
        bin_side = 'L' if l_bin else ('R' if r_bin else None)
        if bin_side is None: continue

        has_bin_approach = bin_side in sides
        approach_stats.append((len(sides), has_bin_approach, sides, bin_side))

print(f"Total proc-intervals analyzed: {len(approach_stats)}")
print(f"Has approach from binary side: {sum(1 for _, h, _, _ in approach_stats if h)}/{len(approach_stats)}")

# When approach is from binary side (b), do we always get even b-fires?
# Actually, approach from b means mover[a2-1] = b.
# Then scanning backward: b-count starts at 1 (odd from the approach step).
# We need to find an earlier step where b-count becomes even.
# If the NEXT step backward is also b, b-count = 2 (even). WIN.
# Otherwise we need to go further back.

# Let me check: when approach from binary side, does "double return" always work?
# i.e., mover[a2-1] = b AND mover[a2-2] = b?

print("\n--- Approach from binary side: double return? ---")
n_bin_approach = 0
n_double = 0
n_not_double_but_works = 0

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

        # For each proc with binary neighbor
        for i in range(n):
            if fc[i] < 2: continue
            li = left(i, n)
            ri = right(i, n)
            if moduli[li] != 2 and moduli[ri] != 2: continue

            fire_steps = [k for k in range(CL) if word[k] == i]

            for idx in range(len(fire_steps)):
                a1 = fire_steps[idx]
                a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
                if a2_raw <= a1: a2_raw += CL
                if a2_raw - a1 <= 2: continue

                prev = (a2_raw - 1) % CL
                m_prev = word[prev]

                b = li if moduli[li] == 2 else ri
                if m_prev == b:
                    n_bin_approach += 1
                    prev2 = (a2_raw - 2) % CL
                    if word[prev2] == b:
                        n_double += 1

print(f"\nBinary approaches: {n_bin_approach}")
print(f"Double returns: {n_double}/{n_bin_approach}")
