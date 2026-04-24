"""
Definitive test with binary-even-fc constraint.

For a VALID good cycle:
- all fc >= 2
- binary procs have even fc
- fc != 1 for all
- some fc >= 3
- zero winding with cw > 0
- next_mover_is_local
"""
import random
from collections import Counter
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def check_provider_ec(mover_word, moduli, n):
    CL = len(mover_word)
    fc = [0] * n
    for m in mover_word:
        fc[m] += 1

    if not all(f >= 2 for f in fc): return None
    if not any(f >= 3 for f in fc): return None

    # Binary procs must have even fire count
    for p in range(n):
        if moduli[p] == 2 and fc[p] % 2 != 0:
            return None

    cw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == right(mover_word[k], n))
    ccw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == left(mover_word[k], n))
    if cw != ccw or cw == 0: return None

    for k in range(CL):
        m_curr = mover_word[k]
        m_next = mover_word[(k+1) % CL]
        if m_next != m_curr and m_next != left(m_curr, n) and m_next != right(m_curr, n):
            return None

    # Try all procs with binary neighbor, using any-even-suffix
    for i in range(n):
        if fc[i] < 2: continue
        li = left(i, n)
        ri = right(i, n)

        # Must have at least one binary neighbor
        if moduli[li] != 2 and moduli[ri] != 2:
            continue

        fire_steps = [k for k in range(CL) if mover_word[k] == i]

        for idx in range(len(fire_steps)):
            a1 = fire_steps[idx]
            a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
            if a2_raw <= a1: a2_raw += CL

            gap = list(range(a1 + 1, a2_raw))
            if not gap: continue

            b_fires_L = 0
            b_fires_R = 0
            for k_raw in range(a2_raw - 1, a1, -1):
                k = k_raw % CL
                m = mover_word[k]
                if m == i: continue
                if m == li: b_fires_L += 1
                if m == ri: b_fires_R += 1

                li_ok = (b_fires_L == 0) or (moduli[li] == 2 and b_fires_L % 2 == 0)
                ri_ok = (b_fires_R == 0) or (moduli[ri] == 2 and b_fires_R % 2 == 0)

                if li_ok and ri_ok and m != i:
                    return (True, f"proc={i}")

    # Also try procs without binary neighbor (fall through)
    for i in range(n):
        if fc[i] < 2: continue
        fire_steps = [k for k in range(CL) if mover_word[k] == i]
        li = left(i, n)
        ri = right(i, n)

        for idx in range(len(fire_steps)):
            a1 = fire_steps[idx]
            a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
            if a2_raw <= a1: a2_raw += CL

            gap = list(range(a1 + 1, a2_raw))
            if not gap: continue

            for k2_raw in gap:
                k2 = k2_raw % CL
                if mover_word[k2] == i: continue

                interval = [t % CL for t in range(k2_raw, a2_raw)]
                li_fires = sum(1 for k in interval if mover_word[k] == li)
                ri_fires = sum(1 for k in interval if mover_word[k] == ri)
                li_ok = (li_fires == 0) or (moduli[li] == 2 and li_fires % 2 == 0)
                ri_ok = (ri_fires == 0) or (moduli[ri] == 2 and ri_fires % 2 == 0)

                if li_ok and ri_ok:
                    return (True, f"proc={i} (fallback)")

    return (False, f"fc={fc}, CL={CL}")


configs = [
    (5, [2,2,2,3,3], "n5 consec"),
    (7, [2,2,2,3,3,3,3], "n7 consec"),
    (9, [2,2,2,3,3,3,3,3,3], "n9 consec"),
    (9, [2,3,3,2,3,3,2,3,3], "n9 spaced"),
    (9, [2,3,2,3,2,3,3,3,3], "n9 alt"),
    (11, [2,2,2,3,3,3,3,3,3,3,3], "n11 consec"),
    (5, [2,2,2,2,3], "n5 4bin"),
    (9, [2,2,2,2,3,3,3,3,3], "n9 4bin"),
]

for n, moduli, desc in configs:
    s, f, sk = 0, 0, 0
    fail_words = []
    for trial in range(300000):
        word = [random.randint(0, n-1)]
        for _ in range(random.randint(2*n+1, 5*n) - 1):
            curr = word[-1]
            word.append(random.choice([curr, left(curr, n), right(curr, n)]))
        r = check_provider_ec(word, moduli, n)
        if r is None: sk += 1
        elif r[0]: s += 1
        else:
            f += 1
            if len(fail_words) < 2:
                fail_words.append((word, r[1]))

    total = s + f
    print(f"{desc}: Valid={total}, Pass={s}, Fail={f}")
    for w, d in fail_words:
        fc = [0]*n
        for m in w: fc[m] += 1
        print(f"  FAIL: {d}, fc={fc}")
