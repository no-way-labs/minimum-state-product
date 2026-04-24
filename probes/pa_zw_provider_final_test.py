"""
Final comprehensive test + analyze the structure of why consecutive b-fires
with no f after them always exist.
"""
import random
from collections import Counter
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def comprehensive_test(mover_word, moduli, n):
    """The full mechanism: find proc i with binary nbr b, interval with b>=2,
    and suffix from second-to-last b-fire (or earlier) with even b, zero f."""
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

    for i in range(n):
        li = left(i, n)
        ri = right(i, n)
        for b, f in [(li, ri), (ri, li)]:
            if moduli[b] != 2: continue
            fire_steps_i = [k for k in range(CL) if mover_word[k] == i]
            if len(fire_steps_i) < 2: continue

            for idx in range(len(fire_steps_i)):
                a1 = fire_steps_i[idx]
                a2_raw = fire_steps_i[(idx + 1) % len(fire_steps_i)]
                if a2_raw <= a1: a2_raw += CL
                gap = list(range(a1 + 1, a2_raw))
                if not gap: continue

                b_fires_in = [k for k in gap if mover_word[k % CL] == b]
                f_fires_in = [k for k in gap if mover_word[k % CL] == f]

                if len(b_fires_in) < 2: continue

                for j in range(len(b_fires_in) - 1):
                    bj = b_fires_in[j]
                    f_after = [fk for fk in f_fires_in if fk >= bj]
                    if not f_after:
                        b_in_suffix = sum(1 for bk in b_fires_in if bk >= bj)
                        if b_in_suffix % 2 == 0:
                            return True

    return False


configs = [
    (5, [2,2,2,3,3]),
    (5, [2,2,2,2,3]),
    (7, [2,2,2,3,3,3,3]),
    (9, [2,2,2,3,3,3,3,3,3]),
    (9, [2,3,3,2,3,3,2,3,3]),
    (9, [2,3,2,3,2,3,3,3,3]),
    (11, [2,2,2,3,3,3,3,3,3,3,3]),
    (9, [2,2,2,2,3,3,3,3,3]),
    (13, [2,2,2,3,3,3,3,3,3,3,3,3,3]),
]

for n, moduli in configs:
    s, f = 0, 0
    for trial in range(300000):
        word = [random.randint(0, n-1)]
        for _ in range(random.randint(2*n+1, 5*n) - 1):
            curr = word[-1]
            word.append(random.choice([curr, left(curr, n), right(curr, n)]))
        r = comprehensive_test(word, moduli, n)
        if r is None: continue
        if r: s += 1
        else: f += 1
    total = s + f
    print(f"n={n}, moduli={moduli}: Valid={total}, Pass={s}, Fail={f}")
