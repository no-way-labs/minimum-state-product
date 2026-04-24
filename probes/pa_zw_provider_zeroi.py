"""
Test: for some binary b and some neighbor i,
between two consecutive fires of b, i fires 0 times.

This would mean the two b-fires bracket an interval with no i-fires,
so both b-fires are in the SAME interval of i -> b fires >= 2 in that interval.
"""
import random
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def test_zero_i_between_b(mover_word, moduli, n):
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

    for b in range(n):
        if moduli[b] != 2: continue
        fire_steps_b = [k for k in range(CL) if mover_word[k] == b]
        if len(fire_steps_b) < 2: continue

        for i in [left(b, n), right(b, n)]:
            for idx in range(len(fire_steps_b)):
                s1 = fire_steps_b[idx]
                s2_raw = fire_steps_b[(idx + 1) % len(fire_steps_b)]
                if s2_raw <= s1: s2_raw += CL

                # Check: does i fire in (s1, s2)?
                i_fires = sum(1 for k in range(s1+1, s2_raw) if mover_word[k % CL] == i)
                if i_fires == 0:
                    return True  # Found!

    return False

configs = [
    (5, [2,2,2,3,3]),
    (7, [2,2,2,3,3,3,3]),
    (9, [2,2,2,3,3,3,3,3,3]),
    (9, [2,3,3,2,3,3,2,3,3]),
]

for n, moduli in configs:
    s, f = 0, 0
    for trial in range(500000):
        word = [random.randint(0, n-1)]
        for _ in range(random.randint(2*n+1, 5*n) - 1):
            curr = word[-1]
            word.append(random.choice([curr, left(curr, n), right(curr, n)]))
        r = test_zero_i_between_b(word, moduli, n)
        if r is None: continue
        if r: s += 1
        else: f += 1
    print(f"n={n}, moduli={moduli}: Valid={s+f}, Pass={s}, Fail={f}")
