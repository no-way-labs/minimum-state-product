"""
Test: for at least one binary b, does some side have max >= 2?
"""
import random
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def test_any_binary(mover_word, moduli, n):
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

    # For EACH binary b, check BOTH sides
    for b in range(n):
        if moduli[b] != 2: continue
        for i in [right(b, n), left(b, n)]:
            fire_steps_i = [k for k in range(CL) if mover_word[k] == i]
            if len(fire_steps_i) < 2: continue
            for idx in range(len(fire_steps_i)):
                a1 = fire_steps_i[idx]
                a2_raw = fire_steps_i[(idx + 1) % len(fire_steps_i)]
                if a2_raw <= a1: a2_raw += CL
                gap = list(range(a1+1, a2_raw))
                b_in = sum(1 for k in gap if mover_word[k % CL] == b)
                if b_in >= 2:
                    return True  # Found one!

    return False

configs = [
    (5, [2,2,2,3,3]),
    (7, [2,2,2,3,3,3,3]),
    (9, [2,2,2,3,3,3,3,3,3]),
    (9, [2,3,3,2,3,3,2,3,3]),
    (9, [2,3,2,3,2,3,3,3,3]),
]

for n, moduli in configs:
    s, f = 0, 0
    for trial in range(500000):
        word = [random.randint(0, n-1)]
        for _ in range(random.randint(2*n+1, 5*n) - 1):
            curr = word[-1]
            word.append(random.choice([curr, left(curr, n), right(curr, n)]))
        r = test_any_binary(word, moduli, n)
        if r is None: continue
        if r: s += 1
        else: f += 1
    print(f"n={n}, moduli={moduli}: Valid={s+f}, Pass={s}, Fail={f}")
