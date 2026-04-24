"""
Check: when considering both possible binary sides,
is b_count always 2? Also check if b_count=0 ever wins.
"""
import random
from collections import Counter
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def full_categorize(mover_word, moduli, n):
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

    all_wins = []

    for i in range(n):
        if fc[i] < 2: continue
        li = left(i, n)
        ri = right(i, n)
        if moduli[li] != 2 and moduli[ri] != 2: continue

        fire_steps = [k for k in range(CL) if mover_word[k] == i]

        for idx in range(len(fire_steps)):
            a1 = fire_steps[idx]
            a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
            if a2_raw <= a1: a2_raw += CL

            gap = a2_raw - a1 - 1
            if gap < 1: continue

            # Full check: both neighbors
            li_count = 0
            ri_count = 0
            for k_raw in range(a2_raw - 1, a1, -1):
                k = k_raw % CL
                m = mover_word[k]
                if m == i: continue
                if m == li: li_count += 1
                if m == ri: ri_count += 1

                li_ok = (li_count == 0) or (moduli[li] == 2 and li_count % 2 == 0)
                ri_ok = (ri_count == 0) or (moduli[ri] == 2 and ri_count % 2 == 0)

                if li_ok and ri_ok:
                    all_wins.append({
                        'li_count': li_count, 'ri_count': ri_count,
                        'mod_li': moduli[li], 'mod_ri': moduli[ri],
                    })
                    break

    return all_wins if all_wins else None


configs = [
    (5, [2,2,2,3,3]),
    (5, [2,2,2,2,3]),
    (9, [2,2,2,3,3,3,3,3,3]),
    (9, [2,3,3,2,3,3,2,3,3]),
]

for n, moduli in configs:
    all_wins = []
    for trial in range(300000):
        word = [random.randint(0, n-1)]
        for _ in range(random.randint(2*n+1, 5*n) - 1):
            curr = word[-1]
            word.append(random.choice([curr, left(curr, n), right(curr, n)]))

        result = full_categorize(word, moduli, n)
        if result is None: continue
        all_wins.extend(result)

    print(f"\nn={n}, moduli={moduli}, wins={len(all_wins)}")
    print("--- (li_count, ri_count, mod_li, mod_ri) ---")
    combos = Counter((w['li_count'], w['ri_count'], w['mod_li'], w['mod_ri']) for w in all_wins)
    for (lc, rc, ml, mr), cnt in combos.most_common(20):
        print(f"  li={lc} (mod={ml}), ri={rc} (mod={mr}): {cnt}")
