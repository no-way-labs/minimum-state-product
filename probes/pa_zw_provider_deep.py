"""
Deep analysis: what is the SIMPLEST sufficient condition?
"""
import random
from collections import Counter
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def find_winning_proc_type(mover_word, moduli, n):
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

    binary_winner = False
    ternary_winner = False
    winner_has_binary_neighbor = False
    any_winner = False

    for i in range(n):
        if fc[i] < 2: continue
        fire_steps = [k for k in range(CL) if mover_word[k] == i]

        found_for_i = False
        for idx in range(len(fire_steps)):
            if found_for_i: break
            a1 = fire_steps[idx]
            a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
            if a2_raw <= a1: a2_raw += CL

            gap = list(range(a1 + 1, a2_raw))
            if not gap: continue

            for k2_raw in gap:
                k2 = k2_raw % CL
                if mover_word[k2] == i: continue

                interval = [t % CL for t in range(k2_raw, a2_raw)]
                li = left(i, n)
                ri = right(i, n)
                li_fires = sum(1 for k in interval if mover_word[k] == li)
                ri_fires = sum(1 for k in interval if mover_word[k] == ri)
                li_ok = (li_fires == 0) or (moduli[li] == 2 and li_fires % 2 == 0)
                ri_ok = (ri_fires == 0) or (moduli[ri] == 2 and ri_fires % 2 == 0)

                if li_ok and ri_ok:
                    any_winner = True
                    found_for_i = True
                    if moduli[i] == 2:
                        binary_winner = True
                    else:
                        ternary_winner = True
                    if moduli[li] == 2 or moduli[ri] == 2:
                        winner_has_binary_neighbor = True
                    break

    if not any_winner:
        return "FAIL"

    return {
        'binary_winner': binary_winner,
        'ternary_winner': ternary_winner,
        'has_bin_nbr': winner_has_binary_neighbor
    }

configs = [
    (9, [2,2,2,3,3,3,3,3,3], "consec binary 0,1,2"),
    (9, [2,3,3,2,3,3,2,3,3], "spaced binary 0,3,6"),
    (9, [2,3,2,3,2,3,3,3,3], "binary 0,2,4"),
    (5, [2,2,2,3,3], "n=5 consec"),
    (7, [2,2,2,3,3,3,3], "n=7 consec"),
]

for n, moduli, desc in configs:
    print(f"\n=== {desc}: n={n}, moduli={moduli} ===")
    stats = Counter()
    n_valid = 0

    for trial in range(100000):
        word = [random.randint(0, n-1)]
        for _ in range(random.randint(2*n+1, 4*n) - 1):
            curr = word[-1]
            word.append(random.choice([curr, left(curr, n), right(curr, n)]))

        result = find_winning_proc_type(word, moduli, n)
        if result is None: continue
        if result == "FAIL":
            stats['FAIL'] += 1
            continue
        n_valid += 1
        if result['binary_winner']:
            stats['binary_wins'] += 1
        if result['ternary_winner']:
            stats['ternary_wins'] += 1
        if not result['binary_winner']:
            stats['ternary_only'] += 1

    print(f"Valid: {n_valid}, Fail: {stats.get('FAIL', 0)}")
    print(f"Binary proc wins: {stats.get('binary_wins', 0)}/{n_valid}")
    print(f"Ternary proc wins: {stats.get('ternary_wins', 0)}/{n_valid}")
    print(f"ONLY ternary wins: {stats.get('ternary_only', 0)}/{n_valid}")
