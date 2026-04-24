"""
DEFINITIVE verification of the ZW provider EC mechanism.

Tests the exact claim that will be the Lean sorry:
exists_provider_interval — for some proc i with binary neighbor,
consecutive fire pair (a1, a2), and step k2 in between:
  left(i) fires 0 or binary-even in [k2, a2)
  right(i) fires 0 or binary-even in [k2, a2)
  i fires 0 in [k2, a2) [automatic]
  moverAt k2 != i

Tested with the binary-even-fc constraint (valid good cycles only).
"""
import random
from collections import Counter
random.seed(2026)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def check_provider_ec(mover_word, moduli, n):
    CL = len(mover_word)
    fc = [0] * n
    for m in mover_word:
        fc[m] += 1

    # Validity checks
    if not all(f >= 2 for f in fc): return None
    if not any(f >= 3 for f in fc): return None
    for p in range(n):
        if moduli[p] == 2 and fc[p] % 2 != 0: return None

    # Zero winding with cw > 0
    cw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == right(mover_word[k], n))
    ccw = sum(1 for k in range(CL) if mover_word[(k+1) % CL] == left(mover_word[k], n))
    if cw != ccw or cw == 0: return None

    # Locality
    for k in range(CL):
        m_curr = mover_word[k]
        m_next = mover_word[(k+1) % CL]
        if m_next != m_curr and m_next != left(m_curr, n) and m_next != right(m_curr, n):
            return None

    # Search for provider interval
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

            # Scan backward from a2
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

                if li_ok and ri_ok and m != i:
                    return True

    return False


# Comprehensive test across many configurations
configs = [
    (5, [2,2,2,3,3]),
    (5, [2,2,2,2,3]),
    (7, [2,2,2,3,3,3,3]),
    (7, [2,3,2,3,2,3,3]),
    (9, [2,2,2,3,3,3,3,3,3]),
    (9, [2,3,3,2,3,3,2,3,3]),
    (9, [2,3,2,3,2,3,3,3,3]),
    (9, [2,2,2,2,3,3,3,3,3]),
    (11, [2,2,2,3,3,3,3,3,3,3,3]),
    (11, [2,3,3,3,2,3,3,3,2,3,3]),
    (13, [2,2,2,3,3,3,3,3,3,3,3,3,3]),
]

total_valid = 0
total_fail = 0

for n, moduli in configs:
    s, f = 0, 0
    for trial in range(500000):
        word = [random.randint(0, n-1)]
        for _ in range(random.randint(2*n+1, 5*n) - 1):
            curr = word[-1]
            word.append(random.choice([curr, left(curr, n), right(curr, n)]))
        r = check_provider_ec(word, moduli, n)
        if r is None: continue
        if r: s += 1
        else: f += 1

    total = s + f
    total_valid += total
    total_fail += f
    status = "PASS" if f == 0 else "FAIL"
    print(f"n={n:2d}, B={sum(1 for m in moduli if m==2)}, Valid={total:5d}, Fail={f} [{status}]")

print(f"\nTOTAL: {total_valid} valid cycles, {total_fail} failures")
if total_fail == 0:
    print("ALL PASS -- mechanism verified!")
else:
    print(f"FAILURES FOUND: {total_fail}")
