"""
Analyze failing cases for the ternary-only approach.
What proc actually wins in those cases?
"""
import random
from collections import Counter
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def full_check(mover_word, moduli, n):
    """Full check - which proc wins and how."""
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

    winners = []
    for i in range(n):
        if fc[i] < 2: continue
        fire_steps = [k for k in range(CL) if mover_word[k] == i]

        for idx in range(len(fire_steps)):
            a1 = fire_steps[idx]
            a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
            if a2_raw <= a1: a2_raw += CL

            gap = list(range(a1 + 1, a2_raw))
            if not gap: continue

            li = left(i, n)
            ri = right(i, n)

            for k2_raw in gap:
                k2 = k2_raw % CL
                if mover_word[k2] == i: continue

                interval = [t % CL for t in range(k2_raw, a2_raw)]
                li_fires = sum(1 for k in interval if mover_word[k] == li)
                ri_fires = sum(1 for k in interval if mover_word[k] == ri)
                li_ok = (li_fires == 0) or (moduli[li] == 2 and li_fires % 2 == 0)
                ri_ok = (ri_fires == 0) or (moduli[ri] == 2 and ri_fires % 2 == 0)

                if li_ok and ri_ok:
                    winners.append({
                        'proc': i, 'mod_i': moduli[i],
                        'mod_li': moduli[li], 'mod_ri': moduli[ri],
                        'li_fires': li_fires, 'ri_fires': ri_fires,
                        'gap': a2_raw - a1, 'fc_i': fc[i]
                    })
                    break
            if winners and winners[-1]['proc'] == i:
                break  # found one for this proc

    return winners if winners else None

def ternary_only_check(mover_word, moduli, n):
    """Check if ternary-with-binary-neighbor approach works."""
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

    for t in range(n):
        if moduli[t] == 2: continue
        li = left(t, n)
        ri = right(t, n)
        if moduli[li] != 2 and moduli[ri] != 2: continue

        fire_steps = [k for k in range(CL) if mover_word[k] == t]
        if len(fire_steps) < 2: continue

        b = li if moduli[li] == 2 else ri
        far = ri if b == li else li

        for idx in range(len(fire_steps)):
            a1 = fire_steps[idx]
            a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
            if a2_raw <= a1: a2_raw += CL

            gap = list(range(a1 + 1, a2_raw))
            if not gap: continue

            last_far_fire = -1
            for k_raw in gap:
                k = k_raw % CL
                if mover_word[k] == far:
                    last_far_fire = k_raw

            k2_raw = (last_far_fire + 1) if last_far_fire != -1 else (a1 + 1)
            if k2_raw >= a2_raw: continue
            k2 = k2_raw % CL
            if mover_word[k2] == t: continue

            interval = [s % CL for s in range(k2_raw, a2_raw)]
            b_fires = sum(1 for k in interval if mover_word[k] == b)
            if b_fires == 0 or b_fires % 2 == 0:
                return True

    return False

n = 5
moduli = [2, 2, 2, 3, 3]

print("Analyzing cases where ternary-only fails but full check passes...")
fail_winners = []
count = 0

for trial in range(500000):
    word = [random.randint(0, n-1)]
    for _ in range(random.randint(2*n+1, 4*n) - 1):
        curr = word[-1]
        word.append(random.choice([curr, left(curr, n), right(curr, n)]))

    tern_result = ternary_only_check(word, moduli, n)
    if tern_result is None or tern_result: continue

    full_result = full_check(word, moduli, n)
    if full_result is None: continue

    count += 1
    for w in full_result:
        fail_winners.append(w)
    if count <= 5:
        print(f"\nExample {count}: word={word}")
        fc = [0] * n
        for m in word:
            fc[m] += 1
        print(f"  fc={fc}")
        for w in full_result:
            print(f"  Winner: proc={w['proc']}, mod={w['mod_i']}, mod_L={w['mod_li']}, mod_R={w['mod_ri']}, li_fires={w['li_fires']}, ri_fires={w['ri_fires']}")

print(f"\nTotal ternary-only failures: {count}")
print("\n--- Winning proc modulus in failure cases ---")
print(Counter(w['mod_i'] for w in fail_winners))
print("\n--- L neighbor modulus ---")
print(Counter(w['mod_li'] for w in fail_winners))
print("\n--- R neighbor modulus ---")
print(Counter(w['mod_ri'] for w in fail_winners))
print("\n--- li_fires ---")
print(Counter(w['li_fires'] for w in fail_winners).most_common(10))
print("\n--- ri_fires ---")
print(Counter(w['ri_fires'] for w in fail_winners).most_common(10))
