"""
Analyze the cases where ALL intervals of ALL binary procs are long (>= n-1).
"""
import random
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

n = 9
moduli = [2, 2, 2, 3, 3, 3, 3, 3, 3]

long_cases = []

for trial in range(5000000):
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
            if word[(k+1)%CL] not in [word[k], left(word[k],n), right(word[k],n)]:
                ok = False; break
        if not ok: continue

        all_long = True
        for b in range(n):
            if moduli[b] != 2: continue
            fire_steps = [k for k in range(CL) if word[k] == b]
            for idx in range(len(fire_steps)):
                s1 = fire_steps[idx]
                s2 = fire_steps[(idx + 1) % len(fire_steps)]
                if s2 <= s1: s2 += CL
                intv_len = s2 - s1 - 1
                if intv_len < n - 1:
                    all_long = False
                    break
            if not all_long: break

        if all_long:
            long_cases.append((word, fc, CL))
            if len(long_cases) >= 20:
                break

print(f"Found {len(long_cases)} all-long cases")
for word, fc, CL in long_cases[:5]:
    print(f"\nfc={fc}, CL={CL}")
    for b in range(n):
        if moduli[b] != 2: continue
        fire_steps = [k for k in range(CL) if word[k] == b]
        print(f"  binary {b}: fires at {fire_steps}")
        for idx in range(len(fire_steps)):
            s1 = fire_steps[idx]
            s2_raw = fire_steps[(idx + 1) % len(fire_steps)]
            if s2_raw <= s1: s2_raw += CL
            intv_len = s2_raw - s1 - 1
            # departure and approach
            dep = word[(s1 + 1) % CL]
            app = word[(s2_raw - 1) % CL]
            dep_side = 'L' if dep == left(b, n) else ('R' if dep == right(b, n) else '?')
            app_side = 'L' if app == left(b, n) else ('R' if app == right(b, n) else '?')
            # L and R fires in interval
            li = left(b, n)
            ri = right(b, n)
            l_fires = sum(1 for k in range(s1+1, s2_raw) if word[k % CL] == li)
            r_fires = sum(1 for k in range(s1+1, s2_raw) if word[k % CL] == ri)
            print(f"    interval {idx}: len={intv_len}, dep={dep_side}, app={app_side}, L_fires={l_fires}, R_fires={r_fires}")

    # Check clustering: for each binary b, some neighbor fires 0 in some interval
    for b in range(n):
        if moduli[b] != 2: continue
        fire_steps = [k for k in range(CL) if word[k] == b]
        for idx in range(len(fire_steps)):
            s1 = fire_steps[idx]
            s2_raw = fire_steps[(idx + 1) % len(fire_steps)]
            if s2_raw <= s1: s2_raw += CL
            li = left(b, n)
            ri = right(b, n)
            l_fires = sum(1 for k in range(s1+1, s2_raw) if word[k % CL] == li)
            r_fires = sum(1 for k in range(s1+1, s2_raw) if word[k % CL] == ri)
            if l_fires == 0 or r_fires == 0:
                zero_nbr = 'L' if l_fires == 0 else 'R'
                print(f"  CLUSTERING at b={b}, interval {idx}: {zero_nbr} fires 0")
