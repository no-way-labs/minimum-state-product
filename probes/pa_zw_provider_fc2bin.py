"""
Analyze the all-binary-fc=2 cases.
In these: every binary fires exactly 2 times. CL > 2n.
Some ternary fires >= 3.

Binary b fires 2 times: 2 intervals.
Each neighbor i fires fc(i) >= 2 total in these 2 intervals.
For "zero i between b-fires": one of the 2 intervals has i firing 0.
This requires fc(i) fires to be concentrated in ONE interval of b.
With fc(i) >= 2, that's possible.

The question: DOES it happen for some (b, i)?

Binary b: 2 fires at s1, s2. Two intervals: (s1, s2) and (s2, s1+CL).
Lengths: L1 = s2 - s1, L2 = CL - L1.

left(b) fires F_L times. If F_L in interval 1 = a and interval 2 = F_L - a.
"zero left in some interval" iff a = 0 or a = F_L.

right(b) fires F_R times. "zero right in some interval" iff r = 0 or r = F_R.

We need: for SOME b, SOME neighbor i, i fires 0 in some interval.

For all-binary-fc=2 cases, let's look at the structure.
"""
import random
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

n = 9
moduli = [2, 2, 2, 3, 3, 3, 3, 3, 3]

examples = []
for trial in range(2000000):
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

        bin_fcs = [fc[p] for p in range(n) if moduli[p] == 2]
        if all(f == 2 for f in bin_fcs):
            examples.append((word, fc))
            if len(examples) >= 50:
                break

print(f"Found {len(examples)} all-binary-fc=2 examples")

for word, fc in examples[:5]:
    CL = len(word)
    print(f"\nfc={fc}, CL={CL}")

    for b in range(n):
        if moduli[b] != 2: continue
        fire_steps_b = [k for k in range(CL) if word[k] == b]
        s1, s2 = fire_steps_b[0], fire_steps_b[1]

        # Two intervals
        for i in [left(b, n), right(b, n)]:
            # Count i fires in interval 1: (s1, s2)
            i_in_1 = sum(1 for k in range(s1+1, s2) if word[k] == i)
            # Count i fires in interval 2: (s2, s1+CL)
            i_in_2 = sum(1 for k in range(s2+1, s1+CL) if word[k % CL] == i)

            zero_exists = (i_in_1 == 0 or i_in_2 == 0)
            side = "L" if i == left(b, n) else "R"
            mark = " ***" if zero_exists else ""
            print(f"  b={b}, {side}={i}: in_int1={i_in_1}, in_int2={i_in_2}{mark}")
