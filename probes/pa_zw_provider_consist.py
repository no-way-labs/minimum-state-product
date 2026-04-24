"""
Check if "every binary b fires at most 1 in every neighbor interval"
is self-consistent with the other constraints.

The constraint: for each binary b and each neighbor i of b,
fc(b) <= fc(i).

With 3 binary at 0,1,2 and n=5: non-binary at 3,4.
Neighbors of 0: 4, 1. Constraint: fc(0) <= fc(4), fc(0) <= fc(1).
Neighbors of 1: 0, 2. Constraint: fc(1) <= fc(0), fc(1) <= fc(2).
Neighbors of 2: 1, 3. Constraint: fc(2) <= fc(1), fc(2) <= fc(3).

From (1 <= 0) and (0 <= 1): fc(0) = fc(1).
From (1 <= 2) and (2 <= 1): fc(1) = fc(2).
So fc(0) = fc(1) = fc(2) = F (say).

And F <= fc(3), F <= fc(4).
Total = 3F + fc(3) + fc(4) = CL > 2*5 = 10.
3F + fc(3) + fc(4) >= 3*2 + 2 + 2 = 10. Need > 10, so >= 11.
fc(3) >= F, fc(4) >= F.
Total >= 3F + F + F = 5F >= 10, so F >= 2.
Need some fc >= 3. If F = 2: total >= 10 + (fc(3)-F) + (fc(4)-F) = 10 + ... >= 10.
Need > 10. So fc(3) + fc(4) > 4. At least one >= 3.

Under "max b fires in any interval <= 1":
Each interval of i has b fires <= 1, so fc(b) <= fc(i).
For i = 3: fc(2) <= fc(3). So fc(3) >= F.
For i = 4: fc(0) <= fc(4). So fc(4) >= F.

If F = 2: fc(3), fc(4) >= 2, and some fc >= 3.
If fc(3) = 3: total = 6 + 3 + fc(4) >= 6+3+2 = 11 > 10. Feasible.

So the "max 1" assumption IS consistent with the constraints!
But the EC mechanism still works 100% in these cases.
That means even when max_b = 1 for ALL (b, side) pairs... wait,
we already showed that doesn't happen!

Let me verify: does "max_b <= 1 for ALL binary b, ALL sides" ever happen?
"""
import random
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

n = 5
moduli = [2, 2, 2, 3, 3]
found_all_max1 = 0
total = 0

for trial in range(1000000):
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
        total += 1

        all_max1 = True
        for b in range(n):
            if moduli[b] != 2: continue
            if not all_max1: break
            for i in [right(b, n), left(b, n)]:
                fire_steps_i = [k for k in range(CL) if word[k] == i]
                if len(fire_steps_i) < 2: continue
                for idx in range(len(fire_steps_i)):
                    a1 = fire_steps_i[idx]
                    a2_raw = fire_steps_i[(idx + 1) % len(fire_steps_i)]
                    if a2_raw <= a1: a2_raw += CL
                    gap = list(range(a1+1, a2_raw))
                    b_in = sum(1 for k in gap if word[k % CL] == b)
                    if b_in >= 2:
                        all_max1 = False
                        break
                if not all_max1: break

        if all_max1:
            found_all_max1 += 1

print(f"Total valid: {total}, ALL max<=1: {found_all_max1}")
print("(If found_all_max1 > 0, the 'always exists >= 2' claim is FALSE for Part 1)")
print("(But the EC mechanism can still work through a DIFFERENT mechanism)")
