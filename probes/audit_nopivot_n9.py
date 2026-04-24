"""Session 1 audit: scope contradiction for non-pivot non-consec n=9.

Target family: ms = [2,3,3,2,3,3,2,3,3] at n=9.
Product = 5832 < 4*3^7 = 8748 (sub-threshold).

Questions:
1. Sandwiched ternaries? (If none, BinSCC 4-mech cannot apply.)
2. 3 consecutive binary? (If none, CIC Expl 14 cannot apply directly.)
3. Do valid ZW+cw>0+fc=2 good cycles exist in this system?
4. Does the clustering/provider-interval route close ZW+cw>0+fc>=3 cases here?
"""
from collections import Counter
import random

random.seed(2026)

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]

def left(p, n=N): return (p - 1) % n
def right(p, n=N): return (p + 1) % n

# Q1
sandwiched = [p for p in range(N) if MS[p] == 3 and MS[left(p)] == 2 and MS[right(p)] == 2]
print(f"Q1. Sandwiched ternaries in {MS}: {sandwiched}")

# Q2
has_3cb = any(MS[p] == 2 and MS[right(p)] == 2 and MS[right(right(p))] == 2 for p in range(N))
print(f"Q2. Has 3 consecutive binary: {has_3cb}")

binary = [p for p in range(N) if MS[p] == 2]
gaps = []
for i, b in enumerate(binary):
    nxt = binary[(i + 1) % len(binary)]
    gaps.append((nxt - b) % N)
print(f"     Binary: {binary}, gaps: {gaps}")

# Q3/Q4
def is_valid_mover_word(word, ms, n):
    CL = len(word)
    fc = [0] * n
    for m in word:
        fc[m] += 1
    if not all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
        return None
    if not all(fc[p] % 2 == 0 for p in range(n) if ms[p] == 2):
        return None
    for k in range(CL):
        a, b = word[k], word[(k + 1) % CL]
        if b not in (a, left(a, n), right(a, n)):
            return None
    cw = sum(1 for k in range(CL) if word[(k + 1) % CL] == right(word[k], n))
    ccw = sum(1 for k in range(CL) if word[(k + 1) % CL] == left(word[k], n))
    if cw != ccw or cw == 0:
        return None
    cfg = [0] * n
    configs = [tuple(cfg)]
    for m in word:
        cfg[m] = (cfg[m] + 1) % ms[m]
        configs.append(tuple(cfg))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:CL])) != CL:
        return None
    return fc

CL_target = 2 * N
found_fc2 = 0
found_fc_any = 0
fc_shapes = Counter()
trials = 2_000_000
for _ in range(trials):
    word = [random.randint(0, N - 1)]
    for _ in range(CL_target - 1):
        curr = word[-1]
        word.append(random.choice([left(curr), curr, right(curr)]))
    fc = is_valid_mover_word(word, MS, N)
    if fc is None:
        continue
    found_fc_any += 1
    if all(f == 2 for f in fc):
        found_fc2 += 1
    fc_shapes[tuple(fc)] += 1

print(f"\nQ3. {trials} random CL={CL_target} trials in {MS}:")
print(f"     valid good cycles: {found_fc_any}")
print(f"     with all fc=2:    {found_fc2}")
print(f"     top fc shapes:    {fc_shapes.most_common(5)}")

# Now longer cycles (fc>=3 case)
found_long = 0
for _ in range(trials):
    cl = random.randint(CL_target + 2, 3 * N)
    word = [random.randint(0, N - 1)]
    for _ in range(cl - 1):
        curr = word[-1]
        word.append(random.choice([left(curr), curr, right(curr)]))
    fc = is_valid_mover_word(word, MS, N)
    if fc is None:
        continue
    if any(f >= 3 for f in fc):
        found_long += 1

print(f"\nQ4. {trials} random CL in [{CL_target+2}, {3*N}] trials in {MS}:")
print(f"     valid with some fc>=3: {found_long}")
