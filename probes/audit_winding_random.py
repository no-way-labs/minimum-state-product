"""Random sampling to classify cycles by winding class.

Focused on the three multisets I need to understand:
  - all-odd-gap (2,3,3,2,3,3,2,3,3): non-pivot non-3CB
  - pivot layout (2,3,2,3,3,3,3,3,3): has pivot but no 3CB
  - all-binary (2,2,2,2,2,2,2,2,2): degenerate, fc=2 possible
"""
from collections import Counter
import random

random.seed(2026)
N = 9

def left(p, n=N): return (p - 1) % n
def right(p, n=N): return (p + 1) % n

def is_valid_good_cycle(word, ms, n):
    CL = len(word)
    fc = [0] * n
    for m in word:
        fc[m] += 1
    if not all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
        return None
    for k in range(CL):
        a, b = word[k], word[(k + 1) % CL]
        if b not in (a, left(a, n), right(a, n)):
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

def classify(word, n):
    CL = len(word)
    cw = sum(1 for k in range(CL) if word[(k + 1) % CL] == right(word[k], n))
    ccw = sum(1 for k in range(CL) if word[(k + 1) % CL] == left(word[k], n))
    stay = CL - cw - ccw
    if ccw == 0 and cw > 0:
        return "sweep-cw"
    if cw == 0 and ccw > 0:
        return "sweep-ccw"
    if cw == ccw:
        return "zw-cw0" if cw == 0 else "zw-cwpos"
    return "odd-winding"

def has_pivot(ms, n):
    return any(ms[p] == 3 and ms[left(p, n)] == 2 and ms[right(p, n)] == 2 for p in range(n))

def has_3cb(ms, n):
    return any(ms[p] == 2 and ms[right(p, n)] == 2 and ms[right(right(p, n), n)] == 2 for p in range(n))

def has_min_fc3(ms, n):
    return any(m == 3 for m in ms)  # ternary → fc≥3 forced

MULTISETS = [
    ("pivot-nopivot-3CB",   [2, 3, 2, 3, 3, 3, 3, 3, 3]),
    ("all-odd-gap",         [2, 3, 3, 2, 3, 3, 2, 3, 3]),
    ("all-binary",          [2, 2, 2, 2, 2, 2, 2, 2, 2]),
]

for label, ms in MULTISETS:
    product = 1
    for m in ms:
        product *= m
    min_cl = sum(ms)
    print(f"\n{'='*70}")
    print(f"{label}: ms={ms}")
    print(f"  product={product}, subthreshold={product < 8748}")
    print(f"  has_3cb={has_3cb(ms, N)}, has_pivot={has_pivot(ms, N)}, min_fc3_forced={has_min_fc3(ms, N)}")
    print(f"  min CL = {min_cl}")
    print('=' * 70)

    classes = Counter()
    total = 0
    trials = 5_000_000
    for _ in range(trials):
        # Random CL in [min_cl, 3*min_cl] or fixed min_cl
        cl = random.choice([min_cl, min_cl + 2, 2 * min_cl])
        word = [random.randint(0, N - 1)]
        for _ in range(cl - 1):
            curr = word[-1]
            word.append(random.choice([left(curr), curr, right(curr)]))
        fc = is_valid_good_cycle(word, ms, N)
        if fc is None:
            continue
        total += 1
        cls = classify(word, N)
        classes[(cls, len(word))] += 1

    print(f"  {total} good cycles found in {trials} trials")
    for (cls, cl), cnt in classes.most_common(10):
        print(f"    {cls:15s} CL={cl:3d}: {cnt}")
