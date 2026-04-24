"""
Follow-up: identify the 2 "always good" multisets and examine k>=2 bad examples.
"""

from itertools import permutations
from functools import reduce
from operator import mul

n = 9
threshold = 4 * 3**7  # = 8748

def enum_multisets():
    results = []
    max_val = threshold // (2**8)
    def backtrack(remaining, min_val, current, prod):
        if remaining == 0:
            num_binary = current.count(2)
            if num_binary >= 3 and prod < threshold:
                results.append(tuple(sorted(current)))
            return
        for v in range(min_val, max_val + 1):
            new_prod = prod * v
            if new_prod >= threshold:
                break
            if new_prod * (2 ** (remaining - 1)) >= threshold and v > 2:
                break
            backtrack(remaining - 1, v, current + [v], new_prod)
    backtrack(n, 2, [], 1)
    return results

multisets = enum_multisets()

def check_arrangement(ring):
    nn = len(ring)
    has_sandwiched_pivot = False
    for t in range(nn):
        if ring[t] >= 3:
            left = ring[(t-1) % nn]
            right = ring[(t+1) % nn]
            if left == 2 and right == 2:
                has_sandwiched_pivot = True
                left2 = ring[(t-2) % nn]
                right2 = ring[(t+2) % nn]
                if left2 > 2 or right2 > 2:
                    return "HAS_GOOD_PIVOT"
    if not has_sandwiched_pivot:
        return "NO_SANDWICHED_PIVOT"
    return "ALL_PIVOTS_BAD"

always_good = []
k2_bad = []

for ms in multisets:
    items = list(ms)
    non_binary = [x for x in items if x > 2]
    k = len(non_binary)
    prod = reduce(mul, items)

    if k <= 1:
        continue

    found_bad = False
    found_good = False
    bad_ring = None

    seen = set()
    for p in permutations(items):
        canonical = min(p[i:] + p[:i] for i in range(n))
        if canonical in seen:
            continue
        seen.add(canonical)

        result = check_arrangement(list(p))
        if result == "ALL_PIVOTS_BAD":
            found_bad = True
            bad_ring = list(p)
        if result == "HAS_GOOD_PIVOT":
            found_good = True

    if not found_bad and found_good:
        always_good.append((ms, prod))
    elif found_bad:
        k2_bad.append((ms, prod, bad_ring, k))

print("ALWAYS GOOD multisets (k>=2, every arrangement with pivots has a good one):")
for ms, prod in always_good:
    non_binary = [x for x in ms if x > 2]
    print(f"  {ms}, product={prod}, non-binary={non_binary}")
print()

print(f"k>=2 BAD multisets: {len(k2_bad)}")
print("\nExamples with k=2 (fewest non-binary):")
for ms, prod, ring, k in k2_bad:
    if k == 2:
        print(f"  multiset={ms}, product={prod}")
        print(f"  ring={ring}")
        for t in range(n):
            if ring[t] >= 3:
                L = ring[(t-1)%n]; R = ring[(t+1)%n]
                if L == 2 and R == 2:
                    L2 = ring[(t-2)%n]; R2 = ring[(t+2)%n]
                    print(f"    pivot at {t}: ...{L2},{L},{ring[t]},{R},{R2}...")
        print()

print("\nExamples with k=3:")
count = 0
for ms, prod, ring, k in k2_bad:
    if k == 3 and count < 10:
        print(f"  multiset={ms}, product={prod}")
        print(f"  ring={ring}")
        for t in range(n):
            if ring[t] >= 3:
                L = ring[(t-1)%n]; R = ring[(t+1)%n]
                if L == 2 and R == 2:
                    L2 = ring[(t-2)%n]; R2 = ring[(t+2)%n]
                    print(f"    pivot at {t}: ...{L2},{L},{ring[t]},{R},{R2}...")
        print()
        count += 1

# Distribution by k
from collections import Counter
k_dist = Counter(k for _, _, _, k in k2_bad)
print(f"\nk>=2 bad by number of non-binary: {dict(sorted(k_dist.items()))}")

# Key structural observation
print("\n" + "="*60)
print("STRUCTURAL ANALYSIS")
print("="*60)
print()
print("For k>=2 bad arrangements, what patterns appear?")
for ms, prod, ring, k in k2_bad[:5]:
    print(f"  ring={ring}")
    # Show binary/non-binary pattern
    pattern = ['B' if x == 2 else 'T' for x in ring]
    print(f"  pattern={''.join(pattern)}")
    # Show run structure
    runs = []
    i = 0
    while i < n:
        j = i
        while j < n and (ring[j] == 2) == (ring[i] == 2):
            j += 1
        runs.append(('B' if ring[i] == 2 else 'T', j - i))
        i = j
    print(f"  runs={runs}")
    print()
