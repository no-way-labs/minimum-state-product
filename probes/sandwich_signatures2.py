"""
Follow-up: check if signatures stabilize when we bound the pivot and neighbor values.
Also check max values appearing at each n.
"""
from collections import Counter
from itertools import combinations_with_replacement

def enum_multisets(n, max_product):
    results = []
    def backtrack(remaining, min_val, current, current_product):
        if remaining == 0:
            if current_product < max_product and current.count(2) >= 3:
                results.append(tuple(current))
            return
        max_val = max_product // (current_product * (2 ** (remaining - 1)))
        if max_val < min_val:
            return
        for v in range(min_val, max_val + 1):
            new_product = current_product * v
            if new_product * (2 ** (remaining - 1)) >= max_product:
                break
            backtrack(remaining - 1, v, current + [v], new_product)
    backtrack(n, 2, [], 1)
    return results

def get_triples_from_multiset(ms):
    n = len(ms)
    if n < 5:
        return set()
    counter = Counter(ms)
    triples = set()
    distinct_b = set(v for v in counter if v >= 3)
    for b in distinct_b:
        temp = Counter(counter)
        temp[b] -= 1
        if temp[b] < 0:
            continue
        if temp[2] < 2:
            continue
        temp[2] -= 2
        remaining = []
        for v, cnt in sorted(temp.items()):
            if cnt > 0:
                remaining.extend([v] * cnt)
        if len(remaining) < 2:
            continue
        rem_counter = Counter(remaining)
        distinct_rem = sorted(rem_counter.keys())
        for a in distinct_rem:
            for c in distinct_rem:
                if a == c:
                    if rem_counter[a] >= 2:
                        triples.add((a, b, c))
                else:
                    triples.add((a, b, c))
    return triples

all_results = {}
for n in [9, 10, 11, 12]:
    threshold = 4 * (3 ** (n - 2))
    multisets = enum_multisets(n, threshold)
    all_triples = set()
    for ms in multisets:
        all_triples.update(get_triples_from_multiset(ms))
    all_results[n] = all_triples

    # Compute max values
    max_a = max(t[0] for t in all_triples)
    max_b = max(t[1] for t in all_triples)
    max_c = max(t[2] for t in all_triples)
    print(f"n={n}: {len(all_triples)} triples, max(a)={max_a}, max(b)={max_b}, max(c)={max_c}, threshold={threshold}")

# Check monotonicity
for n in [10, 11, 12]:
    prev = n - 1
    new = all_results[n] - all_results[prev]
    lost = all_results[prev] - all_results[n]
    print(f"n={prev}->{n}: +{len(new)} new, -{len(lost)} lost")

# Check bounded triples: restrict to a,b,c <= K for various K
print("\nBounded stabilization check:")
for K in [3, 5, 10, 15, 20, 22]:
    bounded = {}
    for n in [9, 10, 11, 12]:
        bounded[n] = set(t for t in all_results[n] if t[0] <= K and t[1] <= K and t[2] <= K)
    sizes = [len(bounded[n]) for n in [9, 10, 11, 12]]
    stable = all(s == sizes[0] for s in sizes)
    print(f"  max value <= {K}: sizes={sizes}, {'STABLE' if stable else 'NOT STABLE'}")

# The real question: for SMALL pivot values (b=3), what a,c pairs appear?
print("\nFor b=3 (ternary pivot):")
for n in [9, 10, 11, 12]:
    b3 = sorted(t for t in all_results[n] if t[1] == 3)
    max_a = max(t[0] for t in b3)
    max_c = max(t[2] for t in b3)
    print(f"  n={n}: {len(b3)} triples, max(a)={max_a}, max(c)={max_c}")

# What's the max b (pivot value) that appears?
print("\nDistinct pivot values m_t at each n:")
for n in [9, 10, 11, 12]:
    pivots = sorted(set(t[1] for t in all_results[n]))
    print(f"  n={n}: {pivots}")
