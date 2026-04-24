"""
Final check: what exactly are the stable triples at K<=5?
And find the exact K threshold where stabilization breaks.
"""
from collections import Counter

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

# Show the 4 stable triples at K<=3
b3 = {}
for n in [9, 10, 11, 12]:
    b3[n] = sorted(t for t in all_results[n] if max(t) <= 3)
print("Triples with all values <= 3:")
for t in b3[9]:
    print(f"  {t}  ->  5-tuple: ({t[0]}, 2, {t[1]}, 2, {t[2]})")

# Show stable triples at K<=5
print("\nTriples with all values <= 5:")
b5 = sorted(t for t in all_results[9] if max(t) <= 5)
for t in b5:
    print(f"  ({t[0]}, 2, {t[1]}, 2, {t[2]})")

# Find exact K where stabilization breaks
print("\nStabilization boundary search:")
for K in range(3, 25):
    bounded = {}
    for n in [9, 10, 11, 12]:
        bounded[n] = set(t for t in all_results[n] if max(t) <= K)
    sizes = [len(bounded[n]) for n in [9, 10, 11, 12]]
    stable = all(s == sizes[0] for s in sizes)
    if not stable or K <= 8:
        print(f"  K={K}: sizes={sizes} {'STABLE' if stable else '*** BREAKS ***'}")

# Why does it break at K=6? What triple appears at n=10 but not n=9?
print("\nFirst breaking triples (at K boundary):")
for K in [6, 7, 8]:
    for n in [10, 11, 12]:
        bounded_n = set(t for t in all_results[n] if max(t) <= K)
        bounded_prev = set(t for t in all_results[n-1] if max(t) <= K)
        new = bounded_n - bounded_prev
        if new:
            print(f"  K={K}, new at n={n}: {sorted(new)[:5]}...")

# Key structural question: what's the max m_t (pivot) given a,c <= 5?
print("\nMax pivot value when neighbors a,c <= 5:")
for n in [9, 10, 11, 12]:
    restricted = set(t for t in all_results[n] if t[0] <= 5 and t[2] <= 5)
    max_b = max(t[1] for t in restricted)
    print(f"  n={n}: max pivot = {max_b}, count = {len(restricted)}")

# Why? Because with small a,c and small remaining, the pivot b can be huge
# The product constraint is: a*2*b*2*c * prod(remaining) < 4*3^(n-2)
# With a=c=2, n-5 remaining all 2's: 2*2*b*2*2 * 2^(n-5) < 4*3^(n-2)
# => b < 4*3^(n-2) / (16 * 2^(n-5)) = 3^(n-2) * 2^(n-3) / 2^(n-1) = 3^(n-2)/4... wait
# 16 * 2^(n-5) = 2^4 * 2^(n-5) = 2^(n-1)
# b < 4*3^(n-2)/2^(n-1) = 2 * (3/2)^(n-2)
# n=9: b < 2*(3/2)^7 = 2*17.09 = 34.17 -> max b=34 CHECK
# n=12: b < 2*(3/2)^10 = 2*57.67 = 115.33 -> max b=115 CHECK
print("\nPredicted max pivot (all-binary rest): 2*(3/2)^(n-2)")
for n in [9, 10, 11, 12]:
    pred = 2 * (1.5)**(n-2)
    print(f"  n={n}: predicted max = {pred:.1f}, actual = {max(t[1] for t in all_results[n])}")
