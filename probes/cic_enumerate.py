"""
CIC Exploration 1: Enumerate all candidate state vectors at n=9
with product < 8748 = 4*3^7, at least 3 binary, at most 3 consecutive binary,
at least one m_i >= 4.
"""

from itertools import combinations_with_replacement
from math import prod
from collections import Counter

N = 9
TARGET = 4 * 3**7  # 8748

def enumerate_multisets(n, target):
    """Enumerate all multisets of n values, each >= 2, with product < target,
    at least 3 values equal to 2, at least one value >= 4."""
    results = []

    # We enumerate by choosing:
    # k = number of binary (value=2) processors, k in {3,...,n}
    # Then fill the remaining n-k slots with values >= 3, at least one >= 4

    for k in range(3, n+1):
        # Product from binary part
        binary_product = 2**k
        if binary_product >= target:
            break

        remaining_budget = target / binary_product
        remaining_count = n - k

        if remaining_count == 0:
            # All binary — no room for m_i >= 4, skip
            continue

        # Enumerate multisets of remaining_count values, each >= 3, at least one >= 4
        # with product < remaining_budget
        for ms_rest in enum_multisets_recursive(remaining_count, 3, remaining_budget, must_have_ge4=True):
            multiset = tuple(sorted([2]*k + list(ms_rest)))
            total_product = binary_product * prod(ms_rest)
            results.append((multiset, total_product, k))

    return results

def enum_multisets_recursive(count, min_val, budget, must_have_ge4=False, current=None):
    """Generate all sorted tuples of 'count' values >= min_val with product < budget.
    If must_have_ge4, at least one value must be >= 4."""
    if current is None:
        current = []

    if count == 0:
        if must_have_ge4 and all(v < 4 for v in current):
            return
        yield tuple(current)
        return

    val = min_val
    while True:
        if val >= budget:
            break
        new_budget = budget / val
        if count > 1 and val**(count-1) >= budget:
            # Even filling all remaining with val exceeds budget
            # But we should still try this val with smaller remaining
            pass

        # Check if product of remaining (count-1) values at minimum (which is val) fits
        if val**(count) >= budget * val:
            # This val alone fills too much
            break

        yield from enum_multisets_recursive(count-1, val, new_budget, must_have_ge4, current + [val])
        val += 1

def max_consecutive_binary(arrangement):
    """Given a ring arrangement, find max consecutive run of 2s."""
    n = len(arrangement)
    if all(v == 2 for v in arrangement):
        return n

    # Find first non-2
    start = None
    for i in range(n):
        if arrangement[i] != 2:
            start = i
            break

    max_run = 0
    current_run = 0
    for j in range(n):
        idx = (start + j) % n
        if arrangement[idx] == 2:
            current_run += 1
            max_run = max(max_run, current_run)
        else:
            current_run = 0

    return max_run

def can_place_with_consecutive_le3(multiset, n):
    """Check if this multiset can be arranged on a ring of size n
    such that max consecutive binary run <= 3."""
    k = multiset.count(2)
    non_binary_count = n - k

    if non_binary_count == 0:
        return k <= 3  # all binary, only ok if n <= 3

    # With non_binary_count non-binary processors creating non_binary_count arcs,
    # we need to distribute k binary into arcs of size <= 3.
    # This is possible iff k <= 3 * non_binary_count.
    return k <= 3 * non_binary_count

def count_valid_orientations(multiset, n):
    """Count distinct ring arrangements (up to rotation) with max consecutive binary <= 3."""
    from itertools import permutations

    # For small cases, enumerate all distinct necklaces
    # For now, just check if placement is possible
    return can_place_with_consecutive_le3(multiset, n)

# Main enumeration
print(f"Enumerating candidate multisets for n={N}, product < {TARGET}")
print(f"Constraints: ≥3 binary, at least one m_i ≥ 4, ≤3 consecutive binary possible")
print()

candidates = enumerate_multisets(N, TARGET)

# Filter: must be placeable with ≤3 consecutive binary
valid_candidates = []
for multiset, product, k_binary in candidates:
    if can_place_with_consecutive_le3(multiset, N):
        valid_candidates.append((multiset, product, k_binary))

# Sort by product
valid_candidates.sort(key=lambda x: x[1])

# Display results grouped by binary count
print(f"Total candidate multisets: {len(valid_candidates)}")
print()

for k in range(3, N+1):
    group = [(ms, p) for ms, p, kb in valid_candidates if kb == k]
    if group:
        print(f"=== k={k} binary processors ({len(group)} multisets) ===")
        for ms, p in group:
            non_binary = [v for v in ms if v > 2]
            print(f"  ms={ms}  product={p}  non-binary={non_binary}")
        print()

# Summary statistics
print("=== SUMMARY ===")
print(f"Total multisets to kill: {len(valid_candidates)}")
products = sorted(set(p for _, p, _ in valid_candidates))
print(f"Distinct products: {len(products)}")
print(f"Product range: [{min(products)}, {max(products)}]")
print()

# Check which are already killed by known results
print("=== STATUS CHECK ===")
# M_9 > 7776 is proved
killed_by_m9 = [(ms, p, k) for ms, p, k in valid_candidates if p <= 7776]
surviving = [(ms, p, k) for ms, p, k in valid_candidates if p > 7776]
print(f"Killed by M_9 > 7776: {len(killed_by_m9)} multisets")
print(f"Surviving (product in [7777, 8747]): {len(surviving)} multisets")
for ms, p, k in surviving:
    non_binary = [v for v in ms if v > 2]
    print(f"  ms={ms}  product={p}  k={k}  non-binary={non_binary}")
