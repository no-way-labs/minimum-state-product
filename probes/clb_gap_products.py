#!/usr/bin/env python3
"""clb_gap_products.py — Find all multisets with product in (7776, 8748) for n=9.

Since M_9 > 7776 (known) and M_9 ≤ 8748 (just proved), M_9 is exactly determined
ONLY IF no multiset has product in (7776, 8748). Find and list all such multisets.
"""

from itertools import combinations_with_replacement


def find_gap_multisets(n, lo, hi):
    """Find all multisets of n values, each ≥ 2, with product strictly in (lo, hi)."""
    results = []

    def search(vals, remaining, max_val, current_product):
        if remaining == 0:
            if lo < current_product < hi:
                results.append(tuple(sorted(vals)))
            return
        # Prune: minimum remaining product = 2^remaining
        if current_product * (2 ** remaining) > hi:
            return
        # Prune: even if all remaining are at max, product too small
        # max_remaining_product: difficult to compute, skip
        for v in range(2, max_val + 1):
            new_product = current_product * v
            if new_product >= hi * (2 ** (remaining - 1)):
                break  # all larger v will also exceed
            search(vals + [v], remaining - 1, v, new_product)

    # Try values up to a reasonable max
    max_single = hi // (2 ** (n - 1))  # upper bound on any single value
    search([], n, max_single + 1, 1)
    return sorted(set(results))


n = 9
lo = 7776
hi = 8748

print(f"Finding multisets with n={n}, product in ({lo}, {hi})...")

# More efficient: enumerate by decomposition
results = []

def dfs(pos, remaining, current_product, min_val, vals):
    if pos == n:
        if lo < current_product < hi:
            results.append(tuple(vals[:]))
        return
    left = n - pos
    # Minimum remaining product: min_val^left
    if current_product * (min_val ** left) >= hi:
        return
    # Maximum remaining product: need current_product * max_val^left > lo
    # min needed: lo / current_product, each remaining ≥ this^(1/left)
    if current_product * (100 ** left) <= lo:
        return

    max_v = hi // max(1, current_product)
    for v in range(min_val, min(max_v + 1, 50)):
        new_prod = current_product * v
        if new_prod * (v ** (left - 1)) < lo:
            continue  # even all remaining = v won't reach lo
        if new_prod * (2 ** (left - 1)) >= hi and v > min_val:
            break  # exceeds hi even with minimum remaining
        vals.append(v)
        dfs(pos + 1, left - 1, new_prod, v, vals)
        vals.pop()


dfs(0, n, 1, 2, [])
results = sorted(set(tuple(sorted(r)) for r in results))

print(f"\nFound {len(results)} multisets with product in ({lo}, {hi}):")
for ms in results:
    product = 1
    for m in ms:
        product *= m
    # Count binary processors
    n_bin = sum(1 for m in ms if m == 2)
    print(f"  {ms} product={product} ({n_bin} binary)")

if not results:
    print(f"\nNO multisets exist with product in ({lo}, {hi})!")
    print(f"Therefore M_9 = {hi} = 4·3^7.")
else:
    print(f"\n{len(results)} multisets need to be checked/eliminated")
    print(f"to determine if M_9 < {hi}.")
