#!/usr/bin/env python3
"""
N=9 Gap Products: Enumerate ALL achievable products in (7776, 8748) with ≥3 binary.

If M_9 = 8748, we need ALL these to fail. Understanding their structure
tells us what the proof must handle.
"""

from itertools import combinations_with_replacement
from math import prod
from collections import Counter


def enum_multisets_in_range(n, lo, hi, min_binary=3):
    """Find all multisets of n integers ≥2 with product in (lo, hi) and ≥min_binary 2s."""
    results = []

    def search(remaining, min_val, current, current_prod):
        if remaining == 0:
            if lo < current_prod < hi:
                num_2 = sum(1 for x in current if x == 2)
                if num_2 >= min_binary:
                    results.append(tuple(sorted(current)))
            return
        # Upper bound on next value
        max_val = hi // current_prod + 1 if current_prod > 0 else hi
        for v in range(min_val, min(max_val + 1, hi)):
            new_prod = current_prod * v
            if new_prod >= hi and remaining > 1:
                break  # Product already too large with more to add
            # Lower bound check: can we still reach > lo?
            # Remaining entries are ≥ v, so min remaining product = v^remaining
            min_future = v ** (remaining - 1)
            if new_prod * min_future >= hi:
                break
            search(remaining - 1, v, current + [v], new_prod)

    search(n, 2, [], 1)
    # Deduplicate
    return sorted(set(results))


print("=" * 70)
print("GAP PRODUCTS: ALL multisets with product in (7776, 8748) and ≥3 binary")
print("=" * 70)
print()

gap_multisets = enum_multisets_in_range(9, 7776, 8748, min_binary=3)
print(f"Found {len(gap_multisets)} multisets:")
print()

# Group by product
from collections import defaultdict
by_product = defaultdict(list)
for ms in gap_multisets:
    by_product[prod(ms)].append(ms)

for p in sorted(by_product.keys()):
    print(f"Product {p}:")
    for ms in by_product[p]:
        num_2 = sum(1 for x in ms if x == 2)
        non_2 = [x for x in ms if x != 2]
        print(f"  {ms}  — {num_2} binary, non-binary: {non_2}")
    print()

print(f"Total distinct products in gap: {len(by_product)}")
print(f"Products: {sorted(by_product.keys())}")
print()

# What do all gap products have in common?
# All have ≥3 binary. What's the minimum number of binary procs?
print("Binary count distribution:")
bin_counts = Counter()
for ms in gap_multisets:
    num_2 = sum(1 for x in ms if x == 2)
    bin_counts[num_2] += 1
print(f"  {dict(sorted(bin_counts.items()))}")
print()

# For the M_9 = 8748 proof:
# ALL these must fail. The shadow theorem handles pure {2,3} systems.
# Need to handle mixed systems (with 4, 5, 6, 7, etc.)

# Key question: which gap products have ONLY {2,3} entries?
pure_23 = [ms for ms in gap_multisets if all(x in [2,3] for x in ms)]
mixed = [ms for ms in gap_multisets if not all(x in [2,3] for x in ms)]
print(f"Pure {{2,3}} multisets: {len(pure_23)}")
for ms in pure_23:
    print(f"  {ms}, product={prod(ms)}")
print()
print(f"Mixed multisets (have entry ≥4): {len(mixed)}")
for ms in mixed:
    print(f"  {ms}, product={prod(ms)}")
print()

# CRITICAL: For pure {2,3} with ≥3 binary, the shadow theorem directly applies.
# The shadow cycle is unavoidable → system fails.
# Product with k binary (k≥3): 2^k · 3^(9-k).
# For 2^k · 3^(9-k) < 8748:
#   k=3: 8·19683... wait, 3^6 = 729, 8·729 = 5832. That's < 7776 even!
# So ALL pure {2,3} with ≥3 binary have product ≤ 5832 < 7776.
# They're already below the gap range!
print("Pure {2,3} products with ≥3 binary at n=9:")
for k in range(3, 10):
    p = (2**k) * (3**(9-k))
    print(f"  k={k} binary: 2^{k} · 3^{9-k} = {p}")
print()
print("ALL pure {2,3} with ≥3 binary have product ≤ 5832 < 7776.")
print("The shadow theorem already handles these (they're below the minimum).")
print()
print("Therefore: ALL gap products (7777-8747) are MIXED (have entry ≥4).")
print("The M_9 ≥ 8748 proof requires showing mixed ≥3-binary systems fail too.")
print()

# Classify the mixed gap products by their "difficulty"
print("=" * 70)
print("CLASSIFICATION OF MIXED GAP PRODUCTS")
print("=" * 70)
print()

# For each, identify:
# - Number of binary procs
# - Largest state count
# - Shadow cycle length (2n = 18 for all)
# - Whether the shadow theorem can be extended

print("All gap multisets, classified:")
print(f"{'Product':>8} {'Multiset':>40} {'#bin':>4} {'max_m':>5} {'comment'}")
print("-" * 80)

for p in sorted(by_product.keys()):
    for ms in by_product[p]:
        num_2 = sum(1 for x in ms if x == 2)
        max_m = max(ms)
        # Can shadow theorem handle this?
        # Shadow theorem: proven for 3+ binary + all ternary
        # Extended computationally: 4+ binary + quaternary
        # Need: ≥3 binary + mixed
        comment = ""
        if max_m == 4:
            comment = "3+1+rest variant (quaternary)"
        elif max_m == 5:
            comment = "has quinary"
        elif max_m >= 6:
            comment = f"has {max_m}-ary"
        print(f"{p:>8} {str(ms):>40} {num_2:>4} {max_m:>5} {comment}")

print()

# The key insight: gap products fall into categories:
# 1. {2^k, 3^j, 4^l, ...} with one "large" entry replacing ternaries
# 2. Multiple non-ternary entries

# For category 1 (single large entry): the shadow theorem for {2,3,m}
# should work similarly to {2,3,4}. The large entry provides free entries,
# but not enough to break the shadow at n=9.

# For category 2 (multiple large entries): even more free entries available,
# but also more constraints. Likely also fails.

print("=" * 70)
print("PROOF STRUCTURE FOR M_9 ≥ 8748")
print("=" * 70)
print()
print("To prove M_9 ≥ 8748:")
print()
print("Step 1: ≤2 binary → product ≥ 4·3^7 = 8748 (arithmetic). ✓")
print()
print("Step 2: ≥3 binary, pure {2,3} → shadow theorem → product needs")
print("  to be > 5832 (max pure {2,3} with ≥3 binary). Already below 7776. ✓")
print()
print("Step 3: ≥3 binary, mixed → need to show ALL gap products fail.")
print(f"  {len(gap_multisets)} multisets to handle across {len(by_product)} products.")
print()
print("Step 3a: Products ≤ 7776 with ≥3 binary and mixed entries:")
# These are the original product-7776 multisets plus any below
mixed_below = []
for k in range(3, 10):
    # k binary, 9-k non-binary. Product = 2^k × P_{9-k}
    # P_{9-k} = product of 9-k entries, each ≥ 3, at least one ≥ 4
    # Min P_{9-k} with one ≥ 4: 4 · 3^{9-k-1}
    min_mixed = (2**k) * 4 * (3**(9-k-1)) if 9-k >= 1 else 0
    if min_mixed > 0 and min_mixed <= 7776:
        print(f"  k={k}: min mixed product = {min_mixed} (≤7776)")

print()
print("Step 3b: Products in (7776, 8748):")
print(f"  {len(gap_multisets)} multisets as enumerated above.")
print()

# For a complete proof, we'd need the shadow theorem generalized to:
# "For any n=9 system with ≥3 binary and product < 8748, there exists
#  a shadow cycle that cannot be broken."
# This subsumes both Step 2 and Step 3.

print("ALTERNATIVE proof structure (cleaner):")
print()
print("  Theorem: For n ≥ 9, any system with ≥3 binary procs and")
print("  ≤(n-4) non-binary procs of sizes m₁,...,mₖ (mᵢ ≥ 3)")
print("  cannot be self-stabilizing if:")
print("    2^(#binary) · ∏mᵢ < 4 · 3^(n-2)")
print()
print("  Proof idea: the shadow cycle has 2n configs in {0,1}^n.")
print("  Binary procs have ALL transitions determined by any good cycle.")
print("  Non-binary procs have {0,1}-triples that are also likely determined.")
print("  Escape requires free entries (S ≥ 2 at non-binary procs).")
print("  But escape interference prevents simultaneous breaking of ALL")
print("  shadow constraints AND convergence of escape configs.")
print()
print("  The threshold 4·3^(n-2) arises because that's the minimum product")
print("  with ≤2 binary, and systems with ≤2 binary don't have shadows.")
print()

# Verification: compute 4·3^(n-2) vs max ≥3-binary product that works
print("Verification across n:")
for n in range(5, 13):
    case_a = 32 * 3**(n-4)
    case_b = 4 * 3**(n-2)
    max_pure_23 = 8 * 3**(n-3)  # 3 binary + rest ternary
    print(f"  n={n}: 32·3^(n-4)={case_a:>10}, 4·3^(n-2)={case_b:>10}, "
          f"max_pure_23={max_pure_23:>10}, "
          f"works={'✓' if n <= 8 else '?'}")
