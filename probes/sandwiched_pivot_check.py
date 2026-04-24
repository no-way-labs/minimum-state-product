"""
Check: for sub-threshold state vectors at n=9 with >=3 binary,
does every arrangement have at least one sandwiched ternary pivot
with a non-binary second-neighbor?

A sandwiched ternary pivot t has: m(t)>=3, m(left)=2, m(right)=2.
We check if second-neighbors (left^2, right^2) include a non-binary.
"""

from itertools import permutations
from functools import reduce
from operator import mul

n = 9
threshold = 4 * 3**7  # = 8748

# Enumerate all multisets with product < threshold, each m_i >= 2, >=3 binary
def enum_multisets():
    results = []
    max_val = threshold // (2**8)  # ~34

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
print(f"Total sub-threshold multisets with >=3 binary: {len(multisets)}")

def check_arrangement(ring):
    """Check arrangement status."""
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

print("\nRunning brute-force check on all multisets...\n")

results_summary = {"always_good": 0, "has_bad": 0, "no_pivots_possible": 0, "vacuous_only": 0}
bad_examples = []

for idx, ms in enumerate(multisets):
    items = list(ms)
    non_binary = [x for x in items if x > 2]
    k = len(non_binary)
    prod = reduce(mul, items)

    if k == 0:
        results_summary["no_pivots_possible"] += 1
        continue

    if k == 1:
        # Single non-binary always sandwiched, always has binary 2nd-neighbors
        results_summary["has_bad"] += 1
        bad_examples.append((ms, list(items), f"k=1: single non-binary always sandwiched with binary 2nd-nbrs"))
        continue

    # k >= 2: enumerate distinct circular arrangements
    found_bad_with_pivots = False
    all_vacuous = True
    bad_ring = None

    seen = set()
    for p in permutations(items):
        canonical = min(p[i:] + p[:i] for i in range(n))
        if canonical in seen:
            continue
        seen.add(canonical)

        result = check_arrangement(list(p))
        if result == "ALL_PIVOTS_BAD":
            found_bad_with_pivots = True
            bad_ring = list(p)
            all_vacuous = False
            break  # found one, enough
        elif result == "HAS_GOOD_PIVOT":
            all_vacuous = False

    if found_bad_with_pivots:
        results_summary["has_bad"] += 1
        bad_examples.append((ms, bad_ring, f"k={k}: arrangement with all-bad sandwiched pivots"))
    elif all_vacuous:
        results_summary["vacuous_only"] += 1
    else:
        results_summary["always_good"] += 1

    if (idx + 1) % 20 == 0:
        print(f"  processed {idx+1}/{len(multisets)} multisets...")

print(f"\nResults summary:")
print(f"  No pivots possible (all binary): {results_summary['no_pivots_possible']}")
print(f"  Always good (every arr with pivots has a good one): {results_summary['always_good']}")
print(f"  Has bad arrangement (with sandwiched pivots, all bad): {results_summary['has_bad']}")
print(f"  Vacuous only (no arrangement has sandwiched pivots): {results_summary['vacuous_only']}")

print(f"\n{'='*60}")
print(f"BAD EXAMPLES (first 30):")
print(f"{'='*60}\n")

for ms, ring, reason in bad_examples[:30]:
    prod = reduce(mul, ms)
    print(f"  multiset={ms}, product={prod}")
    print(f"  ring={ring}")
    print(f"  reason: {reason}")
    if isinstance(ring, list):
        for t in range(n):
            if ring[t] >= 3:
                L = ring[(t-1)%n]; R = ring[(t+1)%n]
                if L == 2 and R == 2:
                    L2 = ring[(t-2)%n]; R2 = ring[(t+2)%n]
                    print(f"    pivot at {t}: ...{L2},{L},{ring[t]},{R},{R2}...")
    print()

print(f"\nTotal bad multisets: {len(bad_examples)} / {len(multisets)}")

# Also: how many multisets have k>=2 non-binary AND can avoid sandwiched pivots?
print(f"\n{'='*60}")
print("SEPARATE QUESTION: among multisets with >=2 non-binary,")
print("can we ALWAYS find an arrangement WITH a good sandwiched pivot?")
print(f"{'='*60}\n")

k2plus = [ms for ms in multisets if sum(1 for x in ms if x > 2) >= 2]
print(f"Multisets with >=2 non-binary: {len(k2plus)}")
k2_good = results_summary["always_good"]
k2_bad = len([e for e in bad_examples if "k=1" not in e[2]])
print(f"  Always good: {k2_good}")
print(f"  Has bad arrangement: {k2_bad}")
print(f"  Vacuous only: {results_summary['vacuous_only']}")
