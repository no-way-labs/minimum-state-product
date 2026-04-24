#!/usr/bin/env python3
"""sol3_gap_search.py — Search for witnesses in the gap (8748, 13122).

Products in the gap with 9-entry multisets (each ≥ 2):
- 8748 = {2^2, 3^7}: DEAD for Sol 3
- 9720 = {2^3, 5, 3^5}: 3 binary + 1 pentary + 5 ternary
- 10368 = {2^3, 4^2, 3^4}: 3 binary + 2 quaternary + 4 ternary
- 11664 = {2^2, 4, 3^6}: 2 binary + 1 quaternary + 6 ternary
- 12150 = {2, 5, 3^7}: 1 binary + 1 pentary + 7 ternary
- 13122 = {2, 3^8}: ALIVE! (Sol 3 v1)

Key insight: any multiset with exactly 1 binary proc and all others ≥ 3
should work with Sol 3 v1. The minimum such product is 2·3^8 = 13122.
But what about {2, 4, 3^7} (product 17496) or {2, 5, 3^7} (product 21870)?
Those have higher products, not helpful.

What about FEWER binary procs? {2, 3^8} is the only 1-binary option in the gap.
For 0 binary: {3^9} = 19683 (all ternary, Dijkstra Sol 3 works).

So the real question: is 13122 the minimum, or can we do better with
non-{2,3} multisets that have 2+ binary procs and compensate with
higher-state procs?
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

from verifier import verify_system
from itertools import combinations_with_replacement


def sol3_adapt_v1(ms, n):
    """v1: replace K with m_i in mod operations."""
    def make_bottom(m0):
        def f(L, S, R):
            if (S + 1) % m0 == R % m0:
                return (S - 1) % m0
            return S
        return f

    def make_top(m_top):
        def f(L, S, R):
            if L % m_top == R % m_top and (L % m_top + 1) % m_top != S:
                return (L % m_top + 1) % m_top
            return S
        return f

    def make_middle(m_i):
        def f(L, S, R):
            if (S + 1) % m_i == L % m_i:
                return L % m_i
            if (S + 1) % m_i == R % m_i:
                return R % m_i
            return S
        return f

    fs = [make_bottom(ms[0])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i]))
    fs.append(make_top(ms[n - 1]))
    return fs


def enumerate_multisets_9(product_target, max_val=9):
    """Find all multisets of 9 integers ≥ 2 whose product = product_target."""
    n = 9
    results = []

    def backtrack(remaining_product, remaining_slots, min_val, current):
        if remaining_slots == 0:
            if remaining_product == 1:
                results.append(tuple(sorted(current)))
            return
        for v in range(min_val, min(max_val + 1, remaining_product + 1)):
            if remaining_product % v == 0:
                rp = remaining_product // v
                if rp >= v ** (remaining_slots - 1):
                    backtrack(rp, remaining_slots - 1, v, current + [v])

    backtrack(product_target, n, 2, [])
    return sorted(set(results))


def necklaces_for_multiset(ms_tuple, n):
    """Generate distinct necklaces for a multiset."""
    from itertools import permutations
    seen = set()
    necklaces = []
    for perm in set(permutations(ms_tuple)):
        canonical = min(tuple(perm[(k + rot) % n] for k in range(n)) for rot in range(n))
        if canonical not in seen:
            seen.add(canonical)
            necklaces.append(canonical)
    return sorted(necklaces)


def main():
    n = 9
    print("=" * 70)
    print("GAP SEARCH: products between 8748 and 13122")
    print("=" * 70)

    # Enumerate all products in the gap
    gap_products = []
    for p in range(8749, 13122):
        ms_list = enumerate_multisets_9(p)
        if ms_list:
            gap_products.append((p, ms_list))

    print(f"Products in gap with valid multisets: {len(gap_products)}")
    for p, ms_list in gap_products[:20]:
        print(f"  {p}: {ms_list}")

    # Test Sol 3 v1 on all gap products
    print(f"\n{'=' * 70}")
    print("TESTING SOL 3 v1 ON GAP PRODUCTS")
    print(f"{'=' * 70}")

    for p, ms_list in gap_products:
        for ms in ms_list:
            bin_count = sum(1 for m in ms if m == 2)

            # Quick filter: if all entries ≥ 3 (0 binary), Sol 3 works
            # If exactly 1 binary, Sol 3 v1 should work (like 13122)
            if bin_count <= 1:
                # Try all necklaces
                necklaces = necklaces_for_multiset(ms, n)
                for neck in necklaces[:5]:  # Limit to 5 necklaces
                    # Try all rotations
                    tested = set()
                    for rot in range(n):
                        ms_rot = tuple(neck[(k + rot) % n] for k in range(n))
                        if ms_rot in tested:
                            continue
                        tested.add(ms_rot)

                        fs = sol3_adapt_v1(list(ms_rot), n)
                        result = verify_system(list(ms_rot), fs)
                        if result.get('valid', False):
                            cycle_len = result.get('cycle_length', '?')
                            n_good = len(result.get('good_configs', set()))
                            print(f"\n  *** VALID at product {p}! ***")
                            print(f"  ms={ms_rot}, cycle={cycle_len}, good={n_good}")
                            props = result.get('properties', {})
                            for k, v in props.items():
                                print(f"    {k}: {v}")
                            break
                    else:
                        continue
                    break
            else:
                # 2+ binary — Sol 3 v1 likely fails, but try base orientation
                fs = sol3_adapt_v1(list(ms), n)
                result = verify_system(list(ms), fs)
                if result.get('valid', False):
                    print(f"\n  *** VALID at product {p}! ***")
                    print(f"  ms={ms}")
                    break

    # Also: check the 1-binary multisets below 13122
    print(f"\n{'=' * 70}")
    print("TESTING 1-BINARY MULTISETS BELOW 13122")
    print(f"{'=' * 70}")

    # {2, X, 3^7}: product = 2·X·3^7. For X ≥ 3:
    # X=3: product = 2·3^8 = 13122 (known)
    # Can we have {2, X, Y, 3^6} with product < 13122?
    # 2·X·Y·3^6. For X=Y=3: 2·9·729 = 13122. For X=3,Y=2: 2·6·729=8748.
    # For X=4,Y=2: 2·8·729=11664. Has 2 binary + 1 quaternary.

    # Try {2, 4, 3, 3, 3, 3, 3, 3, 3} — but product = 2·4·3^7 = 17496 > 13122.

    # 1-binary multisets with product < 13122:
    # {2, a1, a2, ..., a8} with a_i ≥ 2 and 2·∏a_i < 13122
    # ∏a_i < 6561 = 3^8 with 8 values ≥ 2
    # Max with 8 threes: 3^8 = 6561, product = 2·6561 = 13122 (boundary)
    # To get below: at least one a_i = 2, giving 2 binary procs.
    # So the MINIMUM 1-binary-only product is 2·3^8 = 13122!
    # There are NO 1-binary multisets with product < 13122.
    print("Minimum 1-binary product = 2·3^8 = 13122")
    print("No 1-binary multisets exist below 13122.")
    print("Therefore: if 2-binary multisets are all dead, M_9 = 13122.")


if __name__ == "__main__":
    main()
