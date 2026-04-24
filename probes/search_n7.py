"""
Search for M_7: systematic exploration of products between 576 and 1152.

Known bounds: 576 < M_7 <= 1152.
Pattern prediction: M_7 = 864 = 2^5 * 3^3 (3 binary + 1 quaternary + 3 ternary).
Best known: M_7 <= 1152 at (2,2,2,4,3,4,3).

Key lesson from n=6: orientation matters critically.
(2,2,2,4,3,3) worked but (2,2,2,3,3,4) and (2,2,2,3,4,3) failed.
The 4-state processor position relative to the binary/ternary boundary is crucial.

Strategy:
1. Try ALL feasible orientations at product 864 (not just (2,2,2,4,3,3,3))
2. If 864 fails, try products 768, 896, 960, 972, 1024, 1080
3. For each product, generate all distinct state vectors (up to rotation),
   filter by 4-consecutive-binary obstruction, enumerate cycles, SMT complete.
"""

import itertools
import time
import sys
from typing import List, Optional, Tuple
from collections import Counter
from itertools import permutations

from verifier import verify_system
from complete_96 import complete_with_smt
from search_96 import enumerate_good_cycles
from smt_search import has_four_consecutive_binary, canonical_rotation


def generate_n7_vectors(product: int) -> list:
    """
    Generate all distinct (up to rotation) state vectors for n=7 with given product.
    Each m_i >= 2. Filter out vectors with 4+ consecutive binary processors.
    """
    n = 7
    # Find all factorizations of product into n factors, each >= 2
    vectors = set()

    def factorize(remaining, depth, current):
        if depth == n:
            if remaining == 1:
                vectors.add(tuple(current))
            return
        # Max factor to try
        max_f = remaining
        if depth < n - 1:
            # Leave room for remaining positions (each >= 2)
            min_remaining = 2 ** (n - 1 - depth)
            max_f = remaining // min_remaining
        for f in range(2, max_f + 1):
            if remaining % f == 0:
                factorize(remaining // f, depth + 1, current + [f])

    factorize(product, 0, [])

    # Deduplicate by canonical rotation
    seen = set()
    result = []
    for v in vectors:
        # Also check all permutations since factorize gives sorted-ish results
        # Actually factorize gives ordered results, we need all permutations
        pass

    # Better approach: generate all permutations of each multiset of factors
    factor_multisets = set()
    for v in vectors:
        factor_multisets.add(tuple(sorted(v)))

    seen = set()
    result = []
    for ms_sorted in factor_multisets:
        for p in set(permutations(ms_sorted)):
            canon = canonical_rotation(p)
            if canon not in seen:
                if not has_four_consecutive_binary(list(p)):
                    seen.add(canon)
                    result.append(list(p))

    result.sort()
    return result


def search_product(product: int, ms_list: list, max_cycles: int = 500,
                   smt_timeout: int = 60000, max_smt_per_vector: int = 50,
                   verbose: bool = True) -> Optional[dict]:
    """Search all vectors at a given product."""
    if verbose:
        print(f"\n{'='*60}")
        print(f"Product {product}: {len(ms_list)} feasible vectors")
        print(f"{'='*60}")

    for vi, ms in enumerate(ms_list):
        if verbose:
            print(f"\n--- [{vi+1}/{len(ms_list)}] ms={ms}, product={product} ---")

        t0 = time.time()
        cycles = enumerate_good_cycles(ms, max_cycles=max_cycles, verbose=False)
        t_enum = time.time() - t0

        if not cycles:
            if verbose:
                print(f"  0 cycles ({t_enum:.1f}s)")
            continue

        lengths = [len(c) for c in cycles]
        if verbose:
            print(f"  {len(cycles)} cycles (len {min(lengths)}-{max(lengths)}) in {t_enum:.1f}s")

        # Sort by cycle length (shorter = more constrained = faster SMT)
        cycles.sort(key=len)

        # Test the shortest cycles with SMT
        n_test = min(max_smt_per_vector, len(cycles))
        for i in range(n_test):
            cycle = cycles[i]
            t0 = time.time()
            result = complete_with_smt(ms, cycle, timeout_ms=smt_timeout, verbose=False)
            t_smt = time.time() - t0

            if result:
                if verbose:
                    print(f"  *** VALID! Cycle #{i+1} (len={len(cycle)}), "
                          f"verified cycle_len={result['verification']['cycle_length']}, "
                          f"{t_smt:.1f}s ***")
                return result

            if verbose and (i + 1) % 10 == 0:
                print(f"  Tested {i+1}/{n_test} cycles...")

        if verbose:
            print(f"  No valid completion in {n_test} cycles")

    return None


def search_n7_864_all_orientations(verbose: bool = True) -> Optional[dict]:
    """
    Exhaustive search of product 864 = 2^5 * 3^3 with ALL orientations.

    Key factor multisets:
    - (2,2,2,3,3,3,4): the "3+1+rest" pattern
    - (2,2,2,2,3,3,6): introduces 6-state
    - (2,2,2,2,3,4,3): same as above, different factor
    - (2,2,2,2,2,3,9): more binary, 9-state
    - (2,2,3,3,3,4,2): same multiset as first, different orientation
    - etc.
    """
    vectors = generate_n7_vectors(864)

    if verbose:
        print(f"Product 864: {len(vectors)} feasible vectors (after rotation+obstruction filter)")
        # Group by sorted multiset
        by_multiset = {}
        for v in vectors:
            key = tuple(sorted(v))
            if key not in by_multiset:
                by_multiset[key] = []
            by_multiset[key].append(v)
        for key in sorted(by_multiset.keys()):
            print(f"  {key}: {len(by_multiset[key])} orientations")

    return search_product(864, vectors, max_cycles=500, smt_timeout=120000,
                          max_smt_per_vector=30, verbose=verbose)


def search_n7_intermediate_products(verbose: bool = True) -> Optional[dict]:
    """Search products between 576 and 1152 systematically."""
    # Products to try, ordered by promise
    # Focus on products with small prime factors (2,3,4,5,6)
    products_to_try = []

    # Generate products of the form 2^a * 3^b * k where k is small
    for product in range(577, 1152):
        # Only try products whose prime factorization uses small primes
        p = product
        factors = []
        for prime in [2, 3, 5, 7]:
            while p % prime == 0:
                factors.append(prime)
                p //= prime
        if p > 1:
            continue  # Has large prime factor, skip
        if max(factors) > 7:
            continue
        products_to_try.append(product)

    if verbose:
        print(f"Intermediate products to search: {len(products_to_try)}")
        print(f"Products: {products_to_try[:20]}...")

    for product in products_to_try:
        vectors = generate_n7_vectors(product)
        if not vectors:
            continue

        result = search_product(product, vectors, max_cycles=300, smt_timeout=60000,
                                max_smt_per_vector=20, verbose=verbose)
        if result:
            return result

    return None


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--product", type=int, default=0, help="Search specific product")
    parser.add_argument("--all-864", action="store_true", help="All orientations at 864")
    parser.add_argument("--intermediate", action="store_true", help="Search 577-1151")
    parser.add_argument("--ms", type=str, default="", help="Specific state vector, comma-separated")
    parser.add_argument("--max-cycles", type=int, default=500)
    parser.add_argument("--smt-timeout", type=int, default=120000)
    parser.add_argument("--max-smt", type=int, default=30)
    args = parser.parse_args()

    if args.ms:
        ms = [int(x) for x in args.ms.split(",")]
        product = 1
        for m in ms:
            product *= m
        print(f"Searching ms={ms}, product={product}")
        cycles = enumerate_good_cycles(ms, max_cycles=args.max_cycles, verbose=True)
        if cycles:
            cycles.sort(key=len)
            n_test = min(args.max_smt, len(cycles))
            for i in range(n_test):
                cycle = cycles[i]
                t0 = time.time()
                result = complete_with_smt(ms, cycle, timeout_ms=args.smt_timeout, verbose=False)
                t_smt = time.time() - t0
                if result:
                    print(f"\n*** VALID! Cycle #{i+1} (len={len(cycle)}), "
                          f"verified cycle_len={result['verification']['cycle_length']}, "
                          f"{t_smt:.1f}s ***")
                    print(f"ms={result['ms']}, product={result['product']}")
                    # Save result
                    fname = f"n7_product{product}_result.txt"
                    with open(fname, "w") as f:
                        f.write(f"ms={result['ms']}\n")
                        f.write(f"product={result['product']}\n")
                        f.write(f"cycle_length={result['cycle_length']}\n")
                        f.write(f"good_cycle={result['cycle']}\n\n")
                        for key, val in sorted(result['fs_values'].items()):
                            f.write(f"f[{key[0]}]({key[1]},{key[2]},{key[3]}) = {val}\n")
                    print(f"Saved to {fname}")
                    sys.exit(0)
                if (i + 1) % 5 == 0:
                    print(f"  Tested {i+1}/{n_test}...")
            print("No valid completion found")

    elif args.product:
        vectors = generate_n7_vectors(args.product)
        result = search_product(args.product, vectors, max_cycles=args.max_cycles,
                                smt_timeout=args.smt_timeout, max_smt_per_vector=args.max_smt)
        if result:
            print(f"\n*** M_7 <= {args.product} ***")

    elif args.all_864:
        result = search_n7_864_all_orientations()
        if result:
            print(f"\n*** M_7 <= 864 VERIFIED! ***")
        else:
            print("\nProduct 864 appears infeasible across all orientations.")

    elif args.intermediate:
        result = search_n7_intermediate_products()
        if result:
            print(f"\n*** M_7 <= {result['product']} ***")
        else:
            print("\nNo valid system found in range 577-1151.")

    else:
        # Default: try key orientations at 864 first
        print("Phase 1: Key 864 orientations suggested by cross-pollination")
        key_864 = [
            [3, 2, 2, 2, 4, 3, 3],  # 4-state shifted right
            [3, 3, 2, 2, 2, 4, 3],  # 4-state further right
            [2, 2, 2, 3, 4, 3, 3],  # different ternary arrangement
            [2, 2, 2, 3, 3, 4, 3],  # 4-state between ternary
            [3, 2, 2, 4, 2, 3, 3],  # 4-state in middle of ring
            [2, 3, 2, 2, 2, 4, 3],  # ternary breaks binary block
            [3, 2, 4, 2, 2, 3, 3],  # 4-state away from binary block
            [2, 2, 4, 3, 3, 3, 2],  # 4-state adjacent to binary pair
            [3, 3, 3, 4, 2, 2, 2],  # reversed: ternary block first
            [4, 3, 3, 3, 2, 2, 2],  # 4-state at boundary, reversed
            [2, 4, 2, 3, 2, 3, 3],  # scattered binary
            [2, 3, 4, 2, 3, 2, 3],  # alternating-ish
        ]
        # Filter and deduplicate
        seen = set()
        filtered = []
        for ms in key_864:
            p = 1
            for m in ms:
                p *= m
            if p != 864:
                continue
            canon = canonical_rotation(tuple(ms))
            if canon in seen:
                continue
            if has_four_consecutive_binary(ms):
                continue
            seen.add(canon)
            filtered.append(ms)

        print(f"  {len(filtered)} key vectors to test")
        result = search_product(864, filtered, max_cycles=500, smt_timeout=120000,
                                max_smt_per_vector=30)

        if not result:
            print("\nPhase 2: All 864 orientations")
            result = search_n7_864_all_orientations()

        if not result:
            print("\nPhase 3: Intermediate products (577-1151)")
            result = search_n7_intermediate_products()

        if result:
            print(f"\n{'='*60}")
            print(f"*** M_7 <= {result['product']} ***")
            print(f"ms={result['ms']}")
            print(f"{'='*60}")
