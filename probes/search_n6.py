"""
Search for M_6: focus on (2,2,2,3,3,3) at product 216.

The parallel agent reports 35,194 cycles screened with 0 survivors
using fatal recurrent-component screening. We try:
1. Good-cycle enumeration with diverse starting configs
2. SMT completion for any surviving cycles
3. Also check nearby products (e.g., (2,2,2,3,3,4)=288 or (2,2,3,3,3,3)=324)
"""

import itertools
import time
import sys
from typing import List, Optional
from collections import Counter
from verifier import verify_system
from complete_96 import complete_with_smt
from search_96 import enumerate_good_cycles


def search_n6_product_216(verbose: bool = True) -> Optional[dict]:
    """Search (2,2,2,3,3,3) at product 216."""
    ms = [2, 2, 2, 3, 3, 3]
    n = 6
    total = 216

    if verbose:
        print(f"Searching ms={ms}, product={total}")
        print(f"Configuration space: {total} configs")

    # Enumerate good cycles with many starts
    cycles = enumerate_good_cycles(ms, max_cycles=1000, verbose=verbose)

    if not cycles:
        if verbose:
            print("No good cycles found")
        return None

    if verbose:
        lengths = [len(c) for c in cycles]
        print(f"Testing {len(cycles)} cycles, lengths: {min(lengths)}-{max(lengths)}")

    for i, cycle in enumerate(cycles):
        result = complete_with_smt(ms, cycle, timeout_ms=15000, verbose=False)
        if result:
            if verbose:
                print(f"VALID! Cycle #{i+1} (len={len(cycle)})")
            return result
        if (i + 1) % 100 == 0 and verbose:
            print(f"  Tested {i+1}/{len(cycles)}...")

    if verbose:
        print("No valid completion found")
    return None


def search_n6_alternatives(verbose: bool = True) -> Optional[dict]:
    """Search alternative product-216 vectors and nearby products for n=6."""
    from smt_search import has_four_consecutive_binary, canonical_rotation

    # Product 216 vectors (other arrangements of 2,2,2,3,3,3)
    # and product 288 = 2*2*2*3*3*4, product 324 = 2*2*3*3*3*3, etc.
    candidates = []

    # All arrangements of (2,2,2,3,3,3) - these are rotations/reflections
    from itertools import permutations
    seen = set()
    for p in permutations([2, 2, 2, 3, 3, 3]):
        canon = canonical_rotation(p)
        if canon not in seen and not has_four_consecutive_binary(list(p)):
            seen.add(canon)
            candidates.append((216, list(p)))

    # Product 288 = 2^2 * 3^2 * 4 * ... various
    for p in permutations([2, 2, 2, 3, 3, 4]):
        canon = canonical_rotation(p)
        if canon not in seen and not has_four_consecutive_binary(list(p)):
            seen.add(canon)
            candidates.append((288, list(p)))

    # Product 324 = 4 * 3^4
    for p in permutations([2, 2, 3, 3, 3, 3]):
        canon = canonical_rotation(p)
        if canon not in seen and not has_four_consecutive_binary(list(p)):
            seen.add(canon)
            candidates.append((324, list(p)))

    candidates.sort(key=lambda x: (x[0], x[1]))

    if verbose:
        print(f"Total candidate vectors: {len(candidates)}")
        by_product = {}
        for p, v in candidates:
            if p not in by_product:
                by_product[p] = []
            by_product[p].append(v)
        for p in sorted(by_product.keys()):
            print(f"  Product {p}: {len(by_product[p])} vectors")

    for product_val, ms in candidates:
        if verbose:
            print(f"\n--- ms={ms}, product={product_val} ---")

        cycles = enumerate_good_cycles(ms, max_cycles=200, verbose=False)
        if verbose:
            print(f"  {len(cycles)} good cycles found")

        if not cycles:
            continue

        for i, cycle in enumerate(cycles):
            result = complete_with_smt(ms, cycle, timeout_ms=15000, verbose=False)
            if result:
                if verbose:
                    print(f"  VALID! Cycle #{i+1} (len={len(cycle)}), "
                          f"verified cycle_len={result['verification']['cycle_length']}")
                return result
            if (i + 1) % 50 == 0 and verbose:
                print(f"  Tested {i+1}/{len(cycles)}...")

        if verbose:
            print(f"  No valid completion")

    return None


if __name__ == "__main__":
    print("=" * 60)
    print("SEARCH FOR M_6")
    print("=" * 60)
    print()

    # First try the critical case
    print("--- Phase 1: (2,2,2,3,3,3) at product 216 ---")
    result = search_n6_product_216(verbose=True)

    if result:
        print(f"\n*** M_6 <= 216 VERIFIED! ***")
        print(f"ms={result['ms']}, cycle_length={result['cycle_length']}")
    else:
        print("\n--- Phase 2: Searching alternatives ---")
        result = search_n6_alternatives(verbose=True)

        if result:
            print(f"\n*** M_6 <= {result['product']} ***")
            print(f"ms={result['ms']}, cycle_length={result['cycle_length']}")
        else:
            print("\nNo valid n=6 system found in search.")
