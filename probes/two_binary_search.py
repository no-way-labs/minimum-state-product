"""
Search for valid systems with TWO 2-state processors and the rest at S3 rules.
Product = 4 * 3^(n-2) for n processors.

For n=5: product = 4 * 27 = 108.

Search space per pair depends on positions:
- Each binary processor has 2^(m_L * 2 * m_R) candidates
- This can be up to 2^18 = 262K per processor
- Combined: up to 262K^2 ≈ 68 billion — too large for brute force

Strategy: search one binary processor at a time, fixing the other to S3 rules
first, then iterating.

Alternative strategy: for each pair of positions, search processor 1 first
while keeping processor 2 at S3, find all valid P1 functions, then for each,
search over P2.
"""

import itertools
import time
import sys
from verifier import verify_system
from targeted_search import dijkstra_s3_bottom, dijkstra_s3_top, dijkstra_s3_middle


def search_two_binary_staged(n: int, pos1: int, pos2: int, verbose: bool = True):
    """
    Search for valid system with processors at pos1 and pos2 being 2-state.

    Stage 1: Fix pos2 to closest S3 rule, exhaustively search pos1.
             Collect ALL valid pos1 functions (not just the first).
    Stage 2: For each valid pos1 function, exhaustively search pos2.
    """
    ms = [3] * n
    ms[pos1] = 2
    ms[pos2] = 2
    total = 1
    for m in ms:
        total *= m

    if verbose:
        print(f"Two-binary search: n={n}, positions=({pos1},{pos2}), ms={ms}, product={total}")

    # Build fixed S3 functions for non-binary processors
    def get_s3_func(i):
        if i == 0:
            return dijkstra_s3_bottom
        elif i == n - 1:
            return dijkstra_s3_top
        else:
            return dijkstra_s3_middle

    # Enumerate inputs for both binary processors
    def get_inputs(pos):
        m_L = ms[(pos - 1) % n]
        m_S = ms[pos]  # = 2
        m_R = ms[(pos + 1) % n]
        return [(l, s, r) for l in range(m_L) for s in range(m_S) for r in range(m_R)]

    inputs1 = get_inputs(pos1)
    inputs2 = get_inputs(pos2)
    space1 = 2 ** len(inputs1)
    space2 = 2 ** len(inputs2)

    if verbose:
        print(f"  P{pos1}: {len(inputs1)} inputs, {space1} functions")
        print(f"  P{pos2}: {len(inputs2)} inputs, {space2} functions")
        print(f"  Staged search: {space1} + (valid_count * {space2})")

    # Stage 1: Search pos1 while pos2 uses S3 rule
    # But wait — pos2 is 2-state, so S3 rules don't directly apply
    # We need a reasonable default for pos2

    # Strategy: instead of staged search, do joint search with early pruning
    # For each pos1 candidate, quickly check liveness, then search pos2

    start = time.time()
    found_count = 0

    # Actually, let's try direct search but with the smaller processor first
    # and checking liveness constraints early

    # For now, if combined space is manageable, do it directly
    if space1 * space2 <= 10**8:
        if verbose:
            print(f"  Combined space {space1 * space2} is manageable, doing direct search")

        checked = 0
        for bits1 in range(space1):
            d1 = {}
            for idx, inp in enumerate(inputs1):
                d1[inp] = (bits1 >> idx) & 1

            def f1(L, S, R, d=d1):
                return d[(L, S, R)]

            for bits2 in range(space2):
                d2 = {}
                for idx, inp in enumerate(inputs2):
                    d2[inp] = (bits2 >> idx) & 1

                def f2(L, S, R, d=d2):
                    return d[(L, S, R)]

                fs = []
                for i in range(n):
                    if i == pos1:
                        fs.append(f1)
                    elif i == pos2:
                        fs.append(f2)
                    else:
                        fs.append(get_s3_func(i))

                result = verify_system(ms, fs)
                checked += 1

                if result['valid']:
                    elapsed = time.time() - start
                    found_count += 1
                    if verbose:
                        print(f"  FOUND #{found_count}! bits1={bits1:#x}, bits2={bits2:#x}, "
                              f"cycle_len={result['cycle_length']}, time={elapsed:.1f}s")
                    return {
                        'ms': ms,
                        'product': total,
                        'positions': (pos1, pos2),
                        'bits': (bits1, bits2),
                        'dicts': (d1, d2),
                        'verification': result,
                    }

                if checked % 500000 == 0:
                    elapsed = time.time() - start
                    total_space = space1 * space2
                    rate = checked / elapsed if elapsed > 0 else 1
                    remaining = (total_space - checked) / rate
                    if verbose:
                        print(f"  {checked}/{total_space} ({100*checked/total_space:.1f}%), "
                              f"{elapsed:.0f}s, ~{remaining:.0f}s left")

        elapsed = time.time() - start
        if verbose:
            print(f"  Not found ({checked} checked, {elapsed:.1f}s)")
        return None

    else:
        if verbose:
            print(f"  Combined space too large ({space1 * space2}), using staged approach")

        # Stage 1: find pos1 functions that at least satisfy liveness
        # when pos2 is a "neutral" function (always return S, i.e., never privileged)
        # This is too restrictive — pos2 must participate for liveness

        # Alternative: search pos1 with various pos2 defaults
        # Let's try: pos2 copies its left neighbor mod 2
        def default_f2(L, S, R):
            return L % 2

        # Search pos1
        valid_pos1 = []
        for bits1 in range(space1):
            d1 = {}
            for idx, inp in enumerate(inputs1):
                d1[inp] = (bits1 >> idx) & 1

            def f1(L, S, R, d=d1):
                return d[(L, S, R)]

            fs = []
            for i in range(n):
                if i == pos1:
                    fs.append(f1)
                elif i == pos2:
                    fs.append(default_f2)
                else:
                    fs.append(get_s3_func(i))

            result = verify_system(ms, fs)
            if result['valid']:
                valid_pos1.append(bits1)

            if (bits1 + 1) % 50000 == 0 and verbose:
                elapsed = time.time() - start
                print(f"  Stage 1: {bits1+1}/{space1}, {len(valid_pos1)} valid, {elapsed:.1f}s")

        if verbose:
            print(f"  Stage 1 complete: {len(valid_pos1)} valid P{pos1} functions")

        if not valid_pos1:
            return None

        # Stage 2: for each valid pos1, search pos2
        for bits1 in valid_pos1:
            d1 = {}
            for idx, inp in enumerate(inputs1):
                d1[inp] = (bits1 >> idx) & 1

            def f1(L, S, R, d=d1):
                return d[(L, S, R)]

            for bits2 in range(space2):
                d2 = {}
                for idx, inp in enumerate(inputs2):
                    d2[inp] = (bits2 >> idx) & 1

                def f2(L, S, R, d=d2):
                    return d[(L, S, R)]

                fs = []
                for i in range(n):
                    if i == pos1:
                        fs.append(f1)
                    elif i == pos2:
                        fs.append(f2)
                    else:
                        fs.append(get_s3_func(i))

                result = verify_system(ms, fs)
                if result['valid']:
                    elapsed = time.time() - start
                    if verbose:
                        print(f"  FOUND! P{pos1}={bits1:#x}, P{pos2}={bits2:#x}, "
                              f"cycle_len={result['cycle_length']}, {elapsed:.1f}s")
                    return {
                        'ms': ms,
                        'product': total,
                        'positions': (pos1, pos2),
                        'bits': (bits1, bits2),
                        'dicts': (d1, d2),
                        'verification': result,
                    }

        elapsed = time.time() - start
        if verbose:
            print(f"  Not found in staged search ({elapsed:.1f}s)")
        return None


if __name__ == "__main__":
    n = 5

    print("=" * 60)
    print(f"TWO-BINARY SEARCH for n={n}")
    print(f"Product = 4 * 3^{n-2} = {4 * 3**(n-2)}")
    print("=" * 60)
    print()

    # Try all pairs of positions
    # Avoid pairs with 4+ consecutive binary processors
    from smt_search import has_four_consecutive_binary

    pairs = []
    for p1 in range(n):
        for p2 in range(p1 + 1, n):
            ms = [3] * n
            ms[p1] = 2
            ms[p2] = 2
            if not has_four_consecutive_binary(ms):
                pairs.append((p1, p2))

    print(f"Feasible position pairs: {pairs}")
    print()

    for p1, p2 in pairs:
        result = search_two_binary_staged(n, p1, p2, verbose=True)
        if result:
            print(f"\n*** FOUND: product={result['product']}, positions=({p1},{p2}) ***")
            print(f"Cycle length: {result['verification']['cycle_length']}")
            break
        print()

    if not result:
        print("No valid two-binary system found with S3 rules for other processors.")
        print("This doesn't rule out product 108 — other rules might work.")
