"""
Structural lower bound analysis for M_n.

Known obstructions:
1. All-binary fails for n >= 5 (DEA's bad cycle)
2. Four or more consecutive 2-state processors are impossible (RFC)
3. ARG's LCM constraint: with 2N non-adjacent 2-state processors,
   the LCM of state counts in each intervening block must be >= N+1

Goal: derive product lower bounds for n=7 (and general n) without
exhaustive search, ruling out product ranges structurally.
"""

import itertools
import math
from typing import List, Tuple, Set
from collections import defaultdict
from smt_search import has_four_consecutive_binary, canonical_rotation


def min_product_by_arg_constraint(n: int) -> dict:
    """
    Use ARG's LCM constraint to derive minimum products.

    With k 2-state processors (0 <= k <= n), placed non-adjacently
    (no two adjacent unless explicitly adjacent), we need:
    - At most 3 consecutive 2-state processors (RFC)
    - For 2N non-adjacent 2-state processors: LCM of each intervening
      block's state counts >= N+1

    For each possible number of binary processors k, compute the minimum
    product achievable given the constraints.
    """
    results = {}

    for k in range(n + 1):
        # k binary processors in a ring of n
        # The remaining n-k processors have m_i >= 3

        # RFC constraint: no 4+ consecutive binary
        # So binary processors form runs of length <= 3

        # The binary processors split the ring into blocks.
        # Each block between consecutive runs of binary processors
        # has non-binary processors.

        # Let's enumerate the minimum product for each k.
        # Binary contribution: 2^k
        # Non-binary contribution: product of (n-k) processors, each >= 3
        # But with ARG's LCM constraint, some might need to be >= 4

        # Simple lower bound: 2^k * 3^(n-k) if no ARG constraint applies
        simple_lb = 2**k * 3**(n - k)

        # ARG constraint: if we have 2N non-adjacent binary processors,
        # each intervening block must have LCM >= N+1.

        # For the ARG constraint, "non-adjacent" means the 2-state processors
        # that are separated by non-binary blocks.

        # If binary processors are arranged optimally:
        # - Runs of 1, 2, or 3 binary processors
        # - Between runs, at least 1 non-binary processor

        # Minimum non-binary processors needed: ceil(k/3) blocks,
        # each needing at least 1 non-binary processor
        # So we need n - k >= ceil(k/3), i.e., n >= k + ceil(k/3) = k*(1+1/3) = 4k/3
        # Maximum k: k <= 3n/4

        if k > 0:
            min_blocks = math.ceil(k / 3)  # minimum blocks of non-binary
            if n - k < min_blocks:
                results[k] = {'feasible': False, 'reason': 'not enough non-binary'}
                continue

        # Count "non-adjacent" binary positions for ARG.
        # If binary are in runs of 1-3, each run acts as a "non-adjacent" group.
        # For ARG, 2N = number of non-adjacent binary groups? Or individual positions?

        # Actually, let me re-read ARG's constraint more carefully.
        # "with 2N non-adjacent 2-state processors" — I think this means
        # 2N individual binary processors, none adjacent to each other.
        # Each pair of consecutive binary processors defines a block between them.
        # The LCM of state counts in each block must be >= N+1.

        # This applies when ALL binary processors are non-adjacent (isolated).
        # If some are adjacent (runs of 2 or 3), the constraint may be different.

        # For the simplest case: k isolated binary processors (all non-adjacent).
        # Then there are k blocks between consecutive binary processors.
        # ARG says: LCM of each block >= ceil(k/2) + 1? No...
        # "2N non-adjacent 2-state processors" means k = 2N, so N = k/2.
        # LCM >= N + 1 = k/2 + 1.

        results[k] = {
            'feasible': True,
            'simple_lb': simple_lb,
            'binary_count': k,
            'nonbinary_count': n - k,
        }

    return results


def enumerate_valid_multisets(n: int, max_product: int) -> list:
    """
    Enumerate all valid state-count multisets for n processors
    with product <= max_product, respecting structural constraints.

    Returns list of (product, multiset) tuples, sorted by product.
    """
    results = []

    def generate(pos, remaining_product, current, max_consec_binary):
        """
        pos: current processor position
        remaining_product: product budget left
        current: list of state counts so far
        max_consec_binary: current run of consecutive 2-state processors
        """
        if pos == n:
            if remaining_product == 1:
                # Check the wrap-around: consecutive binary at end and start
                total_wrap_binary = 0
                # Count binary at end
                end_bin = 0
                for i in range(n - 1, -1, -1):
                    if current[i] == 2:
                        end_bin += 1
                    else:
                        break
                # Count binary at start
                start_bin = 0
                for i in range(n):
                    if current[i] == 2:
                        start_bin += 1
                    else:
                        break
                if start_bin + end_bin >= 4 and start_bin < n:
                    return  # Wrap-around gives 4+ consecutive binary

                results.append(tuple(current))
            return

        remaining_positions = n - pos
        min_needed = 2 ** remaining_positions
        if remaining_product < min_needed:
            return  # Can't fill remaining positions

        max_m = remaining_product // (2 ** (remaining_positions - 1))

        for m in range(2, min(max_m + 1, remaining_product + 1)):
            if remaining_product % m != 0:
                continue

            new_consec = max_consec_binary + 1 if m == 2 else 0
            if new_consec >= 4:
                continue  # RFC constraint

            current.append(m)
            generate(pos + 1, remaining_product // m, current, new_consec)
            current.pop()

    # Generate all multisets with product exactly p for each p up to max_product
    # Actually, generate all vectors with product <= max_product
    for p in range(2**n, max_product + 1):
        generate(0, p, [], 0)

    # Deduplicate by canonical rotation
    seen = set()
    unique = []
    for v in results:
        canon = canonical_rotation(v)
        if canon not in seen:
            seen.add(canon)
            product = 1
            for m in v:
                product *= m
            unique.append((product, list(v)))

    unique.sort()
    return unique


def arg_constraint_analysis(ms: List[int]) -> dict:
    """
    Check ARG's LCM constraint for a given state vector.

    Identify all maximal runs of 2-state processors and the blocks between them.
    For the constraint: with 2N non-adjacent 2-state processors,
    LCM of each block must be >= N+1.
    """
    n = len(ms)

    # Find runs of binary processors
    binary_runs = []
    i = 0
    while i < n:
        if ms[i] == 2:
            run_start = i
            run_len = 0
            while i < n and ms[i] == 2:
                run_len += 1
                i += 1
            binary_runs.append((run_start, run_len))
        else:
            i += 1

    # Handle wrap-around
    if len(binary_runs) >= 2:
        first = binary_runs[0]
        last = binary_runs[-1]
        if first[0] == 0 and last[0] + last[1] == n:
            # Merge
            merged_len = first[1] + last[1]
            binary_runs = binary_runs[1:-1]
            binary_runs.append((last[0], merged_len))

    total_binary = sum(r[1] for r in binary_runs)
    num_runs = len(binary_runs)

    # Each run acts as a "group" for ARG's constraint.
    # The blocks between runs contain non-binary processors.
    # For ARG: if we have num_runs isolated binary groups,
    # treat them as having 2*num_runs/2 = num_runs non-adjacent positions.
    # But actually, a run of 2 or 3 binary acts as multiple binary processors.

    # The constraint as stated: "2N non-adjacent 2-state processors"
    # For isolated (run length 1) binary processors only:
    isolated_binary = sum(1 for _, l in binary_runs if l == 1)

    # Find blocks between binary runs
    blocks = []
    if num_runs == 0:
        return {
            'binary_runs': binary_runs,
            'total_binary': total_binary,
            'blocks': [],
            'arg_satisfied': True,
            'arg_applicable': False,
        }

    # Sort runs by start position
    binary_runs.sort()

    for idx in range(num_runs):
        run_end = binary_runs[idx][0] + binary_runs[idx][1]
        next_run_start = binary_runs[(idx + 1) % num_runs][0]
        if (idx + 1) % num_runs == 0:
            next_run_start += n  # wrap
        block_positions = list(range(run_end, next_run_start))
        block_ms = [ms[p % n] for p in block_positions]
        if block_ms:
            block_lcm = block_ms[0]
            for m in block_ms[1:]:
                block_lcm = math.lcm(block_lcm, m)
            blocks.append({
                'positions': [p % n for p in block_positions],
                'ms': block_ms,
                'lcm': block_lcm,
            })

    # ARG's constraint: with 2N non-adjacent binary, LCM >= N+1
    # Here N = total_binary / 2 (if even) or (total_binary - 1) / 2
    # Actually, the constraint says "2N" binary, so total must be even
    # If odd, use 2N = total_binary - 1
    N = total_binary // 2
    min_lcm_required = N + 1 if N > 0 else 1

    arg_satisfied = all(b['lcm'] >= min_lcm_required for b in blocks) if blocks else True

    return {
        'binary_runs': binary_runs,
        'total_binary': total_binary,
        'num_runs': num_runs,
        'blocks': blocks,
        'N': N,
        'min_lcm_required': min_lcm_required,
        'arg_satisfied': arg_satisfied,
        'arg_applicable': N > 0,
    }


def theoretical_lower_bound_n7():
    """
    Derive theoretical lower bounds for M_7 using structural constraints.

    Strategy: for each product P from 577 to 863, show that NO state vector
    with that product can satisfy all structural constraints.
    """
    n = 7

    print("=" * 60)
    print("THEORETICAL LOWER BOUND ANALYSIS FOR M_7")
    print("=" * 60)
    print()

    # For each product, enumerate all feasible state vectors and check constraints
    products_with_feasible = []
    products_ruled_out = []

    for product in range(128, 864):
        # Quick check: can product be factored into 7 factors >= 2?
        if product < 2**7:
            continue

        # Check if product has appropriate factorization
        # All prime factors must be >= 2, and product / 2^6 >= 2 for the 7th
        # Actually just check if we can factor it

        # Generate all factorizations into 7 parts >= 2
        def factorize(remaining, depth):
            if depth == 7:
                return [[]] if remaining == 1 else []
            results = []
            min_rest = 2 ** (6 - depth)
            max_f = remaining // min_rest if depth < 6 else remaining
            for f in range(2, max_f + 1):
                if remaining % f == 0:
                    for rest in factorize(remaining // f, depth + 1):
                        results.append([f] + rest)
            return results

        raw = factorize(product, 0)
        if not raw:
            continue

        # Get unique vectors up to rotation, check RFC
        multisets = set()
        for v in raw:
            multisets.add(tuple(sorted(v)))

        seen = set()
        feasible_vectors = []
        for ms_sorted in multisets:
            for p in set(itertools.permutations(ms_sorted)):
                canon = canonical_rotation(p)
                if canon not in seen:
                    seen.add(canon)
                    if not has_four_consecutive_binary(list(p)):
                        # Check ARG constraint
                        arg = arg_constraint_analysis(list(p))
                        if arg['arg_satisfied']:
                            feasible_vectors.append(list(p))

        if feasible_vectors:
            products_with_feasible.append((product, feasible_vectors))
        else:
            products_ruled_out.append(product)

    print(f"Products 128-863 analyzed:")
    print(f"  Ruled out by RFC + ARG: {len(products_ruled_out)}")
    print(f"  Have feasible vectors: {len(products_with_feasible)}")
    print()

    # Focus on the gap 577-863
    gap_feasible = [(p, v) for p, v in products_with_feasible if 577 <= p <= 863]
    print(f"Products in gap [577, 863] with feasible vectors:")
    for product, vectors in gap_feasible:
        n_binary = [sum(1 for m in v if m == 2) for v in vectors]
        print(f"  Product {product}: {len(vectors)} vectors, "
              f"binary counts: {sorted(set(n_binary))}")

    return products_with_feasible, products_ruled_out


def stronger_arg_analysis():
    """
    Analyze ARG's constraint more carefully to rule out more products.

    Key insight: ARG's constraint says that with 2N non-adjacent binary
    processors, each intervening block must have LCM >= N+1.

    For a block of size b with all processors being 3-state,
    LCM = 3 (since lcm(3,3,...,3) = 3).
    So if all non-binary processors are 3-state, we need 3 >= N+1,
    i.e., N <= 2, i.e., at most 4 binary processors.

    For a block with a 4-state processor, LCM >= 4 (if block contains a 4-state).
    Actually lcm(3,4) = 12, lcm(4) = 4.
    So a single 4-state gives LCM >= 4, requiring N <= 3 (6 binary).

    For a block with only 3-state: LCM = 3, requiring N <= 2 (4 binary).
    """
    print()
    print("=" * 60)
    print("STRONGER ARG ANALYSIS")
    print("=" * 60)
    print()

    print("ARG's constraint: with 2N non-adjacent binary, each block LCM >= N+1.")
    print()
    print("If all non-binary are 3-state:")
    print("  Block LCM = 3, so N <= 2, i.e., at most 4 binary processors.")
    print("  This means (2,2,2,3,3,3,3) with 3 binary CAN satisfy ARG (N=1, need LCM>=2, have 3).")
    print("  But (2,2,2,2,3,3,3) with 4 binary: N=2, need LCM>=3, have 3. Barely works!")
    print("  And (2,2,2,2,2,3,3) with 5 binary: N=2, need LCM>=3, have 3. BUT need to check")
    print("  if 5 binary can be placed without 4+ consecutive. Max runs of 3,2 with non-binary between.")
    print("  Ring: 2,2,2,X,2,2,X where X>=3. Wrap: X,2,2,2,X,2,2 — 3 consecutive at most. OK.")
    print("  N = 5//2 = 2, need LCM >= 3. Blocks: [X], [X]. If both are 3, LCM = 3 >= 3. Barely works!")
    print()

    # So ARG alone doesn't kill many products. Let me think about what ELSE we know.
    # The key additional constraint is that product 576 and below are computationally
    # shown to be dead or nearly dead.

    # Can we derive a stronger structural argument?
    #
    # Observation from our data:
    # - M_5 = 96 = 2^5 * 3 = (2,2,2,3,4), needs a 4-state processor
    # - M_6 = 288 = 2^5 * 3^2 = (2,2,2,4,3,3), needs a 4-state processor
    # - M_7 = 864 = 2^5 * 3^3 = (3,2,2,2,3,4,3), needs a 4-state processor
    #
    # Conjecture: ANY valid system for n >= 5 needs at least one processor
    # with m_i >= 4. This would rule out all products that are only 2s and 3s.
    #
    # Products of form 2^a * 3^b for n=7 with product < 864:
    # 2^a * 3^b where 2^a * 3^b < 864 and a+b = 7 (or factors allow 7 processors)

    print("CONJECTURE: Any valid system for n >= 5 needs at least one m_i >= 4.")
    print()
    print("Evidence:")
    print("  n=5: M_5 = 96, all valid systems have max(m_i) >= 4")
    print("  n=6: M_6 = 288, all valid systems have max(m_i) >= 4")
    print("  n=7: M_7 = 864, all valid systems have max(m_i) >= 4")
    print("  Product 648 = 2^3 * 3^4 = (2,2,2,3,3,3,3) — appears dead")
    print("  Product 216 = 2^3 * 3^3 = (2,2,2,3,3,3) for n=6 — dead")
    print("  Product 72 = 2^3 * 3^2 = (2,2,2,3,3) for n=5 — dead")
    print()

    # If this conjecture is true:
    # For n=7, product must include at least one factor >= 4.
    # Minimum product with 3 binary + 1 four-state + 3 ternary:
    # 2^3 * 4 * 3^3 = 864. This IS M_7!
    #
    # So if we can prove that max(m_i) >= 4 is necessary AND that 3 binary
    # is optimal, then M_7 = 864 is exact.

    print("If conjecture is true:")
    print("  Minimum product for n=7 with one 4+ state processor:")
    print("  Need to minimize 2^a * 3^b * m_big where a + b + 1 = 7, m_big >= 4")
    print("  Minimize: 2^a * 3^(6-a) * 4 subject to RFC constraints")
    print("  a=3: 8 * 27 * 4 = 864")
    print("  a=4: 16 * 9 * 4 = 576 (but 4 binary is dangerous)")
    print("  a=5: 32 * 3 * 4 = 384 (5 binary)")
    print()

    # But wait — even if we need one 4-state, having 4 binary might work
    # if they're not all consecutive and ARG is satisfied.
    # (2,2,2,2,3,3,4): product = 576. Four binary!
    # RFC: need no 4 consecutive. Arrangement (2,3,2,2,2,3,4):
    #   wrap: 4,2,3,2,2,2,3 — 3 consecutive at positions 3,4,5. OK.
    # ARG: 4 binary, N=2, need LCM >= 3.
    # Blocks between binary: the non-binary processors.
    # Depends on arrangement.

    # So product 576 with (2,2,2,2,3,3,4) is not ruled out by RFC+ARG alone.
    # But the parallel agent says M_7 >= 576 (all products through 512 dead).
    # And product 576 classes are being ground through computationally.

    print("Products below 864 with a 4+ state processor:")

    for product in [576, 600, 624, 640, 648, 672, 720, 768, 800, 810, 840]:
        def factorize7(remaining, depth):
            if depth == 7:
                return [[]] if remaining == 1 else []
            results = []
            min_rest = 2 ** (6 - depth)
            max_f = remaining // min_rest if depth < 6 else remaining
            for f in range(2, max_f + 1):
                if remaining % f == 0:
                    for rest in factorize7(remaining // f, depth + 1):
                        results.append([f] + rest)
            return results

        raw = factorize7(product, 0)
        multisets = set(tuple(sorted(v)) for v in raw)

        # Filter: must have max >= 4
        with_4plus = [ms for ms in multisets if max(ms) >= 4]
        without_4plus = [ms for ms in multisets if max(ms) < 4]

        if with_4plus:
            print(f"  Product {product}: {len(with_4plus)} multisets with 4+ state "
                  f"({len(without_4plus)} without)")
            for ms in sorted(with_4plus)[:3]:
                print(f"    {ms}")

    return


if __name__ == "__main__":
    # First: analyze ARG's constraint strength
    stronger_arg_analysis()

    print()
    print("=" * 60)
    print("PRODUCT GAP ANALYSIS: 577-863")
    print("=" * 60)
    print()

    # For each product in the gap, count feasible vectors
    # and identify which structural constraints rule them out
    n = 7
    gap_products = []

    for product in range(577, 864):
        # Quick: must be >= 2^7 = 128
        if product < 128:
            continue

        # Factor into 7 parts >= 2
        def fact7(rem, d):
            if d == 7:
                return [[]] if rem == 1 else []
            res = []
            mr = rem // (2 ** (6 - d)) if d < 6 else rem
            for f in range(2, mr + 1):
                if rem % f == 0:
                    for r in fact7(rem // f, d + 1):
                        res.append([f] + r)
            return res

        raw = fact7(product, 0)
        if not raw:
            continue

        multisets = set(tuple(sorted(v)) for v in raw)

        # Check RFC for each arrangement
        total_feasible = 0
        has_4plus_feasible = 0
        no_4plus_feasible = 0

        seen = set()
        for ms in multisets:
            for p in set(itertools.permutations(ms)):
                canon = canonical_rotation(p)
                if canon in seen:
                    continue
                seen.add(canon)
                if not has_four_consecutive_binary(list(p)):
                    total_feasible += 1
                    if max(p) >= 4:
                        has_4plus_feasible += 1
                    else:
                        no_4plus_feasible += 1

        if total_feasible > 0:
            gap_products.append((product, total_feasible, has_4plus_feasible, no_4plus_feasible))

    print(f"Products in [577, 863] with feasible vectors: {len(gap_products)}")
    print(f"\nProducts where ALL feasible vectors have max(m_i) >= 4:")
    forced_4plus = [(p, t, h, n) for p, t, h, n in gap_products if n == 0]
    print(f"  Count: {len(forced_4plus)}")

    print(f"\nProducts where some vectors have only 2s and 3s:")
    has_23_only = [(p, t, h, no4) for p, t, h, no4 in gap_products if no4 > 0]
    print(f"  Count: {len(has_23_only)}")
    for p, t, h, no4 in has_23_only[:20]:
        print(f"    Product {p}: {t} total ({no4} with max<=3, {h} with max>=4)")

    print()
    print("KEY INSIGHT: If the 'quaternary necessity' conjecture is true,")
    print("all products that can ONLY be factored into 2s and 3s are dead.")
    print("Products of form 2^a * 3^b with a+b=7:")
    for a in range(8):
        b = 7 - a
        if b >= 0:
            p = 2**a * 3**b
            if 577 <= p <= 863:
                print(f"  2^{a} * 3^{b} = {p}")
