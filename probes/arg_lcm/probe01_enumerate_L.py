"""probe01: enumerate ARG's L under each reading (R1/R2/R3) across all
non-adjacent orientations of target multisets.

Purpose: check whether any of R1 (global-LCM), R2 (per-arc LCM),
R3 (block-product LCM) distinguishes n=8 valid {2^3, 3^4, 4} from
n=9 invalid {2^3, 3^5, 4}, and likewise other small-n known valid/invalid
cases.

No external deps. stdlib only.
"""

from __future__ import annotations
from collections import Counter
from functools import reduce
from itertools import combinations, permutations
from math import gcd, prod


def lcm(a: int, b: int) -> int:
    return a * b // gcd(a, b) if a and b else 0


def lcm_all(xs):
    xs = [x for x in xs if x > 0]
    if not xs:
        return 1
    return reduce(lcm, xs)


def arcs_between_binaries(ms: tuple[int, ...]) -> list[list[int]] | None:
    """Given state-count tuple ms of length n around a ring, find the arcs
    (maximal runs of non-binary between binaries). Returns None if binaries
    are adjacent (per ARG's hypothesis)."""
    n = len(ms)
    binary_positions = [i for i, m in enumerate(ms) if m == 2]
    if not binary_positions:
        return []
    # Non-adjacency check
    for idx, pos in enumerate(binary_positions):
        nxt = binary_positions[(idx + 1) % len(binary_positions)]
        gap = (nxt - pos) % n
        if gap <= 1:  # adjacent binaries (gap==1) or same (should not happen)
            return None
    # Build arcs: for each consecutive pair of binaries (cyclic), the arc
    # between them is the stretch of non-binary positions.
    arcs = []
    for idx, pos in enumerate(binary_positions):
        nxt = binary_positions[(idx + 1) % len(binary_positions)]
        arc_positions = []
        i = (pos + 1) % n
        while i != nxt:
            arc_positions.append(i)
            i = (i + 1) % n
        arcs.append([ms[j] for j in arc_positions])
    return arcs


def R1_global_lcm(ms: tuple[int, ...]) -> int:
    """Global LCM of non-binary state counts."""
    non_binaries = [m for m in ms if m != 2]
    return lcm_all(non_binaries)


def R2_min_per_arc_lcm(arcs: list[list[int]]) -> int:
    """Minimum over arcs of the per-arc LCM."""
    if not arcs:
        return 1
    return min(lcm_all(arc) for arc in arcs)


def R2_max_per_arc_lcm(arcs: list[list[int]]) -> int:
    if not arcs:
        return 1
    return max(lcm_all(arc) for arc in arcs)


def R3_block_product_lcm(arcs: list[list[int]]) -> int:
    """LCM of the block-products (number of configurations per block)."""
    if not arcs:
        return 1
    block_products = [prod(arc) for arc in arcs]
    return lcm_all(block_products)


def max_arc_length(arcs: list[list[int]]) -> int:
    if not arcs:
        return 0
    return max(len(arc) for arc in arcs)


def enumerate_orientations(multiset: list[int], n: int):
    """Enumerate all distinct cyclic-rotation-inequivalent + reflection-inequivalent
    orientations of the multiset around a ring of length n. For probe purposes,
    we emit all distinct tuples ms (up to cyclic rotation) that realize the multiset.
    We use a canonical-form filter: rotate to lex-smallest, then include only those.
    Reflections kept distinct (since ring left/right neighbors are distinct)."""
    assert len(multiset) == n
    seen = set()
    for perm in set(permutations(multiset)):
        # canonical cyclic rotation: lex-smallest rotation
        rotations = [perm[i:] + perm[:i] for i in range(n)]
        canonical = min(rotations)
        if canonical in seen:
            continue
        seen.add(canonical)
        yield canonical


def summarize(multiset: list[int], n: int, label: str):
    print(f"\n=== {label}: n={n}, multiset={multiset} (product={prod(multiset)}) ===")
    orientations = list(enumerate_orientations(multiset, n))
    print(f"Distinct orientations (up to rotation): {len(orientations)}")
    non_adj = []
    adj = []
    for ms in orientations:
        arcs = arcs_between_binaries(ms)
        if arcs is None:
            adj.append(ms)
        else:
            non_adj.append((ms, arcs))
    print(f"  non-adjacent binary orientations: {len(non_adj)}")
    print(f"  adjacent-binary orientations:     {len(adj)}")

    if not non_adj:
        print("  (all have adjacent binaries — ARG's theorem N/A)")
        return

    # Collect R1/R2/R3 and arc-length stats across non-adjacent orientations
    R1_vals = set()
    R2min_vals = set()
    R2max_vals = set()
    R3_vals = set()
    arc_len_maxes = set()
    arc_len_partitions = set()
    for ms, arcs in non_adj:
        R1_vals.add(R1_global_lcm(ms))
        R2min_vals.add(R2_min_per_arc_lcm(arcs))
        R2max_vals.add(R2_max_per_arc_lcm(arcs))
        R3_vals.add(R3_block_product_lcm(arcs))
        arc_len_maxes.add(max_arc_length(arcs))
        arc_len_partitions.add(tuple(sorted(len(a) for a in arcs)))
    k = sum(1 for m in multiset if m == 2)
    print(f"  k (binary count): {k}")
    print(f"  arc-length partitions: {sorted(arc_len_partitions)}")
    print(f"  max arc length (over orientations): {sorted(arc_len_maxes)}")
    print(f"  R1 L values: {sorted(R1_vals)}")
    print(f"  R2 min-per-arc LCM values: {sorted(R2min_vals)}")
    print(f"  R2 max-per-arc LCM values: {sorted(R2max_vals)}")
    print(f"  R3 block-product LCM values: {sorted(R3_vals)}")


def main():
    # Target cases: known-valid vs known-invalid (from primer)
    cases = [
        # n=5: M_5 = 96 = 2^5 * 3. Minimal multiset = {2,2,2,3,4}
        ([2, 2, 2, 3, 4], 5, "n=5 M_5 witness VALID {2^3, 3, 4}"),
        ([2, 2, 3, 3, 3], 5, "n=5 alt invalid {2^2, 3^3} prod=108"),
        # n=6: M_6 = 96. witnesses at prod=96.
        ([2, 2, 2, 2, 2, 3], 6, "n=6 invalid {2^5, 3} prod=96 (too many binaries)"),
        ([2, 2, 2, 3, 4], 5, "(dup) n=5 base"),
        ([2, 4, 2, 4, 2, 4], 6, "n=6 INVALID [2,4,2,4,2,4] prod=512 (from transcript)"),
        # n=8: M_8 = 2592 = 2^3 * 3^4 * 4.
        ([2, 2, 2, 3, 3, 3, 3, 4], 8, "n=8 VALID {2^3, 3^4, 4} prod=2592"),
        # n=9: M_9 = 8748. Target product-7776 cases (all invalid).
        ([2, 2, 2, 3, 3, 3, 3, 3, 4], 9, "n=9 INVALID {2^3, 3^5, 4} prod=7776"),
        # n=9 other product-7776 multisets per primer:
        ([2, 2, 2, 2, 3, 3, 3, 3, 6], 9, "n=9 INVALID {2^4, 3^4, 6} prod=7776"),
        ([2, 2, 2, 2, 2, 3, 3, 3, 9], 9, "n=9 INVALID {2^5, 3^3, 9} prod=7776"),
        # n=7: for calibration (M_7 = 32*3^3 = 864)
        ([2, 2, 2, 3, 3, 3, 4], 7, "n=7 VALID {2^3, 3^3, 4} prod=864"),
    ]
    for multiset, n, label in cases:
        summarize(list(multiset), n, label)


if __name__ == "__main__":
    main()
