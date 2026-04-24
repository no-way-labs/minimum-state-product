#!/usr/bin/env python3
"""arg_n9_verify.py — Appendix A of dispatch note
"ARG-LCM does not induce the n=9 phase transition."

Enumerates all distinct non-adjacent orientations of the multiset
{2^3, 3^(n-4), 4} on a ring of length n for n = 7, 8, 9, and computes
four candidate LCM functionals corresponding to the three readings of
ARG's 1985 LCM bound (STAN-CS-85-1055, p. 79):

  R1        — global LCM of non-binary state counts
  R2 (min)  — minimum over arcs of per-arc LCM
  R2 (max)  — maximum over arcs of per-arc LCM
  R3        — LCM of arc block-products

Reproduces Theorem 3.1 of the dispatch note.

Python-standard-library only. Deterministic, no randomness. Runtime < 1 s.

Run: `python3 arg_n9_verify.py`
"""

from functools import reduce
from itertools import permutations
from math import gcd, prod


def lcm(a: int, b: int) -> int:
    return a * b // gcd(a, b) if a and b else 0


def lcm_all(xs):
    xs = [x for x in xs if x > 0]
    return reduce(lcm, xs) if xs else 1


def arcs_between_binaries(ms):
    """Return the list of arcs (non-binary runs between consecutive binaries
    cyclically). Return None if any two binaries are cyclically adjacent."""
    n = len(ms)
    binary_positions = [i for i, m in enumerate(ms) if m == 2]
    for idx, pos in enumerate(binary_positions):
        nxt = binary_positions[(idx + 1) % len(binary_positions)]
        gap = (nxt - pos) % n
        if gap <= 1:
            return None
    arcs = []
    for idx, pos in enumerate(binary_positions):
        nxt = binary_positions[(idx + 1) % len(binary_positions)]
        arc = []
        i = (pos + 1) % n
        while i != nxt:
            arc.append(ms[i])
            i = (i + 1) % n
        arcs.append(arc)
    return arcs


def distinct_orientations(multiset):
    """Yield distinct tuples ms (up to cyclic rotation) realizing the multiset."""
    n = len(multiset)
    seen = set()
    for perm in set(permutations(multiset)):
        rotations = [perm[i:] + perm[:i] for i in range(n)]
        canonical = min(rotations)
        if canonical not in seen:
            seen.add(canonical)
            yield canonical


def compute_readings(n, multiset):
    """For the given multiset on a ring of length n, enumerate non-adjacent
    orientations and return the sets of values for R1, R2min, R2max, R3."""
    R1 = set()
    R2min = set()
    R2max = set()
    R3 = set()
    nonadj_count = 0
    total_count = 0
    for ms in distinct_orientations(multiset):
        total_count += 1
        arcs = arcs_between_binaries(ms)
        if arcs is None:
            continue
        nonadj_count += 1
        nonbinary = [m for m in ms if m != 2]
        R1.add(lcm_all(nonbinary))
        per_arc_lcms = [lcm_all(a) for a in arcs]
        R2min.add(min(per_arc_lcms))
        R2max.add(max(per_arc_lcms))
        R3.add(lcm_all([prod(a) for a in arcs]))
    return {
        "total_orientations": total_count,
        "non_adjacent_orientations": nonadj_count,
        "R1": sorted(R1),
        "R2_min": sorted(R2min),
        "R2_max": sorted(R2max),
        "R3": sorted(R3),
    }


def target_multiset(n):
    """{2^3, 3^(n-4), 4} multiset."""
    assert n >= 5
    return [2, 2, 2] + [3] * (n - 4) + [4]


def format_set(s):
    return "{" + ", ".join(str(x) for x in s) + "}"


def main():
    print("=" * 72)
    print("ARG-LCM Insensitivity Theorem — verification table")
    print("=" * 72)
    print()
    print("Target multiset: {2^3, 3^(n-4), 4}")
    print()
    header = f"{'n':>3} | {'prod':>6} | {'orients':>7} | {'nonadj':>6} | "\
             f"{'R1':<10} | {'R2_min':<10} | {'R2_max':<10} | {'R3':<20}"
    print(header)
    print("-" * len(header))
    for n in (7, 8, 9):
        ms = target_multiset(n)
        P = prod(ms)
        result = compute_readings(n, ms)
        print(
            f"{n:>3} | {P:>6} | {result['total_orientations']:>7} | "
            f"{result['non_adjacent_orientations']:>6} | "
            f"{format_set(result['R1']):<10} | "
            f"{format_set(result['R2_min']):<10} | "
            f"{format_set(result['R2_max']):<10} | "
            f"{format_set(result['R3']):<20}"
        )
    print()
    print("Validity status (from docs/verify_witnesses.py + exhaustive search):")
    print("  n=7: M_7 = 864 achieved (ms=(3,2,2,2,3,4,3), adjacent-binary witness)")
    print("  n=8: M_8 = 2592 achieved (ms=(2,2,3,4,3,3,2,3), adjacent-binary witness)")
    print("  n=9: ALL 56 orientations of {2^3, 3^5, 4} FAIL (M_9 > 7776)")
    print()
    print("Key observation (Insensitivity Theorem):")
    print("  R1, R2_min, R2_max — value sets are EQUAL across n=7, 8, 9.")
    print("  R3 — value set at n=9 strictly contains n=8's, which contains n=7's.")
    print()
    print("Consequence: no separating LCM-functional bound can isolate the")
    print("invalid n=9 multiset from the (non-adjacent orientations of the)")
    print("valid-family n=7, 8 multisets. ARG's LCM technique does not")
    print("induce the n=9 phase transition.")


if __name__ == "__main__":
    main()
