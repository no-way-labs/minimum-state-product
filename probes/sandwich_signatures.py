"""
Enumerate local 5-tuple signatures (m_{t-2}, 2, m_t, 2, m_{t+2}) around
sandwiched ternary pivots in sub-threshold rings.

Sub-threshold: product < 4 * 3^(n-2), each m_i >= 2, >= 3 binary.
Sandwiched ternary: m_t >= 3 with m_{t-1} = 2, m_{t+1} = 2.
"""

from itertools import combinations_with_replacement
from collections import Counter
import math

def enum_multisets(n, max_product):
    """Enumerate all sorted multisets of n values >= 2 with product < max_product and >= 3 twos."""
    results = []

    def backtrack(remaining, min_val, current, current_product):
        if remaining == 0:
            if current_product < max_product and current.count(2) >= 3:
                results.append(tuple(current))
            return
        # max possible value: max_product / (current_product * 2^(remaining-1))
        max_val = max_product // (current_product * (2 ** (remaining - 1)))
        if max_val < min_val:
            return
        for v in range(min_val, max_val + 1):
            new_product = current_product * v
            if new_product * (2 ** (remaining - 1)) >= max_product:
                break
            backtrack(remaining - 1, v, current + [v], new_product)

    backtrack(n, 2, [], 1)
    return results


def get_5tuples_from_multiset(ms):
    """
    For a multiset ms (sorted tuple), find all possible (a, b, c) where:
    - b >= 3 is taken from ms
    - Two 2's are taken from ms (for t-1, t+1)
    - a, c are any two values from the remaining elements
    - (a, b, c) means 5-tuple is (a, 2, b, 2, c)

    In a ring arrangement, after placing ...a, 2, b, 2, c... the remaining
    n-5 values fill the rest. We need n >= 5 for a 5-tuple to exist,
    and the remaining values just need to exist (any arrangement works
    since rings are flexible).

    We need: the multiset has b (>=3), at least two 2's, and after removing
    b and two 2's, at least 2 more values for a and c.
    So n >= 5.

    For a and c: they are ORDERED (a is at t-2, c is at t+2), and they
    are drawn from the remaining multiset (after removing b and two 2's).
    We pick two from remaining WITH regard to multiplicity, ordered.
    """
    n = len(ms)
    if n < 5:
        return set()

    counter = Counter(ms)
    tuples_5 = set()

    # For each possible b >= 3
    distinct_b = set(v for v in counter if v >= 3)

    for b in distinct_b:
        # Check we can remove b and two 2's
        temp = Counter(counter)
        temp[b] -= 1
        if temp[b] < 0:
            continue
        if temp[2] < 2:
            continue
        temp[2] -= 2

        # Remaining values (n-3 of them)
        remaining = []
        for v, cnt in sorted(temp.items()):
            if cnt > 0:
                remaining.extend([v] * cnt)

        if len(remaining) < 2:
            continue

        # a and c are any ordered pair from remaining (allowing same value
        # if multiplicity permits)
        rem_counter = Counter(remaining)
        distinct_rem = sorted(rem_counter.keys())

        for a in distinct_rem:
            for c in distinct_rem:
                # Check we can pick both a and c
                if a == c:
                    if rem_counter[a] >= 2:
                        tuples_5.add((a, 2, b, 2, c))
                else:
                    tuples_5.add((a, 2, b, 2, c))

    return tuples_5


def main():
    all_results = {}

    for n in [9, 10, 11, 12]:
        threshold = 4 * (3 ** (n - 2))
        print(f"\n{'='*60}")
        print(f"n = {n}, threshold = {threshold}")
        print(f"{'='*60}")

        multisets = enum_multisets(n, threshold)
        print(f"  Number of sub-threshold multisets (>=3 binary): {len(multisets)}")

        all_tuples = set()
        for ms in multisets:
            t5 = get_5tuples_from_multiset(ms)
            all_tuples.update(t5)

        # Sort for display
        sorted_tuples = sorted(all_tuples)
        print(f"  Number of distinct 5-tuples: {len(sorted_tuples)}")

        # Group by the variable triple (a, b, c)
        triples = sorted(set((a, b, c) for (a, _, b, _, c) in sorted_tuples))
        print(f"  Distinct (m_{{t-2}}, m_t, m_{{t+2}}) triples: {len(triples)}")
        for t in triples:
            print(f"    {t}")

        all_results[n] = set(triples)

    # Stabilization check
    print(f"\n{'='*60}")
    print("STABILIZATION CHECK")
    print(f"{'='*60}")

    ns = [9, 10, 11, 12]
    for i in range(len(ns) - 1):
        n1, n2 = ns[i], ns[i+1]
        s1, s2 = all_results[n1], all_results[n2]
        if s1 == s2:
            print(f"  n={n1} -> n={n2}: IDENTICAL ({len(s1)} triples)")
        else:
            new = s2 - s1
            lost = s1 - s2
            print(f"  n={n1} -> n={n2}: DIFFERENT")
            if new:
                print(f"    New at n={n2}: {sorted(new)}")
            if lost:
                print(f"    Lost at n={n2}: {sorted(lost)}")

    # Check if 9 == 12
    if all_results[9] == all_results[12]:
        print(f"\n  n=9 vs n=12: IDENTICAL -- fully stabilized")
    else:
        print(f"\n  n=9 vs n=12: DIFFERENT")
        print(f"    n=9 only: {sorted(all_results[9] - all_results[12])}")
        print(f"    n=12 only: {sorted(all_results[12] - all_results[9])}")

    # Show the stable core (intersection of all)
    core = all_results[9] & all_results[10] & all_results[11] & all_results[12]
    print(f"\n  Core triples (present at ALL n=9..12): {len(core)}")
    for t in sorted(core):
        print(f"    {t}")

    # Union
    union = all_results[9] | all_results[10] | all_results[11] | all_results[12]
    print(f"\n  Union of all triples: {len(union)}")
    for t in sorted(union):
        present = [n for n in ns if t in all_results[n]]
        print(f"    {t}  present at n={present}")


if __name__ == "__main__":
    main()
