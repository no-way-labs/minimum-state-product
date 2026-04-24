#!/usr/bin/env python3
"""Inventory the exact n=9 frontier below 4*3^7 = 8748.

The main target is the interval (7776, 8748), where Case 1 already eliminates
families with at most two binaries. This script inventories the remaining
multisets with at least three binaries, classifies them by Case 2, and
summarizes the surviving safe orientations by binary run type.
"""

from __future__ import annotations

import argparse
import math
from collections import Counter, defaultdict
import os
import sys

ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from scripts.n9_gap_inventory import inventory_entry
from scripts.n9_sweep import distinct_necklaces
from scripts.verify_lower_bound import has_4_consecutive_binary


def enumerate_frontier_multisets(
    lower_product: int = 7776,
    upper_product: int = 8748,
    n: int = 9,
) -> list[tuple[int, ...]]:
    results: set[tuple[int, ...]] = set()

    def rec(pos: int, last: int, current: list[int], product: int) -> None:
        if pos == n:
            if lower_product < product < upper_product and current.count(2) >= 3:
                results.add(tuple(current))
            return

        candidate = last
        while product * candidate * (2 ** (n - pos - 1)) < upper_product:
            current.append(candidate)
            rec(pos + 1, candidate, current, product * candidate)
            current.pop()
            candidate += 1

    rec(0, 2, [], 1)
    return sorted(results, key=lambda ms: (math.prod(ms), ms.count(2), ms))


def binary_pattern(orientation: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(1 if value == 2 else 0 for value in orientation)


def binary_run_type(pattern: tuple[int, ...]) -> tuple[int, ...]:
    n = len(pattern)
    if sum(pattern) == 0:
        return ()

    runs: list[int] = []
    idx = 0
    while idx < n:
        if pattern[idx] == 0:
            idx += 1
            continue
        end = idx
        while pattern[end % n] == 1:
            end += 1
            if end - idx == n:
                break
        runs.append(end - idx)
        idx = end

    if pattern[0] == 1 and pattern[-1] == 1 and len(runs) >= 2:
        runs = [runs[-1] + runs[0]] + runs[1:-1]
    return tuple(sorted(runs, reverse=True))


def summarize_frontier(lower_product: int, upper_product: int) -> None:
    multisets = enumerate_frontier_multisets(lower_product=lower_product, upper_product=upper_product)
    entries = [inventory_entry(ms) for ms in multisets]

    family_split = Counter(
        "blocked"
        if entry["all_necklaces_blocked_case2"]
        else "all_safe"
        if entry["safe_necklaces_case2"] == entry["necklaces"]
        else "mixed"
        for entry in entries
    )
    binary_histogram = Counter(entry["binary_count"] for entry in entries)

    print(f"frontier interval=({lower_product},{upper_product})")
    print(f"multiset_count={len(entries)}")
    print(f"binary_histogram={dict(sorted(binary_histogram.items()))}")
    print(f"case2_split={dict(sorted(family_split.items()))}")
    print()

    print("multisets:")
    for entry in entries:
        print(
            f"  product={entry['product']} state_counts={tuple(entry['state_counts'])} "
            f"binaries={entry['binary_count']} necklaces={entry['necklaces']} "
            f"safe_necklaces={entry['safe_necklaces_case2']}"
        )
    print()

    run_type_counts: dict[int, Counter[tuple[int, ...]]] = defaultdict(Counter)
    run_type_examples: dict[tuple[int, tuple[int, ...]], tuple[int, ...]] = {}
    safe_necklace_total = 0

    for ms in multisets:
        for orientation in distinct_necklaces(ms):
            if has_4_consecutive_binary(list(orientation), len(orientation)):
                continue
            safe_necklace_total += 1
            pattern = binary_pattern(orientation)
            run_type = binary_run_type(pattern)
            binary_count = sum(pattern)
            run_type_counts[binary_count][run_type] += 1
            run_type_examples.setdefault((binary_count, run_type), orientation)

    print(f"safe_necklace_total={safe_necklace_total}")
    print("binary run types among safe necklaces:")
    for binary_count in sorted(run_type_counts):
        print(f"  binaries={binary_count}")
        for run_type, count in sorted(run_type_counts[binary_count].items()):
            example = run_type_examples[(binary_count, run_type)]
            print(f"    run_type={run_type} count={count} example={example}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lower-product", type=int, default=7776)
    parser.add_argument("--upper-product", type=int, default=8748)
    args = parser.parse_args()
    summarize_frontier(args.lower_product, args.upper_product)


if __name__ == "__main__":
    main()
