from __future__ import annotations

import argparse
import json
import math
import os
import sys
from collections import Counter

sys.path.append(os.path.dirname(os.path.dirname(__file__)))

from scripts.n9_sweep import distinct_necklaces
from scripts.verify_lower_bound import has_4_consecutive_binary


def enumerate_gap_multisets(
    lower_product: int = 8748,
    upper_product: int = 13122,
    n: int = 9,
) -> list[tuple[int, ...]]:
    results: set[tuple[int, ...]] = set()

    def rec(pos: int, last: int, current: list[int], product: int) -> None:
        if pos == n:
            if lower_product < product < upper_product and current.count(2) >= 2:
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


def linear_orientation_count(ms: tuple[int, ...]) -> int:
    counts = Counter(ms)
    total = math.factorial(len(ms))
    for count in counts.values():
        total //= math.factorial(count)
    return total


def inventory_entry(ms: tuple[int, ...]) -> dict:
    necklaces = distinct_necklaces(ms)
    blocked_necklaces = sum(
        1 for orientation in necklaces if has_4_consecutive_binary(list(orientation), len(ms))
    )
    return {
        "state_counts": list(ms),
        "product": math.prod(ms),
        "binary_count": ms.count(2),
        "linear_orientations": linear_orientation_count(ms),
        "necklaces": len(necklaces),
        "blocked_necklaces_case2": blocked_necklaces,
        "safe_necklaces_case2": len(necklaces) - blocked_necklaces,
        "all_necklaces_blocked_case2": blocked_necklaces == len(necklaces),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json-out")
    args = parser.parse_args()

    entries = [inventory_entry(ms) for ms in enumerate_gap_multisets()]
    print(
        "product,binary_count,linear_orientations,necklaces,blocked_necklaces,safe_necklaces,state_counts"
    )
    for entry in entries:
        print(
            f"{entry['product']},{entry['binary_count']},{entry['linear_orientations']},"
            f"{entry['necklaces']},{entry['blocked_necklaces_case2']},"
            f"{entry['safe_necklaces_case2']},{tuple(entry['state_counts'])}"
        )

    if args.json_out:
        with open(args.json_out, "w") as handle:
            json.dump(entries, handle, indent=2, sort_keys=True)


if __name__ == "__main__":
    main()
