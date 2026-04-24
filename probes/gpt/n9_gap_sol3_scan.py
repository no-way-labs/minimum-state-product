from __future__ import annotations

import argparse
import math
import os
import sys
import time
from itertools import permutations

sys.path.append(os.path.dirname(os.path.dirname(__file__)))

from scripts.sol3_adapt import VARIANTS, build_system
from scripts.verify_witnesses import verify as verify_five_properties
from scripts.n9_gap_inventory import enumerate_gap_multisets
from scripts.verify_lower_bound import has_4_consecutive_binary
from p2_ring import verify_system


def unique_orientations(ms: tuple[int, ...]) -> list[tuple[int, ...]]:
    return sorted(set(permutations(ms)))


def parse_multiset(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiset", action="append", help="comma-separated state counts")
    parser.add_argument(
        "--variant",
        action="append",
        choices=sorted(VARIANTS),
        help="limit to one or more Sol 3 variants",
    )
    parser.add_argument(
        "--safe-only",
        action="store_true",
        help="skip orientations with 4+ consecutive binary processors",
    )
    parser.add_argument(
        "--stop-on-witness",
        action="store_true",
        help="stop immediately once a valid witness is found",
    )
    args = parser.parse_args()

    variants = args.variant or sorted(VARIANTS)
    multisets = (
        [parse_multiset(text) for text in args.multiset]
        if args.multiset
        else enumerate_gap_multisets()
    )

    total_tested = 0
    began = time.time()
    for ms in multisets:
        product = math.prod(ms)
        orientations = unique_orientations(ms)
        if args.safe_only:
            orientations = [
                orientation
                for orientation in orientations
                if not has_4_consecutive_binary(list(orientation), len(orientation))
            ]
        print(
            f"multiset={ms} product={product} orientations={len(orientations)} "
            f"variants={','.join(variants)}"
        )
        for orientation in orientations:
            for variant in variants:
                total_tested += 1
                system = build_system(orientation, VARIANTS[variant])
                graph_result = verify_system(system)
                if not graph_result.valid:
                    continue
                cycle_lengths = tuple(summary.length for summary in graph_result.cycle_summaries)
                print(
                    f"WITNESS graph-valid: variant={variant} orientation={orientation} "
                    f"cycle_lengths={cycle_lengths} total_configs={graph_result.configuration_count}"
                )
                five_ok = verify_five_properties(
                    f"{variant}-{orientation}",
                    system.state_counts,
                    system.rules,
                )
                print(f"five_properties={five_ok}")
                if args.stop_on_witness:
                    print(
                        f"tested={total_tested} elapsed={time.time() - began:.3f}s"
                    )
                    return
        print("  no Sol 3 witness found")

    print(f"tested={total_tested} elapsed={time.time() - began:.3f}s")


if __name__ == "__main__":
    main()
