#!/usr/bin/env python3
"""Probe the exact n=9 frontier with a calibrated 25-step bounce seed.

The seed mover sequence is

    0,1,...,8,7,...,1,0,1,...,8

which has length 25 and admits a locally consistent good cycle on the
architecture `(2,3,3,3,3,3,3,3,2)`.
"""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter, OrderedDict


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from scripts.glb_sub8748_inventory import binary_pattern, binary_run_type, enumerate_frontier_multisets
from scripts.n9_sweep import distinct_necklaces
from scripts.p2_seeded_cycle_search import solve_good_cycle_from_movers
from scripts.verify_lower_bound import has_4_consecutive_binary


BOUNCE_25_MOVERS = tuple(list(range(9)) + list(range(7, 0, -1)) + list(range(9)))


def parse_state_counts(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def safe_orientations(ms: tuple[int, ...]) -> list[tuple[int, ...]]:
    return [
        orientation
        for orientation in distinct_necklaces(ms)
        if not has_4_consecutive_binary(list(orientation), len(orientation))
    ]


def mover_variants(family: str) -> list[tuple[int, ...]]:
    def shifts(word: tuple[int, ...]) -> list[tuple[int, ...]]:
        return [word[offset:] + word[:offset] for offset in range(len(word))]

    if family == "base":
        return [BOUNCE_25_MOVERS]
    if family == "shifts":
        return shifts(BOUNCE_25_MOVERS)
    if family == "dihedral":
        variants: OrderedDict[tuple[int, ...], None] = OrderedDict()
        for word in (BOUNCE_25_MOVERS, tuple(reversed(BOUNCE_25_MOVERS))):
            for variant in shifts(word):
                variants.setdefault(variant, None)
        return list(variants)
    raise ValueError(f"unsupported mover family: {family}")


def result_kind(message: str) -> str:
    if "unknown" in message:
        return "unknown"
    return "unsat"


def even_count_processors(movers: tuple[int, ...], n: int) -> tuple[int, ...]:
    counts = Counter(movers)
    return tuple(processor for processor in range(n) if counts[processor] % 2 == 0)


def binary_parity_compatible(state_counts: tuple[int, ...], movers: tuple[int, ...]) -> bool:
    counts = Counter(movers)
    for processor, state_count in enumerate(state_counts):
        if state_count == 2 and counts[processor] % 2 == 1:
            return False
    return True


def representative_safe_orientations_by_run_type(
    lower_product: int,
    upper_product: int,
) -> list[tuple[tuple[int, tuple[int, ...]], tuple[int, ...]]]:
    representatives: OrderedDict[tuple[int, tuple[int, ...]], tuple[int, ...]] = OrderedDict()
    for ms in enumerate_frontier_multisets(lower_product=lower_product, upper_product=upper_product):
        for orientation in safe_orientations(ms):
            pattern = binary_pattern(orientation)
            key = (sum(pattern), binary_run_type(pattern))
            representatives.setdefault(key, orientation)
    return list(representatives.items())


def run_probe(label: str, state_counts: tuple[int, ...], timeout_ms: int) -> None:
    result = solve_good_cycle_from_movers(state_counts, BOUNCE_25_MOVERS, timeout_ms=timeout_ms)
    print(
        f"{label}: state_counts={state_counts} found={result.found} "
        f"elapsed={result.elapsed:.3f}s message={result.message}"
    )


def mode_witness(timeout_ms: int) -> None:
    run_probe("bound_witness_shape", (2, 3, 3, 3, 3, 3, 3, 3, 2), timeout_ms)


def mode_frontier_canonical(lower_product: int, upper_product: int, timeout_ms: int) -> None:
    for ms in enumerate_frontier_multisets(lower_product=lower_product, upper_product=upper_product):
        orientations = safe_orientations(ms)
        if not orientations:
            continue
        run_probe("canonical_safe", orientations[0], timeout_ms)


def mode_frontier_all(lower_product: int, upper_product: int, timeout_ms: int, stop_on_hit: bool) -> None:
    for ms in enumerate_frontier_multisets(lower_product=lower_product, upper_product=upper_product):
        orientations = safe_orientations(ms)
        if not orientations:
            continue
        hits = 0
        for index, orientation in enumerate(orientations, start=1):
            result = solve_good_cycle_from_movers(orientation, BOUNCE_25_MOVERS, timeout_ms=timeout_ms)
            if result.found:
                hits += 1
                print(
                    f"HIT multiset={ms} orientation={index}/{len(orientations)} "
                    f"state_counts={orientation} elapsed={result.elapsed:.3f}s"
                )
                if stop_on_hit:
                    return
        print(f"multiset={ms} safe_orientations={len(orientations)} seeded_hits={hits}")


def mode_minimality(timeout_ms: int) -> None:
    base = [2, 3, 3, 3, 3, 3, 3, 3, 2]
    base_result = solve_good_cycle_from_movers(tuple(base), BOUNCE_25_MOVERS, timeout_ms=timeout_ms)
    print(
        f"base state_counts={tuple(base)} found={base_result.found} "
        f"elapsed={base_result.elapsed:.3f}s message={base_result.message}"
    )
    for processor, value in enumerate(base):
        if value <= 2:
            continue
        lowered = list(base)
        lowered[processor] -= 1
        result = solve_good_cycle_from_movers(tuple(lowered), BOUNCE_25_MOVERS, timeout_ms=timeout_ms)
        print(
            f"lowered processor={processor} state_counts={tuple(lowered)} "
            f"found={result.found} elapsed={result.elapsed:.3f}s message={result.message}"
        )


def mode_variant_witness(timeout_ms: int, family: str) -> None:
    variants = mover_variants(family)
    hits = 0
    unknowns = 0
    for index, movers in enumerate(variants, start=1):
        result = solve_good_cycle_from_movers((2, 3, 3, 3, 3, 3, 3, 3, 2), movers, timeout_ms=timeout_ms)
        if result.found:
            hits += 1
        elif result_kind(result.message) == "unknown":
            unknowns += 1
        print(
            f"variant={index}/{len(variants)} family={family} found={result.found} "
            f"elapsed={result.elapsed:.3f}s message={result.message}"
        )
    print(f"summary family={family} variants={len(variants)} hits={hits} unknowns={unknowns}")


def mode_variant_run_types(lower_product: int, upper_product: int, timeout_ms: int, family: str) -> None:
    variants = mover_variants(family)
    for key, orientation in representative_safe_orientations_by_run_type(lower_product, upper_product):
        hits = 0
        unknowns = 0
        first_hit = None
        for index, movers in enumerate(variants, start=1):
            result = solve_good_cycle_from_movers(orientation, movers, timeout_ms=timeout_ms)
            if result.found:
                hits += 1
                if first_hit is None:
                    first_hit = index
            elif result_kind(result.message) == "unknown":
                unknowns += 1
        print(
            f"run_type={key} orientation={orientation} family={family} "
            f"variants={len(variants)} hits={hits} unknowns={unknowns} first_hit={first_hit}"
        )


def mode_variant_frontier_canonical(lower_product: int, upper_product: int, timeout_ms: int, family: str) -> None:
    variants = mover_variants(family)
    for ms in enumerate_frontier_multisets(lower_product=lower_product, upper_product=upper_product):
        orientations = safe_orientations(ms)
        if not orientations:
            continue
        orientation = orientations[0]
        hits = 0
        unknowns = 0
        first_hit = None
        for index, movers in enumerate(variants, start=1):
            result = solve_good_cycle_from_movers(orientation, movers, timeout_ms=timeout_ms)
            if result.found:
                hits += 1
                if first_hit is None:
                    first_hit = index
            elif result_kind(result.message) == "unknown":
                unknowns += 1
        print(
            f"multiset={ms} canonical={orientation} family={family} "
            f"variants={len(variants)} hits={hits} unknowns={unknowns} first_hit={first_hit}"
        )


def mode_variant_frontier_all(
    lower_product: int,
    upper_product: int,
    timeout_ms: int,
    family: str,
    stop_on_hit: bool,
) -> None:
    variants = mover_variants(family)
    total_orientations = 0
    total_checks = 0
    parity_blocked = 0
    sat_hits = 0
    unknowns = 0

    for ms in enumerate_frontier_multisets(lower_product=lower_product, upper_product=upper_product):
        orientations = safe_orientations(ms)
        if not orientations:
            continue

        multiset_checks = 0
        multiset_parity_blocked = 0
        multiset_hits = 0
        multiset_unknowns = 0

        for orientation in orientations:
            total_orientations += 1
            for movers in variants:
                total_checks += 1
                multiset_checks += 1
                if not binary_parity_compatible(orientation, movers):
                    parity_blocked += 1
                    multiset_parity_blocked += 1
                    continue
                result = solve_good_cycle_from_movers(orientation, movers, timeout_ms=timeout_ms)
                if result.found:
                    sat_hits += 1
                    multiset_hits += 1
                    print(
                        f"HIT multiset={ms} orientation={orientation} family={family} "
                        f"elapsed={result.elapsed:.3f}s even_count_processors={even_count_processors(movers, len(orientation))}"
                    )
                    if stop_on_hit:
                        return
                elif result_kind(result.message) == "unknown":
                    unknowns += 1
                    multiset_unknowns += 1

        print(
            f"multiset={ms} safe_orientations={len(orientations)} family={family} variants={len(variants)} "
            f"checks={multiset_checks} parity_blocked={multiset_parity_blocked} "
            f"hits={multiset_hits} unknowns={multiset_unknowns}"
        )

    print(
        f"summary family={family} total_orientations={total_orientations} total_checks={total_checks} "
        f"parity_blocked={parity_blocked} sat_hits={sat_hits} unknowns={unknowns}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--mode",
        choices=(
            "witness",
            "frontier-canonical",
            "frontier-all",
            "minimality",
            "variant-witness",
            "variant-run-types",
            "variant-frontier-canonical",
            "variant-frontier-all",
            "custom",
        ),
        default="witness",
    )
    parser.add_argument("--state-counts", action="append", help="comma-separated state counts for --mode custom")
    parser.add_argument("--lower-product", type=int, default=7776)
    parser.add_argument("--upper-product", type=int, default=8748)
    parser.add_argument("--timeout-ms", type=int, default=5000)
    parser.add_argument("--variant-family", choices=("base", "shifts", "dihedral"), default="shifts")
    parser.add_argument("--stop-on-hit", action="store_true")
    args = parser.parse_args()

    if args.mode == "witness":
        mode_witness(args.timeout_ms)
        return
    if args.mode == "frontier-canonical":
        mode_frontier_canonical(args.lower_product, args.upper_product, args.timeout_ms)
        return
    if args.mode == "frontier-all":
        mode_frontier_all(args.lower_product, args.upper_product, args.timeout_ms, args.stop_on_hit)
        return
    if args.mode == "minimality":
        mode_minimality(args.timeout_ms)
        return
    if args.mode == "variant-witness":
        mode_variant_witness(args.timeout_ms, args.variant_family)
        return
    if args.mode == "variant-run-types":
        mode_variant_run_types(args.lower_product, args.upper_product, args.timeout_ms, args.variant_family)
        return
    if args.mode == "variant-frontier-canonical":
        mode_variant_frontier_canonical(args.lower_product, args.upper_product, args.timeout_ms, args.variant_family)
        return
    if args.mode == "variant-frontier-all":
        mode_variant_frontier_all(
            args.lower_product,
            args.upper_product,
            args.timeout_ms,
            args.variant_family,
            args.stop_on_hit,
        )
        return
    if args.mode == "custom":
        if not args.state_counts:
            raise SystemExit("--state-counts is required for --mode custom")
        for index, text in enumerate(args.state_counts):
            run_probe(f"custom_{index}", parse_state_counts(text), args.timeout_ms)
        return


if __name__ == "__main__":
    main()
