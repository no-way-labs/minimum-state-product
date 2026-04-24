#!/usr/bin/env python3
"""Probe and cluster three-sweep assignment laws across true Case 3c gap patterns."""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter
from itertools import product


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from scripts.glb_case3c_starpower_probe import predicted_status
from scripts.glb_three_sweep_assignment_scan import assignment_rows


TRUE_N9_GAPS: tuple[tuple[int, int, int], ...] = (
    (1, 2, 3),
    (1, 1, 4),
    (1, 3, 2),
    (2, 2, 2),
)


def parse_int_tuple(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def canonical_gap_pattern(gaps: tuple[int, int, int]) -> tuple[int, int, int]:
    rotations = (
        gaps,
        (gaps[1], gaps[2], gaps[0]),
        (gaps[2], gaps[0], gaps[1]),
    )
    return min(rotations)


def true_case3c_gap_patterns(n: int) -> tuple[tuple[int, int, int], ...]:
    if n < 9:
        raise ValueError("true Case 3c requires n >= 9")

    seen: set[tuple[int, int, int]] = set()
    patterns: list[tuple[int, int, int]] = []
    total_gap = n - 3

    for first, second in product(range(1, total_gap - 1), repeat=2):
        third = total_gap - first - second
        if third < 1:
            continue
        canonical = canonical_gap_pattern((first, second, third))
        if canonical in seen:
            continue
        seen.add(canonical)
        patterns.append(canonical)

    return tuple(sorted(patterns))


def state_counts_from_gaps(gaps: tuple[int, int, int]) -> tuple[int, ...]:
    if len(gaps) != 3:
        raise ValueError("Case 3c gap pattern must have exactly three entries")

    n = sum(gaps) + 3
    state_counts = [3] * n

    position = 0
    binaries = [position]
    for gap in gaps[:-1]:
        position += gap + 1
        binaries.append(position)

    for binary in binaries:
        state_counts[binary] = 2
    state_counts[-1] = 4
    return tuple(state_counts)


def family_spec_from_state_counts(
    state_counts: tuple[int, ...],
    orientation: str,
    include_upper_wiggle: bool,
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    n = len(state_counts)
    binaries = [index for index, value in enumerate(state_counts) if value == 2]
    if len(binaries) != 3 or binaries[0] != 0 or state_counts[-1] != 4:
        raise ValueError("state_counts must be normalized with a binary at 0 and a quaternary at n-1")

    if orientation == "reverse":
        interior_edges = tuple(binary - 1 for binary in binaries[1:])
        tail = (0, n - 1)
    elif orientation == "forward":
        interior_edges = tuple(binaries[1:])
        tail = (0, 1)
    else:
        raise ValueError(f"unsupported orientation: {orientation}")

    if include_upper_wiggle:
        interior_edges += (n - 2,)
    return interior_edges, tail


def classify_family(
    state_counts: tuple[int, ...],
    orientation: str,
    include_upper_wiggle: bool,
    timeout_ms: int,
    include_fragment_size: bool = True,
) -> dict[str, object]:
    interior_edges, tail = family_spec_from_state_counts(state_counts, orientation, include_upper_wiggle)
    rows = assignment_rows(
        state_counts,
        interior_edges,
        orientation,
        tail,
        timeout_ms,
        include_fragment_size=include_fragment_size,
    )

    summary = Counter((status, fragment_size) for _, _, status, fragment_size in rows)
    predicted_counter = Counter()
    actual_counter = Counter()
    mismatch_rows: list[tuple[tuple[int, ...], str, str, int | None]] = []

    for assignment, _, status, fragment_size in rows:
        bottom_slot = assignment[0]
        predicted = predicted_status(orientation, assignment)
        predicted_counter[(bottom_slot, predicted)] += 1
        actual_counter[(bottom_slot, status)] += 1
        if status != predicted:
            mismatch_rows.append((assignment, predicted, status, fragment_size))

    return {
        "state_counts": state_counts,
        "orientation": orientation,
        "include_upper_wiggle": include_upper_wiggle,
        "interior_edges": interior_edges,
        "tail": tail,
        "summary": dict(sorted(summary.items(), key=str)),
        "predicted_bottom_slot_counter": dict(sorted(predicted_counter.items())),
        "actual_bottom_slot_counter": dict(sorted(actual_counter.items())),
        "mismatches": mismatch_rows,
    }


def family_name(orientation: str, include_upper_wiggle: bool) -> str:
    return f"{orientation}_{'upper' if include_upper_wiggle else 'base'}"


def family_flags(family_set: str) -> tuple[bool, ...]:
    if family_set == "both":
        return (False, True)
    if family_set == "upper":
        return (True,)
    return (False,)


def symbolic_regime_label(
    gaps: tuple[int, int, int],
    orientation: str,
    include_upper_wiggle: bool,
) -> str:
    if gaps[0] == 1 and gaps[1] == 1:
        return "local_11k"

    if not include_upper_wiggle or orientation == "forward":
        return "asymmetric_1ab" if gaps[0] == 1 else "semi_symmetric_2plus"

    if gaps[0] == 1 and gaps[2] == 2:
        return "reverse_upper_trailing2"
    if gaps[0] == 1:
        return "asymmetric_1ab"
    return "semi_symmetric_2plus"


def slot_status_signature(result: dict[str, object]) -> tuple[tuple[int, tuple[tuple[str, int], ...]], ...]:
    by_slot: dict[int, Counter[str]] = {}
    actual_counter = result["actual_bottom_slot_counter"]
    assert isinstance(actual_counter, dict)
    for (slot, status), count in actual_counter.items():
        by_slot.setdefault(slot, Counter())[status] += count
    return tuple(
        (slot, tuple(sorted(counter.items())))
        for slot, counter in sorted(by_slot.items())
    )


def summary_signature(result: dict[str, object]) -> tuple[tuple[str, int | None, int], ...]:
    summary = result["summary"]
    assert isinstance(summary, dict)
    return tuple(
        (status, fragment_size, count)
        for (status, fragment_size), count in sorted(summary.items(), key=str)
    )


def exact_signature(
    result: dict[str, object],
) -> tuple[
    tuple[tuple[int, tuple[tuple[str, int], ...]], ...],
    tuple[tuple[str, int | None, int], ...],
]:
    return slot_status_signature(result), summary_signature(result)


def taxonomy_rows(
    gaps_list: tuple[tuple[int, int, int], ...],
    orientations: tuple[str, ...],
    include_upper_flags: tuple[bool, ...],
    timeout_ms: int,
    include_fragment_size: bool,
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for gaps in gaps_list:
        state_counts = state_counts_from_gaps(gaps)
        for include_upper_wiggle in include_upper_flags:
            for orientation in orientations:
                result = classify_family(
                    state_counts,
                    orientation,
                    include_upper_wiggle,
                    timeout_ms,
                    include_fragment_size=include_fragment_size,
                )
                rows.append(
                    {
                        "gaps": gaps,
                        "family": family_name(orientation, include_upper_wiggle),
                        "predicted_match": len(result["mismatches"]) == 0,
                        "slot_status_signature": slot_status_signature(result),
                        "summary_signature": summary_signature(result),
                        "exact_signature": exact_signature(result),
                        "result": result,
                    }
                )
    return rows


def cluster_taxonomy(
    rows: list[dict[str, object]],
) -> dict[str, list[dict[str, object]]]:
    grouped: dict[str, dict[object, list[dict[str, object]]]] = {}
    for row in rows:
        family = row["family"]
        signature = row["exact_signature"]
        assert isinstance(family, str)
        grouped.setdefault(family, {}).setdefault(signature, []).append(row)

    clusters: dict[str, list[dict[str, object]]] = {}
    for family, family_groups in grouped.items():
        ordered_clusters: list[dict[str, object]] = []
        for regime_index, signature in enumerate(
            sorted(
                family_groups,
                key=lambda key: [entry["gaps"] for entry in family_groups[key]],
            ),
            start=1,
        ):
            members = sorted(family_groups[signature], key=lambda row: row["gaps"])
            exemplar = members[0]
            ordered_clusters.append(
                {
                    "family": family,
                    "regime_id": f"{family}_r{regime_index}",
                    "gaps_list": [row["gaps"] for row in members],
                    "predicted_match": exemplar.get("predicted_match"),
                    "slot_status_signature": exemplar.get("slot_status_signature"),
                    "summary_signature": exemplar.get("summary_signature"),
                }
            )
        clusters[family] = ordered_clusters
    return clusters


def symbolic_rows(
    gaps_list: tuple[tuple[int, int, int], ...],
    orientations: tuple[str, ...],
    include_upper_flags: tuple[bool, ...],
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for gaps in gaps_list:
        for include_upper_wiggle in include_upper_flags:
            for orientation in orientations:
                rows.append(
                    {
                        "gaps": gaps,
                        "family": family_name(orientation, include_upper_wiggle),
                        "symbolic_label": symbolic_regime_label(gaps, orientation, include_upper_wiggle),
                    }
                )
    return rows


def cluster_symbolic(
    rows: list[dict[str, object]],
) -> dict[str, list[dict[str, object]]]:
    grouped: dict[str, dict[str, list[tuple[int, int, int]]]] = {}
    for row in rows:
        family = row["family"]
        label = row["symbolic_label"]
        gaps = row["gaps"]
        assert isinstance(family, str)
        assert isinstance(label, str)
        assert isinstance(gaps, tuple)
        grouped.setdefault(family, {}).setdefault(label, []).append(gaps)

    clusters: dict[str, list[dict[str, object]]] = {}
    for family, family_groups in grouped.items():
        clusters[family] = [
            {
                "family": family,
                "symbolic_label": label,
                "gaps_list": sorted(gaps_list),
            }
            for label, gaps_list in sorted(family_groups.items())
        ]
    return clusters


def compare_symbolic_to_exact(
    exact_rows: list[dict[str, object]],
    gaps_list: tuple[tuple[int, int, int], ...],
    orientations: tuple[str, ...],
    include_upper_flags: tuple[bool, ...],
) -> dict[str, dict[str, object]]:
    exact_clusters = cluster_taxonomy(exact_rows)
    symbolic_clusters = cluster_symbolic(symbolic_rows(gaps_list, orientations, include_upper_flags))
    comparison: dict[str, dict[str, object]] = {}

    for family in sorted(set(exact_clusters) | set(symbolic_clusters)):
        exact_gap_sets = sorted(sorted(cluster["gaps_list"]) for cluster in exact_clusters.get(family, []))
        symbolic_gap_sets = sorted(sorted(cluster["gaps_list"]) for cluster in symbolic_clusters.get(family, []))
        comparison[family] = {
            "match": exact_gap_sets == symbolic_gap_sets,
            "exact_gap_sets": exact_gap_sets,
            "symbolic_gap_sets": symbolic_gap_sets,
        }
    return comparison


def print_classification(gaps: tuple[int, int, int], result: dict[str, object]) -> None:
    print(
        f"gaps={gaps} state_counts={result['state_counts']} orientation={result['orientation']} "
        f"upper_wiggle={'yes' if result['include_upper_wiggle'] else 'no'}"
    )
    print(f"  interior_edges={result['interior_edges']} tail={result['tail']}")
    print(f"  summary={result['summary']}")
    print(f"  predicted_bottom_slot_counter={result['predicted_bottom_slot_counter']}")
    print(f"  actual_bottom_slot_counter={result['actual_bottom_slot_counter']}")
    print(f"  mismatches={len(result['mismatches'])}")
    for mismatch in result["mismatches"][:6]:
        assignment, predicted, actual, fragment_size = mismatch
        print(
            f"    assignment={assignment} predicted={predicted} actual={actual} "
            f"fragment_size={fragment_size}"
        )


def print_taxonomy(clusters: dict[str, list[dict[str, object]]]) -> None:
    for family in sorted(clusters):
        print(f"family={family}")
        for cluster in clusters[family]:
            print(
                f"  regime={cluster['regime_id']} gaps={cluster['gaps_list']} "
                f"predicted_match={cluster['predicted_match']}"
            )
            print(f"    slot_status_signature={cluster['slot_status_signature']}")
            print(f"    summary_signature={cluster['summary_signature']}")


def print_symbolic(clusters: dict[str, list[dict[str, object]]]) -> None:
    for family in sorted(clusters):
        print(f"family={family}")
        for cluster in clusters[family]:
            print(f"  symbolic_label={cluster['symbolic_label']} gaps={cluster['gaps_list']}")


def print_symbolic_comparison(comparison: dict[str, dict[str, object]]) -> None:
    for family in sorted(comparison):
        row = comparison[family]
        print(f"family={family} symbolic_match={row['match']}")
        print(f"  exact_gap_sets={row['exact_gap_sets']}")
        print(f"  symbolic_gap_sets={row['symbolic_gap_sets']}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=9)
    parser.add_argument("--gaps", help="semicolon-separated gap triples, e.g. 1,2,3;1,1,4")
    parser.add_argument("--orientation", choices=("reverse", "forward", "both"), default="both")
    parser.add_argument("--family-set", choices=("base", "upper", "both"), default="base")
    parser.add_argument(
        "--mode",
        choices=("detail", "taxonomy", "symbolic", "compare-symbolic"),
        default="detail",
    )
    parser.add_argument("--timeout-ms", type=int, default=1200)
    parser.add_argument("--omit-fragment-sizes", action="store_true")
    args = parser.parse_args()

    if args.gaps:
        gaps_list = tuple(parse_int_tuple(text) for text in args.gaps.split(";") if text.strip())
    else:
        gaps_list = TRUE_N9_GAPS if args.n == 9 else true_case3c_gap_patterns(args.n)
    orientations = ("reverse", "forward") if args.orientation == "both" else (args.orientation,)
    include_upper_flags = family_flags(args.family_set)

    if args.mode == "taxonomy":
        rows = taxonomy_rows(
            gaps_list,
            orientations,
            include_upper_flags,
            args.timeout_ms,
            include_fragment_size=not args.omit_fragment_sizes,
        )
        print_taxonomy(cluster_taxonomy(rows))
        return

    if args.mode == "symbolic":
        print_symbolic(cluster_symbolic(symbolic_rows(gaps_list, orientations, include_upper_flags)))
        return

    if args.mode == "compare-symbolic":
        rows = taxonomy_rows(
            gaps_list,
            orientations,
            include_upper_flags,
            args.timeout_ms,
            include_fragment_size=not args.omit_fragment_sizes,
        )
        print_symbolic_comparison(
            compare_symbolic_to_exact(rows, gaps_list, orientations, include_upper_flags)
        )
        return

    for gaps in gaps_list:
        state_counts = state_counts_from_gaps(gaps)
        for include_upper_wiggle in include_upper_flags:
            for orientation in orientations:
                result = classify_family(
                    state_counts,
                    orientation,
                    include_upper_wiggle,
                    args.timeout_ms,
                    include_fragment_size=not args.omit_fragment_sizes,
                )
                print_classification(gaps, result)


if __name__ == "__main__":
    main()
