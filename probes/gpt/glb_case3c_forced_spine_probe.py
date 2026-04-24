#!/usr/bin/env python3
"""Collect normalized forced singleton spines on the predicted completion branch.

This avoids exact completion solving when the current goal is to scout the
canonical spine at higher n rather than certify completion-unsat again.
"""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter
from itertools import product

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(__file__))))
if REPO_ROOT not in sys.path:
    sys.path.insert(0, REPO_ROOT)

from probes.gpt.glb_case3c_fragment_anatomy import (
    anchored_rule,
    cycle_first_appearance_permutations,
    normalize_forced_map,
)
from probes.gpt.glb_case3c_gap_pattern_probe import (
    family_spec_from_state_counts,
    state_counts_from_gaps,
)
from probes.gpt.glb_case3c_starpower_probe import (
    predicted_status,
    representative_case3c_state_counts,
)
from probes.gpt.glb_three_sweep_assignment_scan import assignment_rows
from probes.gpt.glb_three_sweep_assignment_scan import build_word
from probes.gpt.p2_completion_search import build_initial_domains_from_cycle
from probes.gpt.p2_seeded_cycle_search import (
    solve_good_cycle_from_movers,
    solve_good_cycle_from_movers_lexmin,
)


def parse_int_tuple(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def completion_branch_assignments(
    interior_edges: tuple[int, ...],
    orientation: str,
) -> list[tuple[int, ...]]:
    assignments = []
    for assignment in product(range(3), repeat=len(interior_edges)):
        if predicted_status(orientation, assignment) == "completion_unsat":
            assignments.append(assignment)
    return assignments


def actual_completion_assignments(
    state_counts: tuple[int, ...],
    interior_edges: tuple[int, ...],
    orientation: str,
    tail: tuple[int, ...],
    timeout_ms: int,
) -> list[tuple[int, ...]]:
    rows = assignment_rows(
        state_counts,
        interior_edges,
        orientation,
        tail,
        timeout_ms,
        include_fragment_size=False,
    )
    return [assignment for assignment, _, status, _ in rows if status == "completion_unsat"]


def print_probe(
    n: int,
    orientation: str,
    include_upper_wiggle: bool,
    timeout_ms: int,
    cycle_selector: str,
    assignment_mode: str,
) -> None:
    summary = probe_summary(
        n,
        orientation,
        include_upper_wiggle,
        timeout_ms,
        cycle_selector,
        assignment_mode,
    )
    print(
        f"n={summary['n']} orientation={summary['orientation']} "
        f"upper_wiggle={'yes' if summary['include_upper_wiggle'] else 'no'} "
        f"selector={summary['cycle_selector']} assignment_mode={summary['assignment_mode']}"
    )
    print(f"  selected_assignments={summary['selected_assignment_count']}")
    print(f"  solved_cycles={summary['solved_cycles']} missing_cycles={summary['missing_cycles']}")
    print(f"  forced_size_histogram={summary['forced_size_histogram']}")
    print(f"  forced_common_spine_size={summary['forced_common_spine_size']}")
    print(f"  forced_union_size={summary['forced_union_size']}")
    print(f"  normalized_forced_common_spine_size={summary['normalized_forced_common_spine_size']}")
    print(f"  normalized_forced_union_size={summary['normalized_forced_union_size']}")
    print(f"  normalized_common_by_processor={summary['normalized_common_by_processor']}")
    if summary["missing_cycle_assignments"]:
        print(f"  missing_cycle_assignments={summary['missing_cycle_assignments']}")
    print(f"  normalized_common_spine_rules={summary['normalized_common_spine_rules']}")


def probe_summary(
    n: int,
    orientation: str,
    include_upper_wiggle: bool,
    timeout_ms: int,
    cycle_selector: str = "lexmin",
    assignment_mode: str = "predicted_completion",
) -> dict[str, object]:
    state_counts = representative_case3c_state_counts(n)
    return probe_summary_for_state_counts(
        state_counts,
        orientation,
        include_upper_wiggle,
        timeout_ms,
        cycle_selector,
        assignment_mode=assignment_mode,
    )


def probe_summary_for_gaps(
    gaps: tuple[int, int, int],
    orientation: str,
    include_upper_wiggle: bool,
    timeout_ms: int,
    cycle_selector: str = "lexmin",
    assignment_mode: str = "predicted_completion",
) -> dict[str, object]:
    return probe_summary_for_state_counts(
        state_counts_from_gaps(gaps),
        orientation,
        include_upper_wiggle,
        timeout_ms,
        cycle_selector,
        assignment_mode=assignment_mode,
        gaps=gaps,
    )


def probe_summary_for_state_counts(
    state_counts: tuple[int, ...],
    orientation: str,
    include_upper_wiggle: bool,
    timeout_ms: int,
    cycle_selector: str = "lexmin",
    assignment_mode: str = "predicted_completion",
    gaps: tuple[int, int, int] | None = None,
) -> dict[str, object]:
    interior_edges, tail = family_spec_from_state_counts(
        state_counts,
        orientation,
        include_upper_wiggle,
    )
    n = len(state_counts)
    if assignment_mode == "predicted_completion":
        assignments = completion_branch_assignments(interior_edges, orientation)
    elif assignment_mode == "actual_completion":
        assignments = actual_completion_assignments(
            state_counts,
            interior_edges,
            orientation,
            tail,
            timeout_ms,
        )
    else:
        raise ValueError(f"unsupported assignment mode: {assignment_mode}")
    cycle_solver = solve_good_cycle_from_movers_lexmin if cycle_selector == "lexmin" else solve_good_cycle_from_movers

    forced_sets: list[set[tuple[str, tuple[int, int, int], int]]] = []
    normalized_forced_sets: list[set[tuple[str, tuple[int, int, int], int]]] = []
    forced_size_hist = Counter()
    missing_cycles: list[tuple[int, ...]] = []

    for assignment in assignments:
        word = build_word(interior_edges, assignment, orientation, tail, n)
        cycle = cycle_solver(state_counts, word, timeout_ms=timeout_ms)
        if not cycle.found or cycle.cycle is None:
            missing_cycles.append(assignment)
            continue
        _, _, domains = build_initial_domains_from_cycle(state_counts, cycle.cycle, word)
        forced = {
            anchored_rule(processor, ctx, next(iter(domain)), n)
            for (processor, ctx), domain in domains.items()
            if len(domain) == 1
        }
        forced_map = {
            key: next(iter(domain))
            for key, domain in domains.items()
            if len(domain) == 1
        }
        normalized_forced = normalize_forced_map(
            forced_map,
            cycle_first_appearance_permutations(cycle.cycle, state_counts),
            n,
        )
        forced_sets.append(forced)
        normalized_forced_sets.append(normalized_forced)
        forced_size_hist[len(forced)] += 1

    if forced_sets:
        common_spine = set.intersection(*forced_sets)
        union = set.union(*forced_sets)
    else:
        common_spine = set()
        union = set()
    if normalized_forced_sets:
        normalized_common_spine = set.intersection(*normalized_forced_sets)
        normalized_union = set.union(*normalized_forced_sets)
    else:
        normalized_common_spine = set()
        normalized_union = set()

    return {
        "n": len(state_counts),
        "gaps": gaps,
        "state_counts": state_counts,
        "orientation": orientation,
        "include_upper_wiggle": include_upper_wiggle,
        "interior_edges": interior_edges,
        "tail": tail,
        "cycle_selector": cycle_selector,
        "assignment_mode": assignment_mode,
        "predicted_completion_assignments": len(assignments),
        "selected_assignment_count": len(assignments),
        "selected_assignments": assignments,
        "solved_cycles": len(forced_sets),
        "missing_cycles": len(missing_cycles),
        "missing_cycle_assignments": missing_cycles,
        "forced_size_histogram": dict(sorted(forced_size_hist.items())),
        "forced_common_spine_size": len(common_spine),
        "forced_union_size": len(union),
        "normalized_forced_common_spine_size": len(normalized_common_spine),
        "normalized_forced_union_size": len(normalized_union),
        "normalized_common_by_processor": dict(
            sorted(Counter(label for label, _, _ in normalized_common_spine).items())
        ),
        "normalized_common_spine_rules": sorted(normalized_common_spine),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-values", default="9,10,11")
    parser.add_argument("--orientation", choices=("reverse", "forward", "both"), default="both")
    parser.add_argument("--include-upper-wiggle", action="store_true")
    parser.add_argument("--timeout-ms", type=int, default=1200)
    parser.add_argument("--cycle-selector", choices=("any", "lexmin"), default="lexmin")
    parser.add_argument(
        "--assignment-mode",
        choices=("predicted_completion", "actual_completion"),
        default="predicted_completion",
    )
    args = parser.parse_args()

    n_values = parse_int_tuple(args.n_values)
    orientations = ("reverse", "forward") if args.orientation == "both" else (args.orientation,)
    for n in n_values:
        for orientation in orientations:
            print_probe(
                n,
                orientation,
                args.include_upper_wiggle,
                args.timeout_ms,
                args.cycle_selector,
                args.assignment_mode,
            )


if __name__ == "__main__":
    main()
