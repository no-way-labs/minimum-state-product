#!/usr/bin/env python3
"""Extract completion-fragment anatomy for the representative true Case 3c residue.

This script is aimed at the all-killer project, not day-to-day residue checks.
It keeps exact seeded/completion solving in the loop, but records the minimized
fatal fragments in an anchored coordinate system so we can compare:

- fragment growth across n,
- common spines across completion-unsat assignments,
- which rules are genuinely new versus quaternary/tail shifts,
- whether the completion residue is localizing or diffusing.
"""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter
from dataclasses import dataclass
from itertools import product


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from scripts.glb_case3c_completion_fragment import (
    fatal_scc_summary_from_forced,
    minimize_fatal_fragment,
)
from scripts.glb_three_sweep_assignment_scan import build_word
from scripts.glb_case3c_starpower_probe import family_spec, representative_case3c_state_counts
from scripts.p2_completion_search import build_initial_domains_from_cycle
from scripts.p2_seeded_cycle_search import solve_good_cycle_from_movers
from scripts.p2_smt_completion import solve_cycle_with_smt


Config = tuple[int, ...]
RuleKey = tuple[int, tuple[int, int, int]]
ForcedMap = dict[RuleKey, int]
AnchoredRule = tuple[str, tuple[int, int, int], int]
StatePermutation = tuple[dict[int, int], ...]


@dataclass(frozen=True)
class AssignmentRecord:
    assignment: tuple[int, ...]
    word: tuple[int, ...]
    status: str
    cycle: tuple[Config, ...] | None
    forced_size: int | None
    forced_map: ForcedMap | None
    fragment_size: int | None
    fragment: ForcedMap | None
    scc_summary: dict[str, object] | None


def parse_int_tuple(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def anchored_processor_label(processor: int, n: int) -> str:
    if processor <= 5:
        return f"P{processor}"
    if processor == n - 1:
        return "Q"
    return f"Q-{(n - 1) - processor}"


def anchored_rule(
    processor: int,
    ctx: tuple[int, int, int],
    out_state: int,
    n: int,
) -> AnchoredRule:
    return anchored_processor_label(processor, n), ctx, out_state


def cycle_first_appearance_permutations(
    cycle: tuple[Config, ...],
    state_counts: tuple[int, ...],
) -> StatePermutation:
    permutations: list[dict[int, int]] = []
    for processor, state_count in enumerate(state_counts):
        order: list[int] = [0]
        seen = {0}
        for config in cycle:
            state = config[processor]
            if state not in seen:
                seen.add(state)
                order.append(state)
        for state in range(state_count):
            if state not in seen:
                order.append(state)
        permutations.append({state: idx for idx, state in enumerate(order)})
    return tuple(permutations)


def normalize_cycle(
    cycle: tuple[Config, ...],
    permutations: StatePermutation,
) -> tuple[Config, ...]:
    return tuple(
        tuple(permutations[processor][config[processor]] for processor in range(len(config)))
        for config in cycle
    )


def normalize_forced_map(
    forced_map: ForcedMap,
    permutations: StatePermutation,
    n: int,
) -> set[AnchoredRule]:
    normalized: set[AnchoredRule] = set()
    for (processor, ctx), out_state in forced_map.items():
        normalized_ctx = (
            permutations[(processor - 1) % n][ctx[0]],
            permutations[processor][ctx[1]],
            permutations[(processor + 1) % n][ctx[2]],
        )
        normalized.add(
            anchored_rule(
                processor,
                normalized_ctx,
                permutations[processor][out_state],
                n,
            )
        )
    return normalized


def assignment_records(
    state_counts: tuple[int, ...],
    interior_edges: tuple[int, ...],
    orientation: str,
    tail: tuple[int, ...],
    timeout_ms: int,
) -> list[AssignmentRecord]:
    n = len(state_counts)
    records: list[AssignmentRecord] = []
    for assignment in product(range(3), repeat=len(interior_edges)):
        word = build_word(interior_edges, assignment, orientation, tail, n)
        cycle = solve_good_cycle_from_movers(state_counts, word, timeout_ms=timeout_ms)
        if not cycle.found or cycle.cycle is None:
            records.append(
                AssignmentRecord(
                    assignment=assignment,
                    word=word,
                    status="seed_unsat" if "unknown" not in cycle.message else "seed_unknown",
                    cycle=None,
                    forced_size=None,
                    forced_map=None,
                    fragment_size=None,
                    fragment=None,
                    scc_summary=None,
                )
            )
            continue

        completion = solve_cycle_with_smt(state_counts, cycle.cycle, word, timeout_ms=max(10000, timeout_ms))
        if completion.found:
            records.append(
                AssignmentRecord(
                    assignment=assignment,
                    word=word,
                    status="completion_sat",
                    cycle=cycle.cycle,
                    forced_size=None,
                    forced_map=None,
                    fragment_size=None,
                    fragment=None,
                    scc_summary=None,
                )
            )
            continue
        if "unknown" in completion.message:
            records.append(
                AssignmentRecord(
                    assignment=assignment,
                    word=word,
                    status="completion_unknown",
                    cycle=cycle.cycle,
                    forced_size=None,
                    forced_map=None,
                    fragment_size=None,
                    fragment=None,
                    scc_summary=None,
                )
            )
            continue

        _, cycle_set, domains = build_initial_domains_from_cycle(state_counts, cycle.cycle, word)
        forced = {key: next(iter(domain)) for key, domain in domains.items() if len(domain) == 1}
        fragment = minimize_fatal_fragment(state_counts, cycle_set, forced)
        records.append(
            AssignmentRecord(
                assignment=assignment,
                word=word,
                status="completion_unsat",
                cycle=cycle.cycle,
                forced_size=len(forced),
                forced_map=forced,
                fragment_size=len(fragment),
                fragment=fragment,
                scc_summary=fatal_scc_summary_from_forced(state_counts, cycle_set, fragment),
            )
        )
    return records


def summarize_completion_fragments(
    records: list[AssignmentRecord],
    state_counts: tuple[int, ...],
) -> dict[str, object]:
    n = len(state_counts)
    completion_records = [record for record in records if record.status == "completion_unsat" and record.fragment is not None]
    if not completion_records:
        return {
            "completion_records": 0,
            "forced_size_histogram": {},
            "forced_common_spine_size": 0,
            "forced_common_spine_by_processor": {},
            "forced_rule_union": 0,
            "forced_common_spine_rules": [],
            "normalized_forced_common_spine_size": 0,
            "normalized_forced_common_spine_by_processor": {},
            "normalized_forced_rule_union": 0,
            "normalized_forced_support_histogram": {},
            "normalized_forced_common_spine_rules": [],
            "size_histogram": {},
            "common_spine_size": 0,
            "common_spine_by_processor": {},
            "support_histogram": {},
            "anchored_rule_union": 0,
            "scc_histogram": {},
            "common_spine_rules": [],
        }

    anchored_forced_maps = [
        {
            anchored_rule(processor, ctx, out_state, n)
            for (processor, ctx), out_state in record.forced_map.items()
        }
        for record in completion_records
        if record.forced_map is not None
    ]
    normalized_anchored_forced_maps = [
        normalize_forced_map(
            record.forced_map,
            cycle_first_appearance_permutations(record.cycle, state_counts),
            n,
        )
        for record in completion_records
        if record.forced_map is not None and record.cycle is not None
    ]
    anchored_fragments = [
        {
            anchored_rule(processor, ctx, out_state, n)
            for (processor, ctx), out_state in record.fragment.items()
        }
        for record in completion_records
    ]
    forced_common_spine = set.intersection(*anchored_forced_maps)
    forced_union = set.union(*anchored_forced_maps)
    normalized_forced_common_spine = set.intersection(*normalized_anchored_forced_maps)
    normalized_forced_union = set.union(*normalized_anchored_forced_maps)
    common_spine = set.intersection(*anchored_fragments)
    union = set.union(*anchored_fragments)

    forced_size_histogram = Counter(record.forced_size for record in completion_records)
    size_histogram = Counter(record.fragment_size for record in completion_records)
    support_histogram = Counter(rule[0] for fragment in anchored_fragments for rule in fragment)
    forced_support_histogram = Counter(rule[0] for fragment in anchored_forced_maps for rule in fragment)
    forced_common_spine_by_processor = Counter(rule[0] for rule in forced_common_spine)
    normalized_forced_support_histogram = Counter(
        rule[0] for fragment in normalized_anchored_forced_maps for rule in fragment
    )
    normalized_forced_common_spine_by_processor = Counter(rule[0] for rule in normalized_forced_common_spine)
    common_spine_by_processor = Counter(rule[0] for rule in common_spine)
    scc_histogram = Counter(
        (
            None if record.scc_summary is None else record.scc_summary["scc_size"],
            None if record.scc_summary is None else record.scc_summary["all_binary"],
        )
        for record in completion_records
    )

    return {
        "completion_records": len(completion_records),
        "forced_size_histogram": dict(sorted(forced_size_histogram.items())),
        "forced_common_spine_size": len(forced_common_spine),
        "forced_common_spine_by_processor": dict(sorted(forced_common_spine_by_processor.items())),
        "forced_rule_union": len(forced_union),
        "forced_support_histogram": dict(sorted(forced_support_histogram.items())),
        "forced_common_spine_rules": sorted(forced_common_spine),
        "normalized_forced_common_spine_size": len(normalized_forced_common_spine),
        "normalized_forced_common_spine_by_processor": dict(
            sorted(normalized_forced_common_spine_by_processor.items())
        ),
        "normalized_forced_rule_union": len(normalized_forced_union),
        "normalized_forced_support_histogram": dict(sorted(normalized_forced_support_histogram.items())),
        "normalized_forced_common_spine_rules": sorted(normalized_forced_common_spine),
        "size_histogram": dict(sorted(size_histogram.items())),
        "common_spine_size": len(common_spine),
        "common_spine_by_processor": dict(sorted(common_spine_by_processor.items())),
        "support_histogram": dict(sorted(support_histogram.items())),
        "anchored_rule_union": len(union),
        "scc_histogram": dict(sorted(scc_histogram.items(), key=str)),
        "common_spine_rules": sorted(common_spine),
    }


def print_family_summary(
    n: int,
    orientation: str,
    include_upper_wiggle: bool,
    timeout_ms: int,
) -> None:
    state_counts = representative_case3c_state_counts(n)
    interior_edges, tail = family_spec(n, orientation, include_upper_wiggle)
    records = assignment_records(state_counts, interior_edges, orientation, tail, timeout_ms)

    status_histogram = Counter((record.status, record.fragment_size) for record in records)
    fragment_summary = summarize_completion_fragments(records, state_counts)

    print(
        f"n={n} orientation={orientation} upper_wiggle={'yes' if include_upper_wiggle else 'no'}"
    )
    print(f"  state_counts={state_counts}")
    print(f"  interior_edges={interior_edges} tail={tail}")
    print(f"  status_histogram={dict(sorted(status_histogram.items(), key=str))}")
    print(f"  completion_records={fragment_summary['completion_records']}")
    print(f"  forced_size_histogram={fragment_summary['forced_size_histogram']}")
    print(f"  forced_rule_union={fragment_summary['forced_rule_union']}")
    print(f"  forced_common_spine_size={fragment_summary['forced_common_spine_size']}")
    print(f"  forced_common_spine_by_processor={fragment_summary['forced_common_spine_by_processor']}")
    print(f"  forced_support_histogram={fragment_summary['forced_support_histogram']}")
    print(f"  normalized_forced_rule_union={fragment_summary['normalized_forced_rule_union']}")
    print(f"  normalized_forced_common_spine_size={fragment_summary['normalized_forced_common_spine_size']}")
    print(
        "  normalized_forced_common_spine_by_processor="
        f"{fragment_summary['normalized_forced_common_spine_by_processor']}"
    )
    print(
        "  normalized_forced_support_histogram="
        f"{fragment_summary['normalized_forced_support_histogram']}"
    )
    print(f"  size_histogram={fragment_summary['size_histogram']}")
    print(f"  anchored_rule_union={fragment_summary['anchored_rule_union']}")
    print(f"  common_spine_size={fragment_summary['common_spine_size']}")
    print(f"  common_spine_by_processor={fragment_summary['common_spine_by_processor']}")
    print(f"  support_histogram={fragment_summary['support_histogram']}")
    print(f"  scc_histogram={fragment_summary['scc_histogram']}")
    for assignment_record in records:
        if assignment_record.status != "completion_unsat" or assignment_record.scc_summary is None:
            continue
        print(
            f"  completion_assignment={assignment_record.assignment} "
            f"forced_size={assignment_record.forced_size} "
            f"fragment_size={assignment_record.fragment_size} "
            f"scc_size={assignment_record.scc_summary['scc_size']} "
            f"all_binary={assignment_record.scc_summary['all_binary']}"
        )
    print("  forced_common_spine_rules:")
    for rule in fragment_summary["forced_common_spine_rules"]:
        print(f"    {rule}")
    print("  normalized_forced_common_spine_rules:")
    for rule in fragment_summary["normalized_forced_common_spine_rules"]:
        print(f"    {rule}")
    print("  common_spine_rules:")
    for rule in fragment_summary["common_spine_rules"]:
        print(f"    {rule}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-values", default="9,10")
    parser.add_argument("--orientation", choices=("reverse", "forward", "both"), default="both")
    parser.add_argument("--include-upper-wiggle", action="store_true")
    parser.add_argument("--timeout-ms", type=int, default=1500)
    args = parser.parse_args()

    n_values = parse_int_tuple(args.n_values)
    orientations = ("reverse", "forward") if args.orientation == "both" else (args.orientation,)

    for n in n_values:
        for orientation in orientations:
            print_family_summary(n, orientation, args.include_upper_wiggle, args.timeout_ms)


if __name__ == "__main__":
    main()
