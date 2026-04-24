#!/usr/bin/env python3
"""Classify three-sweep wiggle-slot assignments by seeded/completion outcome."""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter
from itertools import product


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from scripts.glb_case3c_completion_fragment import minimize_fatal_fragment
from scripts.glb_three_sweep_scan import build_forward_block, build_reverse_block
from scripts.glb_block_signature import word_signature
from scripts.p2_completion_search import build_initial_domains_from_cycle
from scripts.p2_seeded_cycle_search import solve_good_cycle_from_movers
from scripts.p2_smt_completion import solve_cycle_with_smt


def parse_int_tuple(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def stitch(pieces: list[tuple[int, ...]]) -> tuple[int, ...]:
    out: list[int] = []
    for piece in pieces:
        out.extend(piece if not out else piece[1:])
    return tuple(out)


def build_word(
    interior_edges: tuple[int, ...],
    assignment: tuple[int, ...],
    orientation: str,
    tail: tuple[int, ...],
    n: int,
) -> tuple[int, ...]:
    builder = build_forward_block if orientation == "forward" else build_reverse_block
    block_wiggles = [set() for _ in range(3)]
    for edge, slot in zip(interior_edges, assignment, strict=True):
        block_wiggles[slot].add(edge)
    blocks = [builder(block_wiggles[i], n) for i in range(3)]
    return stitch(blocks + [tail])


def assignment_rows(
    state_counts: tuple[int, ...],
    interior_edges: tuple[int, ...],
    orientation: str,
    tail: tuple[int, ...],
    timeout_ms: int,
    include_fragment_size: bool = True,
) -> list[tuple[tuple[int, ...], tuple[int, ...], str, int | None]]:
    n = len(state_counts)
    rows: list[tuple[tuple[int, ...], tuple[int, ...], str, int | None]] = []
    for assignment in product(range(3), repeat=len(interior_edges)):
        word = build_word(interior_edges, assignment, orientation, tail, n)
        cycle = solve_good_cycle_from_movers(state_counts, word, timeout_ms=timeout_ms)
        if not cycle.found:
            rows.append((assignment, word, "seed_unsat", None))
            continue

        completion = solve_cycle_with_smt(state_counts, cycle.cycle, word, timeout_ms=max(10000, timeout_ms))
        if completion.found:
            rows.append((assignment, word, "completion_sat", None))
            continue
        if "unknown" in completion.message:
            rows.append((assignment, word, "completion_unknown", None))
            continue

        if not include_fragment_size:
            rows.append((assignment, word, "completion_unsat", None))
            continue

        _, cycle_set, domains = build_initial_domains_from_cycle(state_counts, cycle.cycle, word)
        forced = {key: next(iter(domain)) for key, domain in domains.items() if len(domain) == 1}
        fragment = minimize_fatal_fragment(state_counts, cycle_set, forced)
        rows.append((assignment, word, "completion_unsat", len(fragment)))
    return rows


def classify_assignments(
    state_counts: tuple[int, ...],
    interior_edges: tuple[int, ...],
    orientation: str,
    tail: tuple[int, ...],
    timeout_ms: int,
    include_fragment_size: bool,
) -> None:
    rows = assignment_rows(
        state_counts,
        interior_edges,
        orientation,
        tail,
        timeout_ms,
        include_fragment_size=include_fragment_size,
    )
    counter = Counter((status, fragment_size) for _, _, status, fragment_size in rows)
    print(f"state_counts={state_counts}")
    print(f"interior_edges={interior_edges}")
    print(f"orientation={orientation}")
    print(f"tail={tail}")
    print(f"summary={dict(sorted(counter.items(), key=str))}")
    for assignment, word, status, fragment_size in rows:
        print(
            f"assignment={assignment} status={status} fragment_size={fragment_size} "
            f"signature={word_signature(word, len(state_counts))}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--state-counts", default="2,3,2,3,3,2,3,3,4")
    parser.add_argument("--interior-edges", required=True)
    parser.add_argument("--orientation", choices=("forward", "reverse"), required=True)
    parser.add_argument("--tail", required=True, help="comma-separated tail, e.g. 0,8")
    parser.add_argument("--timeout-ms", type=int, default=1500)
    parser.add_argument("--omit-fragment-sizes", action="store_true")
    args = parser.parse_args()

    classify_assignments(
        parse_int_tuple(args.state_counts),
        parse_int_tuple(args.interior_edges),
        args.orientation,
        parse_int_tuple(args.tail),
        args.timeout_ms,
        not args.omit_fragment_sizes,
    )


if __name__ == "__main__":
    main()
