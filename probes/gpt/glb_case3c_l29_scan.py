#!/usr/bin/env python3
"""Scan a fixed Case 3c length-29 edge-vector branch."""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from scripts.glb_adjacent_walk_scan import binary_parity_compatible, cycle_count_compatible
from scripts.glb_raw_cycle_core import build_raw_cycle_solver
from scripts.glb_ring_family_scan import cyclic_edge_counts
from scripts.glb_seeded_unsat_core import unsat_core_labels
from scripts.p2_seeded_cycle_search import solve_good_cycle_from_movers


def parse_int_tuple(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def edge_between(left: int, right: int, n: int) -> int:
    if (right - left) % n == 1:
        return left
    if (left - right) % n == 1:
        return right
    raise ValueError(f"non-adjacent step {left}->{right}")


def enumerate_words_with_edge_counts(n: int, edge_counts: tuple[int, ...]) -> list[tuple[int, ...]]:
    mover_length = sum(edge_counts)
    remaining = list(edge_counts)
    words: list[tuple[int, ...]] = []
    prefix = [0]

    def rec() -> None:
        if len(prefix) == mover_length:
            last = prefix[-1]
            final_edge = edge_between(last, 0, n)
            if remaining[final_edge] != 1:
                return
            remaining[final_edge] -= 1
            if all(count == 0 for count in remaining):
                words.append(tuple(prefix))
            remaining[final_edge] += 1
            return

        position = prefix[-1]
        for nxt in ((position - 1) % n, (position + 1) % n):
            edge = edge_between(position, nxt, n)
            if remaining[edge] == 0:
                continue
            remaining[edge] -= 1
            prefix.append(nxt)
            rec()
            prefix.pop()
            remaining[edge] += 1

    rec()
    return words


def raw_sat(word: tuple[int, ...], state_counts: tuple[int, ...]) -> bool:
    solver, _, _ = build_raw_cycle_solver(state_counts, word, track_labels=False)
    return str(solver.check()) == "sat"


def first_context_and_move(labels: list[str]) -> tuple[str | None, str | None]:
    ctx = next((label for label in labels if label.startswith("ctx_")), None)
    move = next((label for label in labels if label.startswith("move_")), None)
    return ctx, move


def scan_branch(
    state_counts: tuple[int, ...],
    edge_counts: tuple[int, ...],
    timeout_ms: int,
    limit: int | None,
    require_cycle_filters: bool,
    skip_cores: bool,
    progress_every: int,
) -> None:
    n = len(state_counts)
    words = enumerate_words_with_edge_counts(n, edge_counts)
    print(f"state_counts={state_counts}")
    print(f"edge_counts={edge_counts}")
    print(f"enumerated_words={len(words)}")

    totals: Counter[str] = Counter()
    local_core_counter: Counter[tuple[str | None, str | None]] = Counter()
    raw_examples: dict[str, tuple[int, ...]] = {}
    local_examples: dict[tuple[str | None, str | None], tuple[int, ...]] = {}

    processed = 0
    for word in words:
        if require_cycle_filters:
            if not binary_parity_compatible(state_counts, word):
                totals["parity_blocked"] += 1
                continue
            if not cycle_count_compatible(word, n):
                totals["single_blocked"] += 1
                continue

        processed += 1
        if limit is not None and processed > limit:
            break

        assert cyclic_edge_counts(word, n) == edge_counts

        if not raw_sat(word, state_counts):
            totals["raw_unsat"] += 1
            raw_examples.setdefault("raw_unsat", word)
            continue

        totals["raw_sat"] += 1
        raw_examples.setdefault("raw_sat", word)
        result = solve_good_cycle_from_movers(state_counts, word, timeout_ms=timeout_ms)
        if result.found:
            totals["local_sat"] += 1
            raw_examples.setdefault("local_sat", word)
            print(f"LOCAL_SAT word={word}")
            continue
        if "unknown" in result.message:
            totals["local_unknown"] += 1
            raw_examples.setdefault("local_unknown", word)
            continue

        totals["local_unsat"] += 1
        if not skip_cores:
            status, labels = unsat_core_labels(state_counts, word)
            assert status == "unsat"
            key = first_context_and_move(labels)
            local_core_counter[key] += 1
            local_examples.setdefault(key, word)

        if progress_every and processed % progress_every == 0:
            print(f"progress={processed} totals={dict(totals)}")

    print(f"totals={dict(totals)}")
    print("examples:")
    for key in sorted(raw_examples):
        print(f"  {key}: {raw_examples[key]}")
    print("local_core_counter:")
    for key, count in local_core_counter.most_common():
        print(f"  {key}: {count} example={local_examples[key]}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--state-counts", default="2,3,2,3,3,2,3,3,4")
    parser.add_argument("--edge-counts", default="1,3,5,3,3,5,3,3,3")
    parser.add_argument("--timeout-ms", type=int, default=1000)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--skip-cycle-filters", action="store_true")
    parser.add_argument("--skip-cores", action="store_true")
    parser.add_argument("--progress-every", type=int, default=200)
    args = parser.parse_args()

    scan_branch(
        parse_int_tuple(args.state_counts),
        parse_int_tuple(args.edge_counts),
        args.timeout_ms,
        args.limit,
        not args.skip_cycle_filters,
        args.skip_cores,
        args.progress_every,
    )


if __name__ == "__main__":
    main()
