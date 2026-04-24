#!/usr/bin/env python3
"""Scan compressed three-sweep block languages for Case 3c support experiments."""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter
from itertools import product


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from scripts.glb_completion_diagnose import forced_scc_summary
from scripts.p2_seeded_cycle_search import solve_good_cycle_from_movers
from scripts.p2_smt_completion import solve_cycle_with_smt


def parse_int_tuple(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def build_forward_block(wiggles: set[int], n: int = 9) -> tuple[int, ...]:
    out = [0]
    for edge in range(n - 1):
        out.append(edge + 1)
        if edge in wiggles:
            out.extend([edge, edge + 1])
    out.append(0)
    return tuple(out)


def build_reverse_block(wiggles: set[int], n: int = 9) -> tuple[int, ...]:
    out = [0]
    current = n - 1
    out.append(current)
    for _ in range(n - 1):
        nxt = (current - 1) % n
        if nxt == 0:
            break
        out.append(nxt)
        edge = nxt
        if edge in wiggles:
            out.extend([current, nxt])
        current = nxt
    out.append(0)
    return tuple(out)


def generate_words(
    interior_edges: tuple[int, ...],
    orientation: str,
    boundary_mode: str,
    n: int = 9,
) -> list[tuple[int, ...]]:
    def block_builder(wiggles: set[int]) -> tuple[int, ...]:
        if orientation == "forward":
            return build_forward_block(wiggles, n)
        return build_reverse_block(wiggles, n)

    short_block = {
        "short080": (0, n - 1, 0),
        "short010": (0, 1, 0),
    }.get(boundary_mode)
    tail = {
        "tail08": (0, n - 1),
        "tail01": (0, 1),
        "tail121": (0, 1, 2, 1),
    }.get(boundary_mode)

    words: set[tuple[int, ...]] = set()

    def stitch(pieces: list[tuple[int, ...]]) -> tuple[int, ...]:
        out: list[int] = []
        for piece in pieces:
            out.extend(piece if not out else piece[1:])
        return tuple(out)

    base_assignments = list(product(range(3), repeat=len(interior_edges)))

    def base_blocks_from_assignment(assignment: tuple[int, ...]) -> list[tuple[int, ...]]:
        block_wiggles = [set() for _ in range(3)]
        for edge, slot in zip(interior_edges, assignment, strict=True):
            block_wiggles[slot].add(edge)
        return [block_builder(block_wiggles[index]) for index in range(3)]

    if boundary_mode == "tail08_or_short080":
        for assignment in base_assignments:
            base_blocks = base_blocks_from_assignment(assignment)
            words.add(stitch(base_blocks + [(0, n - 1)]))
            for slot in range(4):
                pieces: list[tuple[int, ...]] = []
                for pos in range(4):
                    if pos == slot:
                        pieces.append((0, n - 1, 0))
                    if pos < 3:
                        pieces.append(base_blocks[pos])
                words.add(stitch(pieces))
        return sorted(words)

    if boundary_mode == "tail01_or_short010":
        for assignment in base_assignments:
            base_blocks = base_blocks_from_assignment(assignment)
            words.add(stitch(base_blocks + [(0, 1)]))
            for slot in range(4):
                pieces: list[tuple[int, ...]] = []
                for pos in range(4):
                    if pos == slot:
                        pieces.append((0, 1, 0))
                    if pos < 3:
                        pieces.append(base_blocks[pos])
                words.add(stitch(pieces))
        return sorted(words)

    for assignment in base_assignments:
        base_blocks = base_blocks_from_assignment(assignment)
        if boundary_mode == "none":
            words.add(stitch(base_blocks))
        elif tail is not None:
            words.add(stitch(base_blocks + [tail]))
        else:
            assert short_block is not None
            for slot in range(4):
                pieces: list[tuple[int, ...]] = []
                for pos in range(4):
                    if pos == slot:
                        pieces.append(short_block)
                    if pos < 3:
                        pieces.append(base_blocks[pos])
                words.add(stitch(pieces))

    return sorted(words)


def scan_seed(
    state_counts: tuple[int, ...],
    words: list[tuple[int, ...]],
    timeout_ms: int,
) -> None:
    counter: Counter[str] = Counter()
    examples: dict[str, tuple[int, ...]] = {}

    for word in words:
        result = solve_good_cycle_from_movers(state_counts, word, timeout_ms=timeout_ms)
        key = "seed_sat" if result.found else ("seed_unknown" if "unknown" in result.message else "seed_unsat")
        counter[key] += 1
        examples.setdefault(key, word)

    print(f"word_count={len(words)}")
    print(f"counter={dict(sorted(counter.items()))}")
    for key in sorted(examples):
        print(f"example_{key}={examples[key]}")


def scan_completion(
    state_counts: tuple[int, ...],
    words: list[tuple[int, ...]],
    cycle_timeout_ms: int,
    completion_timeout_ms: int,
) -> None:
    counter: Counter[str] = Counter()
    scc_counter: Counter[tuple[int | None, bool | None]] = Counter()

    for word in words:
        cycle = solve_good_cycle_from_movers(state_counts, word, timeout_ms=cycle_timeout_ms)
        if not cycle.found:
            key = "seed_unknown" if "unknown" in cycle.message else "seed_unsat"
            counter[key] += 1
            continue

        completion = solve_cycle_with_smt(state_counts, cycle.cycle, word, timeout_ms=completion_timeout_ms)
        if completion.found:
            counter["completion_sat"] += 1
            continue
        if "unknown" in completion.message:
            counter["completion_unknown"] += 1
            continue

        counter["completion_unsat"] += 1
        summary = forced_scc_summary(state_counts, cycle.cycle, word)
        if summary is not None:
            scc_counter[(summary["scc_size"], summary["all_binary"])] += 1

    print(f"word_count={len(words)}")
    print(f"counter={dict(sorted(counter.items()))}")
    print(f"scc_counter={dict(sorted(scc_counter.items()))}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--state-counts", required=True)
    parser.add_argument("--orientation", choices=("forward", "reverse"), required=True)
    parser.add_argument("--interior-edges", required=True)
    parser.add_argument(
        "--boundary-mode",
        choices=(
            "none",
            "tail08",
            "tail01",
            "tail121",
            "short080",
            "short010",
            "tail08_or_short080",
            "tail01_or_short010",
        ),
        default="none",
    )
    parser.add_argument("--mode", choices=("seed", "completion"), default="seed")
    parser.add_argument("--timeout-ms", type=int, default=500)
    parser.add_argument("--cycle-timeout-ms", type=int, default=2500)
    parser.add_argument("--completion-timeout-ms", type=int, default=2500)
    args = parser.parse_args()

    state_counts = parse_int_tuple(args.state_counts)
    interior_edges = parse_int_tuple(args.interior_edges)
    words = generate_words(interior_edges, args.orientation, args.boundary_mode, len(state_counts))

    if args.mode == "seed":
        scan_seed(state_counts, words, args.timeout_ms)
    else:
        scan_completion(
            state_counts,
            words,
            args.cycle_timeout_ms,
            args.completion_timeout_ms,
        )


if __name__ == "__main__":
    main()
