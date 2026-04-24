#!/usr/bin/env python3
"""Enumerate feasible Case 3c edge vectors and scan singleton/zero branches."""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from scripts.glb_case3c_l29_scan import enumerate_words_with_edge_counts
from scripts.glb_return_staircase import (
    find_anchored_return_contexts,
    find_binary_bounce_contexts,
    find_return_cones,
)


ODD_VALUES = tuple(range(1, 100, 2))


def parse_int_tuple(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def feasible_edge_vectors(state_counts: tuple[int, ...], mover_length: int) -> list[tuple[int, ...]]:
    n = len(state_counts)
    vectors: list[tuple[int, ...]] = []

    def vertex_ok(edge_counts: tuple[int, ...], vertex: int) -> bool:
        total = edge_counts[vertex - 1] + edge_counts[vertex]
        if total < 4:
            return False
        if state_counts[vertex] == 2 and ((total // 2) % 2 != 0):
            return False
        return True

    def rec(index: int, prefix: list[int], remaining: int) -> None:
        if index == n:
            if remaining != 0:
                return
            edge_counts = tuple(prefix)
            if all(vertex_ok(edge_counts, vertex) for vertex in range(n)):
                vectors.append(edge_counts)
            return

        for value in ODD_VALUES:
            if value > remaining:
                break
            prefix.append(value)
            if index > 0:
                partial = tuple(prefix + [1] * (n - len(prefix)))
                if vertex_ok(partial, index):
                    rec(index + 1, prefix, remaining - value)
            else:
                rec(index + 1, prefix, remaining - value)
            prefix.pop()

    rec(0, [], mover_length)
    return sorted(vectors)


def mode_summary(state_counts: tuple[int, ...], mover_length: int) -> None:
    vectors = feasible_edge_vectors(state_counts, mover_length)
    singleton_counter = Counter(sum(1 for value in edge_counts if value == 1) for edge_counts in vectors)
    print(f"state_counts={state_counts}")
    print(f"mover_length={mover_length}")
    print(f"vector_count={len(vectors)}")
    print(f"singleton_histogram={dict(sorted(singleton_counter.items()))}")
    for edge_counts in vectors:
        print(edge_counts)


def mode_zero_vectors(state_counts: tuple[int, ...], mover_length: int) -> None:
    vectors = feasible_edge_vectors(state_counts, mover_length)
    zero_vectors = [edge_counts for edge_counts in vectors if all(value >= 3 for value in edge_counts)]
    print(f"state_counts={state_counts}")
    print(f"mover_length={mover_length}")
    print(f"zero_vectors={len(zero_vectors)}")
    for edge_counts in zero_vectors:
        print(edge_counts)


def mode_scan_singletons(
    state_counts: tuple[int, ...],
    mover_length: int,
    start_index: int,
    stop_index: int | None,
) -> None:
    vectors = feasible_edge_vectors(state_counts, mover_length)
    singleton_vectors = [edge_counts for edge_counts in vectors if sum(1 for value in edge_counts if value == 1) == 1]
    selected = singleton_vectors[start_index:stop_index]
    print(f"state_counts={state_counts}")
    print(f"mover_length={mover_length}")
    print(f"singleton_vectors={len(singleton_vectors)}")
    print(f"selected_range=({start_index},{stop_index}) selected_count={len(selected)}")
    for offset, edge_counts in enumerate(selected, start=1):
        index = start_index + offset
        words = enumerate_words_with_edge_counts(len(state_counts), edge_counts)
        bad_word = next((word for word in words if not find_binary_bounce_contexts(word, state_counts)), None)
        print(
            f"vector {index}/{len(singleton_vectors)} edge_counts={edge_counts} "
            f"words={len(words)} all_binary_bounce={bad_word is None}"
        )
        if bad_word is not None:
            print(f"bad_word={bad_word}")
            break


def mode_scan_zero_vectors(
    state_counts: tuple[int, ...],
    mover_length: int,
    start_index: int,
    stop_index: int | None,
    progress_every: int,
) -> None:
    vectors = feasible_edge_vectors(state_counts, mover_length)
    zero_vectors = [edge_counts for edge_counts in vectors if all(value >= 3 for value in edge_counts)]
    selected = zero_vectors[start_index:stop_index]
    print(f"state_counts={state_counts}")
    print(f"mover_length={mover_length}")
    print(f"zero_vectors={len(zero_vectors)}")
    print(f"selected_range=({start_index},{stop_index}) selected_count={len(selected)}")
    for offset, edge_counts in enumerate(selected, start=1):
        index = start_index + offset
        words = enumerate_words_with_edge_counts(len(state_counts), edge_counts)
        exception_count = 0
        first_exception: tuple[int, ...] | None = None
        for word_index, word in enumerate(words, start=1):
            if find_return_cones(word, len(state_counts)):
                continue
            if find_binary_bounce_contexts(word, state_counts):
                continue
            if find_anchored_return_contexts(word, state_counts):
                continue
            exception_count += 1
            if first_exception is None:
                first_exception = word
            if progress_every and word_index % progress_every == 0:
                print(
                    f"vector_progress index={index}/{len(zero_vectors)} word_index={word_index}/{len(words)} "
                    f"exceptions={exception_count}"
                )
        print(
            f"vector {index}/{len(zero_vectors)} edge_counts={edge_counts} "
            f"words={len(words)} exceptions={exception_count}"
        )
        if first_exception is not None:
            print(f"first_exception={first_exception}")


def mode_dump_zero_exceptions(
    state_counts: tuple[int, ...],
    mover_length: int,
    edge_counts: tuple[int, ...],
) -> None:
    words = enumerate_words_with_edge_counts(len(state_counts), edge_counts)
    print(f"state_counts={state_counts}")
    print(f"mover_length={mover_length}")
    print(f"edge_counts={edge_counts}")
    print(f"words={len(words)}")
    exceptions = []
    for word in words:
        if find_return_cones(word, len(state_counts)):
            continue
        if find_binary_bounce_contexts(word, state_counts):
            continue
        if find_anchored_return_contexts(word, state_counts):
            continue
        exceptions.append(word)
    print(f"exceptions={len(exceptions)}")
    for index, word in enumerate(exceptions, start=1):
        print(f"exception {index}: {word}")


def mode_scan_branch(
    state_counts: tuple[int, ...],
    mover_length: int,
    edge_counts: tuple[int, ...],
    progress_every: int,
) -> None:
    words = enumerate_words_with_edge_counts(len(state_counts), edge_counts)
    print(f"state_counts={state_counts}")
    print(f"mover_length={mover_length}")
    print(f"edge_counts={edge_counts}")
    print(f"words={len(words)}")
    exception_count = 0
    first_exception: tuple[int, ...] | None = None
    for word_index, word in enumerate(words, start=1):
        if find_return_cones(word, len(state_counts)):
            continue
        if find_binary_bounce_contexts(word, state_counts):
            continue
        if find_anchored_return_contexts(word, state_counts):
            continue
        exception_count += 1
        if first_exception is None:
            first_exception = word
        if progress_every and word_index % progress_every == 0:
            print(
                f"branch_progress word_index={word_index}/{len(words)} exceptions={exception_count}"
            )
    print(f"exceptions={exception_count}")
    if first_exception is not None:
        print(f"first_exception={first_exception}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--state-counts", required=True)
    parser.add_argument("--mover-length", type=int, default=29)
    parser.add_argument(
        "--mode",
        choices=(
            "summary",
            "zero-vectors",
            "scan-singletons",
            "scan-zero",
            "dump-zero-exceptions",
            "scan-branch",
        ),
        default="summary",
    )
    parser.add_argument("--start-index", type=int, default=0)
    parser.add_argument("--stop-index", type=int)
    parser.add_argument("--progress-every", type=int, default=0)
    parser.add_argument("--edge-counts")
    args = parser.parse_args()

    state_counts = parse_int_tuple(args.state_counts)
    if args.mode == "summary":
        mode_summary(state_counts, args.mover_length)
    elif args.mode == "zero-vectors":
        mode_zero_vectors(state_counts, args.mover_length)
    elif args.mode == "scan-singletons":
        mode_scan_singletons(state_counts, args.mover_length, args.start_index, args.stop_index)
    elif args.mode == "scan-zero":
        mode_scan_zero_vectors(
            state_counts,
            args.mover_length,
            args.start_index,
            args.stop_index,
            args.progress_every,
        )
    elif args.mode == "scan-branch":
        if not args.edge_counts:
            raise SystemExit("--edge-counts is required for --mode scan-branch")
        mode_scan_branch(
            state_counts,
            args.mover_length,
            parse_int_tuple(args.edge_counts),
            args.progress_every,
        )
    else:
        if not args.edge_counts:
            raise SystemExit("--edge-counts is required for --mode dump-zero-exceptions")
        mode_dump_zero_exceptions(
            state_counts,
            args.mover_length,
            parse_int_tuple(args.edge_counts),
        )


if __name__ == "__main__":
    main()
