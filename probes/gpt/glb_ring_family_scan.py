#!/usr/bin/env python3
"""Classify ring-adjacent length-(3n-2) mover words by known family membership.

The known valid cyclic families are:

1. The bounce family
2. The bottom-insertion family

This script enumerates fair ring-adjacent cyclic mover words, filters by the
binary parity and no-single-move lemmas, and then classifies the surviving
internal-wrap words by:

- dihedral family membership (rotation or reversal of bounce / insertion),
- rotation class,
- cyclic edge-count vector.
"""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter
from typing import Iterable


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from scripts.glb_adjacent_walk_scan import binary_parity_compatible, cycle_count_compatible
from scripts.p2_seeded_cycle_search import solve_good_cycle_from_movers


def parse_state_counts(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def load_mover_words(path: str) -> list[tuple[int, ...]]:
    words: list[tuple[int, ...]] = []
    with open(path, encoding="utf-8") as handle:
        for line in handle:
            stripped = line.strip()
            if not stripped:
                continue
            words.append(tuple(int(part) for part in stripped.split()))
    return words


def bounce_word(n: int) -> tuple[int, ...]:
    return tuple(list(range(n)) + list(range(n - 2, 0, -1)) + list(range(n)))


def insertion_word(n: int) -> tuple[int, ...]:
    return tuple([0, 1, 0] + list(range(1, n)) + list(range(n - 2, 0, -1)) + list(range(2, n)))


def shifts(word: tuple[int, ...]) -> list[tuple[int, ...]]:
    return [word[offset:] + word[:offset] for offset in range(len(word))]


def canonical_rotation(word: tuple[int, ...]) -> tuple[int, ...]:
    return min(shifts(word))


def canonical_dihedral(word: tuple[int, ...]) -> tuple[int, ...]:
    variants = shifts(word) + shifts(tuple(reversed(word)))
    return min(variants)


def internal_wrap_used(word: tuple[int, ...], n: int) -> bool:
    return any({left, right} == {0, n - 1} for left, right in zip(word, word[1:]))


def cyclic_edge_counts(word: tuple[int, ...], n: int) -> tuple[int, ...]:
    counts = [0] * n
    cyclic = word[1:] + word[:1]
    for left, right in zip(word, cyclic, strict=True):
        if (right - left) % n == 1:
            edge = left
        elif (left - right) % n == 1:
            edge = right
        else:
            raise ValueError(f"non-adjacent pair {left}->{right} in word {word}")
        counts[edge] += 1
    return tuple(counts)


def enumerate_fair_ring_words(n: int, mover_length: int) -> Iterable[tuple[int, ...]]:
    full_seen = (1 << n) - 1

    def rec(prefix: list[int], seen_mask: int) -> Iterable[tuple[int, ...]]:
        if len(prefix) == mover_length:
            last = prefix[-1]
            if seen_mask == full_seen and last in {(0 - 1) % n, (0 + 1) % n}:
                yield tuple(prefix)
            return

        position = prefix[-1]
        for nxt in ((position - 1) % n, (position + 1) % n):
            prefix.append(nxt)
            yield from rec(prefix, seen_mask | (1 << nxt))
            prefix.pop()

    yield from rec([0], 1)


def known_family_canons(n: int) -> dict[str, tuple[int, ...]]:
    return {
        "bounce": canonical_dihedral(bounce_word(n)),
        "insertion": canonical_dihedral(insertion_word(n)),
    }


def classify_wrap_survivors(
    n: int,
    mover_length: int,
    state_counts: tuple[int, ...],
) -> dict[str, object]:
    families = known_family_canons(n)
    family_lookup = {canon: label for label, canon in families.items()}

    total_fair = 0
    total_wrap = 0
    total_wrap_parity = 0
    total_wrap_cycle = 0
    family_word_counts = Counter()
    family_rotation_classes: dict[str, set[tuple[int, ...]]] = {label: set() for label in families}
    unknown_rotation_reps: dict[tuple[int, ...], tuple[int, ...]] = {}
    unknown_dihedral_reps: dict[tuple[int, ...], tuple[int, ...]] = {}
    unknown_edge_vector_reps: dict[tuple[int, ...], tuple[int, ...]] = {}

    for movers in enumerate_fair_ring_words(n, mover_length):
        total_fair += 1
        if not internal_wrap_used(movers, n):
            continue
        total_wrap += 1
        if not binary_parity_compatible(state_counts, movers):
            continue
        total_wrap_parity += 1
        if not cycle_count_compatible(movers, n):
            continue
        total_wrap_cycle += 1

        dihedral = canonical_dihedral(movers)
        family = family_lookup.get(dihedral)
        if family is not None:
            family_word_counts[family] += 1
            family_rotation_classes[family].add(canonical_rotation(movers))
            continue

        rotation = canonical_rotation(movers)
        unknown_rotation_reps.setdefault(rotation, movers)
        unknown_dihedral_reps.setdefault(dihedral, movers)
        unknown_edge_vector_reps.setdefault(cyclic_edge_counts(movers, n), movers)

    return {
        "families": families,
        "total_fair": total_fair,
        "total_wrap": total_wrap,
        "total_wrap_parity": total_wrap_parity,
        "total_wrap_cycle": total_wrap_cycle,
        "family_word_counts": family_word_counts,
        "family_rotation_classes": {label: len(classes) for label, classes in family_rotation_classes.items()},
        "unknown_rotation_reps": unknown_rotation_reps,
        "unknown_dihedral_reps": unknown_dihedral_reps,
        "unknown_edge_vector_reps": unknown_edge_vector_reps,
    }


def mode_summary(n: int, mover_length: int, state_counts: tuple[int, ...]) -> None:
    stats = classify_wrap_survivors(n, mover_length, state_counts)
    print(f"state_counts={state_counts} n={n} mover_length={mover_length}")
    print(f"total_fair={stats['total_fair']}")
    print(f"wrap_total={stats['total_wrap']}")
    print(f"wrap_parity={stats['total_wrap_parity']}")
    print(f"wrap_cycle={stats['total_wrap_cycle']}")
    print(f"family_word_counts={dict(stats['family_word_counts'])}")
    print(f"family_rotation_classes={stats['family_rotation_classes']}")
    print(f"unknown_rotation_classes={len(stats['unknown_rotation_reps'])}")
    print(f"unknown_dihedral_classes={len(stats['unknown_dihedral_reps'])}")
    print(f"unknown_edge_vectors={len(stats['unknown_edge_vector_reps'])}")
    for family_name, canon in stats["families"].items():
        print(f"{family_name}_canon={canon}")


def mode_unknown_sat(
    n: int,
    mover_length: int,
    state_counts: tuple[int, ...],
    timeout_ms: int,
    second_timeout_ms: int | None,
    progress_every: int,
    start_index: int,
    stop_index: int | None,
) -> None:
    stats = classify_wrap_survivors(n, mover_length, state_counts)
    hits = 0
    unknowns = 0
    rerun_hits = 0
    rerun_unknowns = 0
    rerun_queue: list[tuple[int, tuple[int, ...]]] = []
    reps = sorted(stats["unknown_rotation_reps"].items())
    selected = reps[start_index:stop_index]
    base_index = start_index + 1
    for offset, (_rotation, movers) in enumerate(selected, start=1):
        index = start_index + offset
        result = solve_good_cycle_from_movers(state_counts, movers, timeout_ms=timeout_ms)
        if result.found:
            hits += 1
            print(
                f"HIT rotation_class={index}/{len(reps)} elapsed={result.elapsed:.3f}s "
                f"movers={movers}"
            )
        elif "unknown" in result.message:
            unknowns += 1
            rerun_queue.append((index, movers))
            print(
                f"UNKNOWN rotation_class={index}/{len(reps)} elapsed={result.elapsed:.3f}s "
                f"message={result.message} movers={movers}"
            )
        elif progress_every and index % progress_every == 0:
            print(
                f"progress rotation_class={index}/{len(reps)} "
                f"hits={hits} unknowns={unknowns}"
            )
    if second_timeout_ms and second_timeout_ms > timeout_ms and rerun_queue:
        print(
            f"rerunning_unknown_rotation_classes count={len(rerun_queue)} "
            f"timeout_ms={second_timeout_ms}"
        )
        for index, movers in rerun_queue:
            result = solve_good_cycle_from_movers(state_counts, movers, timeout_ms=second_timeout_ms)
            if result.found:
                rerun_hits += 1
                print(
                    f"RERUN_HIT rotation_class={index}/{len(reps)} elapsed={result.elapsed:.3f}s "
                    f"movers={movers}"
                )
            elif "unknown" in result.message:
                rerun_unknowns += 1
                print(
                    f"RERUN_UNKNOWN rotation_class={index}/{len(reps)} elapsed={result.elapsed:.3f}s "
                    f"message={result.message} movers={movers}"
                )
    print(
        f"rotation_slice_start={base_index} "
        f"rotation_slice_stop={start_index + len(selected)} "
        f"rotation_slice_total={len(selected)} "
        f"sat_hits={hits} unknowns={unknowns} unsat={len(selected) - hits - unknowns} "
        f"rerun_hits={rerun_hits} rerun_unknowns={rerun_unknowns}"
    )


def mode_edge_vector_sat(
    n: int,
    mover_length: int,
    state_counts: tuple[int, ...],
    timeout_ms: int,
    progress_every: int,
) -> None:
    stats = classify_wrap_survivors(n, mover_length, state_counts)
    hits = 0
    unknowns = 0
    reps = sorted(stats["unknown_edge_vector_reps"].items())
    for index, (edge_vector, movers) in enumerate(reps, start=1):
        result = solve_good_cycle_from_movers(state_counts, movers, timeout_ms=timeout_ms)
        if result.found:
            hits += 1
            print(
                f"HIT edge_vector_class={index}/{len(reps)} edge_vector={edge_vector} "
                f"elapsed={result.elapsed:.3f}s movers={movers}"
            )
        elif "unknown" in result.message:
            unknowns += 1
            print(
                f"UNKNOWN edge_vector_class={index}/{len(reps)} edge_vector={edge_vector} "
                f"elapsed={result.elapsed:.3f}s message={result.message}"
            )
        elif progress_every and index % progress_every == 0:
            print(
                f"progress edge_vector_class={index}/{len(reps)} "
                f"hits={hits} unknowns={unknowns}"
            )
    print(
        f"unknown_edge_vectors={len(reps)} sat_hits={hits} "
        f"unknowns={unknowns} unsat={len(reps) - hits - unknowns}"
    )


def mode_dihedral_sat(
    n: int,
    mover_length: int,
    state_counts: tuple[int, ...],
    timeout_ms: int,
    progress_every: int,
    start_index: int,
    stop_index: int | None,
) -> None:
    stats = classify_wrap_survivors(n, mover_length, state_counts)
    hits = 0
    unknowns = 0
    reps = sorted(stats["unknown_dihedral_reps"].items())
    selected = reps[start_index:stop_index]
    base_index = start_index + 1
    for offset, (_dihedral, movers) in enumerate(selected, start=1):
        index = start_index + offset
        result = solve_good_cycle_from_movers(state_counts, movers, timeout_ms=timeout_ms)
        if result.found:
            hits += 1
            print(
                f"HIT dihedral_class={index}/{len(reps)} elapsed={result.elapsed:.3f}s "
                f"movers={movers}"
            )
        elif "unknown" in result.message:
            unknowns += 1
            print(
                f"UNKNOWN dihedral_class={index}/{len(reps)} elapsed={result.elapsed:.3f}s "
                f"message={result.message}"
            )
        elif progress_every and index % progress_every == 0:
            print(
                f"progress dihedral_class={index}/{len(reps)} "
                f"hits={hits} unknowns={unknowns}"
            )
    print(
        f"dihedral_slice_start={base_index} "
        f"dihedral_slice_stop={start_index + len(selected)} "
        f"dihedral_slice_total={len(selected)} "
        f"sat_hits={hits} unknowns={unknowns} unsat={len(selected) - hits - unknowns}"
    )


def mode_cached_rotation_file_sat(
    movers_path: str,
    state_counts: tuple[int, ...],
    timeout_ms: int,
    second_timeout_ms: int | None,
    progress_every: int,
    start_index: int,
    stop_index: int | None,
) -> None:
    words = load_mover_words(movers_path)
    selected = words[start_index:stop_index]
    total = len(words)
    hits = 0
    unknowns = 0
    rerun_hits = 0
    rerun_unknowns = 0
    rerun_queue: list[tuple[int, tuple[int, ...]]] = []

    for offset, movers in enumerate(selected, start=1):
        index = start_index + offset
        result = solve_good_cycle_from_movers(state_counts, movers, timeout_ms=timeout_ms)
        if result.found:
            hits += 1
            print(
                f"HIT cached_rotation_class={index}/{total} elapsed={result.elapsed:.3f}s "
                f"movers={movers}"
            )
        elif "unknown" in result.message:
            unknowns += 1
            rerun_queue.append((index, movers))
            print(
                f"UNKNOWN cached_rotation_class={index}/{total} elapsed={result.elapsed:.3f}s "
                f"message={result.message} movers={movers}"
            )
        elif progress_every and index % progress_every == 0:
            print(
                f"progress cached_rotation_class={index}/{total} "
                f"hits={hits} unknowns={unknowns}"
            )

    if second_timeout_ms and second_timeout_ms > timeout_ms and rerun_queue:
        print(
            f"rerunning_unknown_cached_rotation_classes count={len(rerun_queue)} "
            f"timeout_ms={second_timeout_ms}"
        )
        for index, movers in rerun_queue:
            result = solve_good_cycle_from_movers(state_counts, movers, timeout_ms=second_timeout_ms)
            if result.found:
                rerun_hits += 1
                print(
                    f"RERUN_HIT cached_rotation_class={index}/{total} elapsed={result.elapsed:.3f}s "
                    f"movers={movers}"
                )
            elif "unknown" in result.message:
                rerun_unknowns += 1
                print(
                    f"RERUN_UNKNOWN cached_rotation_class={index}/{total} elapsed={result.elapsed:.3f}s "
                    f"message={result.message} movers={movers}"
                )

    print(
        f"cached_rotation_slice_start={start_index + 1} "
        f"cached_rotation_slice_stop={start_index + len(selected)} "
        f"cached_rotation_slice_total={len(selected)} "
        f"sat_hits={hits} unknowns={unknowns} unsat={len(selected) - hits - unknowns} "
        f"rerun_hits={rerun_hits} rerun_unknowns={rerun_unknowns}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--mode",
        choices=("summary", "unknown-sat", "dihedral-sat", "edge-vector-sat", "cached-rotation-file-sat"),
        default="summary",
    )
    parser.add_argument("--n", type=int, default=9)
    parser.add_argument("--mover-length", type=int, default=25)
    parser.add_argument("--state-counts", default="2,3,3,3,3,3,3,3,2")
    parser.add_argument("--movers-path", default="")
    parser.add_argument("--timeout-ms", type=int, default=1000)
    parser.add_argument("--second-timeout-ms", type=int, default=None)
    parser.add_argument("--progress-every", type=int, default=25)
    parser.add_argument("--start-index", type=int, default=0)
    parser.add_argument("--stop-index", type=int, default=None)
    args = parser.parse_args()

    state_counts = parse_state_counts(args.state_counts)
    if args.mode == "summary":
        mode_summary(args.n, args.mover_length, state_counts)
        return
    if args.mode == "unknown-sat":
        mode_unknown_sat(
            args.n,
            args.mover_length,
            state_counts,
            args.timeout_ms,
            args.second_timeout_ms,
            args.progress_every,
            args.start_index,
            args.stop_index,
        )
        return
    if args.mode == "dihedral-sat":
        mode_dihedral_sat(
            args.n,
            args.mover_length,
            state_counts,
            args.timeout_ms,
            args.progress_every,
            args.start_index,
            args.stop_index,
        )
        return
    if args.mode == "edge-vector-sat":
        mode_edge_vector_sat(args.n, args.mover_length, state_counts, args.timeout_ms, args.progress_every)
        return
    if args.mode == "cached-rotation-file-sat":
        if not args.movers_path:
            raise ValueError("--movers-path is required for cached-rotation-file-sat")
        mode_cached_rotation_file_sat(
            args.movers_path,
            state_counts,
            args.timeout_ms,
            args.second_timeout_ms,
            args.progress_every,
            args.start_index,
            args.stop_index,
        )
        return


if __name__ == "__main__":
    main()
