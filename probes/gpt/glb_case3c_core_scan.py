#!/usr/bin/env python3
"""Scan true n=9 Case 3c orientations against the minimum {1,1,5} signature."""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter
from itertools import combinations


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from scripts.glb_adjacent_walk_scan import binary_parity_compatible, cycle_count_compatible
from scripts.glb_ring_family_scan import cyclic_edge_counts, enumerate_fair_ring_words
from scripts.glb_seeded_unsat_core import unsat_core_labels
from scripts.p2_seeded_cycle_search import solve_good_cycle_from_movers


SIGNATURE = (1, 1, 3, 3, 3, 3, 3, 3, 5)


def pairwise_nonadjacent_case3c_classes(n: int = 9) -> list[tuple[int, ...]]:
    seen: set[tuple[int, ...]] = set()
    classes: list[tuple[int, ...]] = []
    for bins in combinations(range(n), 3):
        bin_set = set(bins)
        if any((b + 1) % n in bin_set or (b - 1) % n in bin_set for b in bins):
            continue
        for quaternary in range(n):
            if quaternary in bin_set:
                continue
            state_counts = [3] * n
            for b in bin_set:
                state_counts[b] = 2
            state_counts[quaternary] = 4
            rotations = [tuple(state_counts[i:] + state_counts[:i]) for i in range(n)]
            canonical = min(rotations)
            if canonical in seen:
                continue
            seen.add(canonical)
            classes.append(canonical)
    return sorted(classes)


def binary_gap_pattern(state_counts: tuple[int, ...]) -> tuple[int, ...]:
    n = len(state_counts)
    binaries = [i for i, state_count in enumerate(state_counts) if state_count == 2]
    gaps = [((binaries[(i + 1) % 3] - binaries[i]) % n) - 1 for i in range(3)]
    return min(tuple(gaps[i:] + gaps[:i]) for i in range(3))


def signature_words(n: int = 9, mover_length: int = 25) -> list[tuple[int, ...]]:
    words: list[tuple[int, ...]] = []
    for movers in enumerate_fair_ring_words(n, mover_length):
        if tuple(sorted(cyclic_edge_counts(movers, n))) != SIGNATURE:
            continue
        if not cycle_count_compatible(movers, n):
            continue
        words.append(movers)
    return words


def first_compatible_word(
    state_counts: tuple[int, ...],
    movers_catalog: list[tuple[int, ...]],
) -> tuple[int, ...] | None:
    for movers in movers_catalog:
        if binary_parity_compatible(state_counts, movers):
            return movers
    return None


def first_context_and_move(core: list[str]) -> tuple[str | None, str | None]:
    ctx = next((label for label in core if label.startswith("ctx_")), None)
    move = next((label for label in core if label.startswith("move_")), None)
    return ctx, move


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout-ms", type=int, default=1000)
    args = parser.parse_args()

    classes = pairwise_nonadjacent_case3c_classes()
    movers_catalog = signature_words()
    print(f"pairwise_nonadjacent_classes={len(classes)}")
    print(f"signature_words={len(movers_catalog)}")

    gap_counter: Counter[tuple[int, ...]] = Counter()
    core_counter: Counter[tuple[str | None, str | None]] = Counter()
    outcome_counter: Counter[str] = Counter()

    for state_counts in classes:
        gap = binary_gap_pattern(state_counts)
        gap_counter[gap] += 1
        movers = first_compatible_word(state_counts, movers_catalog)
        if movers is None:
            outcome_counter["no_word"] += 1
            print(f"ms={state_counts} gap={gap} outcome=no_signature_word")
            continue

        result = solve_good_cycle_from_movers(state_counts, movers, timeout_ms=args.timeout_ms)
        if result.found:
            outcome_counter["sat"] += 1
            print(f"ms={state_counts} gap={gap} outcome=sat movers={movers}")
            continue

        if "unknown" in result.message:
            outcome_counter["unknown"] += 1
            print(f"ms={state_counts} gap={gap} outcome=unknown movers={movers}")
            continue

        status, core = unsat_core_labels(state_counts, movers)
        assert status == "unsat"
        ctx, move = first_context_and_move(core)
        core_counter[(ctx, move)] += 1
        outcome_counter["unsat"] += 1
        print(
            f"ms={state_counts} gap={gap} outcome=unsat ctx={ctx} move={move} "
            f"movers={movers}"
        )

    print(f"gap_counter={dict(sorted(gap_counter.items()))}")
    print(f"outcomes={dict(sorted(outcome_counter.items()))}")
    print("core_counter:")
    for key, value in core_counter.most_common():
        print(f"  {key}: {value}")


if __name__ == "__main__":
    main()
