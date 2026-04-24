#!/usr/bin/env python3
"""Scan adjacent fair mover words on the cut chain 0..n-1.

This script treats a mover word as a walk on the line graph `0--1--...--n-1`:
successive movers differ by exactly one. It enumerates fair words of a fixed
length, classifies them by turnaround count, applies the binary parity filter,
and optionally runs the seeded good-cycle SAT check on the survivors.
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

from scripts.p2_seeded_cycle_search import solve_good_cycle_from_movers


def parse_state_counts(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def count_turnarounds(movers: tuple[int, ...]) -> int:
    turns = 0
    for left, mid, right in zip(movers, movers[1:], movers[2:]):
        if (mid - left) != (right - mid):
            turns += 1
    return turns


def mover_counts(movers: tuple[int, ...]) -> Counter[int]:
    return Counter(movers)


def even_count_processors(movers: tuple[int, ...], n: int) -> tuple[int, ...]:
    counts = mover_counts(movers)
    return tuple(processor for processor in range(n) if counts[processor] % 2 == 0)


def binary_parity_compatible(state_counts: tuple[int, ...], movers: tuple[int, ...]) -> bool:
    counts = mover_counts(movers)
    for processor, state_count in enumerate(state_counts):
        if state_count == 2 and counts[processor] % 2 == 1:
            return False
    return True


def cycle_count_compatible(movers: tuple[int, ...], n: int) -> bool:
    counts = mover_counts(movers)
    return all(counts[processor] != 1 for processor in range(n))


def returns_to_bottom_before_top(movers: tuple[int, ...], bottom: int = 0, top: int | None = None) -> bool:
    if top is None:
        top = max(movers)
    first_top = movers.index(top)
    return any(mover == bottom for mover in movers[1:first_top])


def first_hit(movers: tuple[int, ...], vertex: int) -> int:
    return movers.index(vertex)


def last_hit(movers: tuple[int, ...], vertex: int) -> int:
    return max(index for index, mover in enumerate(movers) if mover == vertex)


def enumerate_fair_adjacent_walks(n: int, mover_length: int) -> Iterable[tuple[int, ...]]:
    target = n - 1
    full_seen = (1 << n) - 1

    def rec(prefix: list[int], seen_mask: int) -> Iterable[tuple[int, ...]]:
        if len(prefix) == mover_length:
            if prefix[-1] == target and seen_mask == full_seen:
                yield tuple(prefix)
            return

        position = prefix[-1]
        for nxt in (position - 1, position + 1):
            if 0 <= nxt < n:
                prefix.append(nxt)
                yield from rec(prefix, seen_mask | (1 << nxt))
                prefix.pop()

    yield from rec([0], 1)


def mode_turn_summary(n: int, mover_length: int) -> None:
    counts: Counter[int] = Counter()
    examples: dict[int, tuple[int, ...]] = {}
    total = 0
    for movers in enumerate_fair_adjacent_walks(n, mover_length):
        total += 1
        turns = count_turnarounds(movers)
        counts[turns] += 1
        examples.setdefault(turns, movers)

    print(f"total_words={total}")
    for turns in sorted(counts):
        print(f"turnarounds={turns} count={counts[turns]} example={examples[turns]}")


def mode_filter_summary(n: int, mover_length: int, state_counts: tuple[int, ...]) -> None:
    total = 0
    parity_ok = 0
    cycle_ok = 0
    by_turns: dict[int, Counter[str]] = {}

    for movers in enumerate_fair_adjacent_walks(n, mover_length):
        turns = count_turnarounds(movers)
        total += 1
        by_turns.setdefault(turns, Counter())
        by_turns[turns]["total"] += 1
        if not binary_parity_compatible(state_counts, movers):
            by_turns[turns]["parity_blocked"] += 1
            continue
        parity_ok += 1
        by_turns[turns]["parity_ok"] += 1
        if not cycle_count_compatible(movers, n):
            by_turns[turns]["single_move_blocked"] += 1
            continue
        cycle_ok += 1
        by_turns[turns]["cycle_ok"] += 1

    print(f"state_counts={state_counts} total={total} parity_ok={parity_ok} cycle_ok={cycle_ok}")
    for turns in sorted(by_turns):
        row = by_turns[turns]
        print(
            f"turnarounds={turns} total={row['total']} parity_blocked={row['parity_blocked']} "
            f"parity_ok={row['parity_ok']} single_move_blocked={row['single_move_blocked']} "
            f"cycle_ok={row['cycle_ok']}"
        )


def mode_bottom_return_summary(n: int, mover_length: int, state_counts: tuple[int, ...]) -> None:
    rows: Counter[tuple[int, bool]] = Counter()
    examples: dict[tuple[int, bool], tuple[int, ...]] = {}
    total_cycle_ok = 0

    for movers in enumerate_fair_adjacent_walks(n, mover_length):
        if not binary_parity_compatible(state_counts, movers):
            continue
        if not cycle_count_compatible(movers, n):
            continue
        total_cycle_ok += 1
        key = (count_turnarounds(movers), returns_to_bottom_before_top(movers, bottom=0, top=n - 1))
        rows[key] += 1
        examples.setdefault(key, movers)

    print(f"state_counts={state_counts} cycle_ok={total_cycle_ok}")
    for key in sorted(rows):
        turns, returns = key
        print(f"turnarounds={turns} returns_to_0_before_{n-1}={returns} count={rows[key]} example={examples[key]}")


def mode_window_summary(n: int, mover_length: int, state_counts: tuple[int, ...]) -> None:
    rows: Counter[tuple[int, int, bool, bool]] = Counter()
    examples: dict[tuple[int, int, bool, bool], tuple[int, ...]] = {}

    for movers in enumerate_fair_adjacent_walks(n, mover_length):
        if not binary_parity_compatible(state_counts, movers):
            continue
        if not cycle_count_compatible(movers, n):
            continue

        top = n - 1
        first_top = first_hit(movers, top)
        key = (
            count_turnarounds(movers),
            first_top,
            last_hit(movers, 0) < first_top,
            last_hit(movers, 1) < first_top,
        )
        rows[key] += 1
        examples.setdefault(key, movers)

    print(f"state_counts={state_counts}")
    for key in sorted(rows):
        turns, first_top, last0_before, last1_before = key
        print(
            f"turnarounds={turns} first_top={first_top} "
            f"last0_before_top={last0_before} last1_before_top={last1_before} "
            f"count={rows[key]} example={examples[key]}"
        )


def mode_sat_scan(
    n: int,
    mover_length: int,
    state_counts: tuple[int, ...],
    timeout_ms: int,
    turn_counts: set[int] | None,
    limit: int | None,
) -> None:
    total = 0
    parity_ok = 0
    cycle_ok = 0
    hits = 0
    unknowns = 0
    by_turns: dict[int, Counter[str]] = {}
    first_hit: dict[int, tuple[int, ...]] = {}

    for movers in enumerate_fair_adjacent_walks(n, mover_length):
        turns = count_turnarounds(movers)
        if turn_counts is not None and turns not in turn_counts:
            continue
        total += 1
        by_turns.setdefault(turns, Counter())
        by_turns[turns]["total"] += 1

        if not binary_parity_compatible(state_counts, movers):
            by_turns[turns]["parity_blocked"] += 1
            continue

        parity_ok += 1
        by_turns[turns]["parity_ok"] += 1
        if not cycle_count_compatible(movers, n):
            by_turns[turns]["single_move_blocked"] += 1
            continue

        cycle_ok += 1
        by_turns[turns]["cycle_ok"] += 1
        result = solve_good_cycle_from_movers(state_counts, movers, timeout_ms=timeout_ms)
        if result.found:
            hits += 1
            by_turns[turns]["sat"] += 1
            first_hit.setdefault(turns, movers)
        elif "unknown" in result.message:
            unknowns += 1
            by_turns[turns]["unknown"] += 1
        else:
            by_turns[turns]["unsat"] += 1

        if limit is not None and total >= limit:
            break

    print(
        f"state_counts={state_counts} total={total} parity_ok={parity_ok} cycle_ok={cycle_ok} "
        f"sat_hits={hits} unknowns={unknowns}"
    )
    for turns in sorted(by_turns):
        row = by_turns[turns]
        print(
            f"turnarounds={turns} total={row['total']} parity_blocked={row['parity_blocked']} "
            f"parity_ok={row['parity_ok']} single_move_blocked={row['single_move_blocked']} "
            f"cycle_ok={row['cycle_ok']} sat={row['sat']} unknown={row['unknown']} unsat={row['unsat']}"
        )
        if turns in first_hit:
            print(f"  first_hit={first_hit[turns]}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--mode",
        choices=("turn-summary", "filter-summary", "bottom-return-summary", "window-summary", "sat-scan"),
        default="turn-summary",
    )
    parser.add_argument("--n", type=int, default=9)
    parser.add_argument("--mover-length", type=int, default=25)
    parser.add_argument("--state-counts", default="2,3,3,3,3,3,3,3,2")
    parser.add_argument("--timeout-ms", type=int, default=1000)
    parser.add_argument("--turn-counts", help="comma-separated turnaround counts to keep")
    parser.add_argument("--limit", type=int)
    args = parser.parse_args()

    if args.mode == "turn-summary":
        mode_turn_summary(args.n, args.mover_length)
        return
    if args.mode == "filter-summary":
        mode_filter_summary(args.n, args.mover_length, parse_state_counts(args.state_counts))
        return
    if args.mode == "bottom-return-summary":
        mode_bottom_return_summary(args.n, args.mover_length, parse_state_counts(args.state_counts))
        return
    if args.mode == "window-summary":
        mode_window_summary(args.n, args.mover_length, parse_state_counts(args.state_counts))
        return

    turn_counts = None
    if args.turn_counts:
        turn_counts = {int(part.strip()) for part in args.turn_counts.split(",") if part.strip()}
    mode_sat_scan(
        n=args.n,
        mover_length=args.mover_length,
        state_counts=parse_state_counts(args.state_counts),
        timeout_ms=args.timeout_ms,
        turn_counts=turn_counts,
        limit=args.limit,
    )


if __name__ == "__main__":
    main()
