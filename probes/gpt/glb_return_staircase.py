#!/usr/bin/env python3
"""Detect return-staircase intervals in adjacent mover words."""

from __future__ import annotations

import argparse
from collections import Counter


def parse_int_tuple(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def contiguous_segment(vertices: set[int], n: int) -> tuple[int, int] | None:
    if not vertices:
        return None
    ordered = sorted(vertices)
    for start in ordered:
        segment = {(start + offset) % n for offset in range(len(vertices))}
        if segment == vertices:
            return start, (start + len(vertices) - 1) % n
    return None


def first_last_occurrences(movers: tuple[int, ...], n: int) -> tuple[dict[int, int], dict[int, int]]:
    total_counts = Counter(movers)
    first_occurrence = {vertex: movers.index(vertex) for vertex in range(n) if vertex in total_counts}
    last_occurrence = {vertex: max(i for i, mover in enumerate(movers) if mover == vertex) for vertex in range(n)}
    return first_occurrence, last_occurrence


def find_return_cones(movers: tuple[int, ...], n: int) -> list[dict[str, object]]:
    first_occurrence, last_occurrence = first_last_occurrences(movers, n)
    witnesses: list[dict[str, object]] = []
    for t in range(len(movers)):
        support: set[int] = set()
        for u in range(t + 1, len(movers) + 1):
            support.add(movers[u - 1])
            segment = contiguous_segment(support, n)
            if segment is None:
                continue
            if len(support) <= 1 or len(support) >= n:
                continue
            if any(first_occurrence[vertex] < t for vertex in support):
                continue
            if any(last_occurrence[vertex] >= u for vertex in support):
                continue
            witnesses.append(
                {
                    "t": t,
                    "u": u,
                    "segment_start": segment[0],
                    "segment_end": segment[1],
                    "support": tuple(sorted(support)),
                    "subword": movers[t:u],
                }
            )
    return witnesses


def find_binary_bounce_contexts(
    movers: tuple[int, ...],
    state_counts: tuple[int, ...],
) -> list[dict[str, object]]:
    n = len(state_counts)
    witnesses: list[dict[str, object]] = []
    for t in range(len(movers)):
        for u in range(t + 1, len(movers)):
            for processor in range(n):
                left = (processor - 1) % n
                right = (processor + 1) % n

                for binary_neighbor, fixed_neighbor in ((left, right), (right, left)):
                    if state_counts[binary_neighbor] != 2:
                        continue
                    segment = movers[t:u]
                    if movers[t] == processor:
                        continue
                    if movers[u] != processor:
                        continue
                    if processor in segment:
                        continue
                    if processor == fixed_neighbor or processor == binary_neighbor:
                        continue
                    if fixed_neighbor in segment:
                        continue
                    if sum(1 for mover in segment if mover == binary_neighbor) != 2:
                        continue
                    witnesses.append(
                        {
                            "t": t,
                            "u": u,
                            "processor": processor,
                            "binary_neighbor": binary_neighbor,
                            "fixed_neighbor": fixed_neighbor,
                            "subword": movers[t:u],
                            "mover_t": movers[t],
                            "mover_u": movers[u],
                        }
                    )
    return witnesses


def find_even_return_contexts(
    movers: tuple[int, ...],
    state_counts: tuple[int, ...],
) -> list[dict[str, object]]:
    witnesses: list[dict[str, object]] = []
    n = len(state_counts)
    for t in range(len(movers)):
        for u in range(t + 1, len(movers)):
            processor = movers[u]
            segment = movers[t:u]
            if processor in segment:
                continue

            left = (processor - 1) % n
            right = (processor + 1) % n
            neighbor_data = []
            for neighbor in (left, right):
                count = sum(1 for mover in segment if mover == neighbor)
                if count == 0:
                    neighbor_data.append((neighbor, count, "fixed"))
                    continue
                if state_counts[neighbor] == 2 and count % 2 == 0:
                    neighbor_data.append((neighbor, count, "binary-even"))
                    continue
                break
            else:
                witnesses.append(
                    {
                        "t": t,
                        "u": u,
                        "processor": processor,
                        "left": left,
                        "right": right,
                        "neighbor_data": tuple(neighbor_data),
                        "subword": segment,
                        "mover_t": movers[t],
                        "mover_u": movers[u],
                    }
                )
    return witnesses


def find_anchored_return_contexts(
    movers: tuple[int, ...],
    state_counts: tuple[int, ...],
) -> list[dict[str, object]]:
    n = len(state_counts)
    total_counts = Counter(movers)
    prefix_counts = [Counter()]
    running = Counter()
    for mover in movers:
        running = running.copy()
        running[mover] += 1
        prefix_counts.append(running)

    def count_in_interval(processor: int, start: int, stop: int) -> int:
        return prefix_counts[stop][processor] - prefix_counts[start][processor]

    witnesses: list[dict[str, object]] = []
    for t, processor in enumerate(movers):
        if prefix_counts[t][processor] != 0:
            continue
        for u in range(t + 1, len(movers)):
            if movers[u] == processor:
                continue
            if count_in_interval(processor, u, len(movers)) != 0:
                continue

            neighbor_data = []
            ok = True
            for neighbor in ((processor - 1) % n, (processor + 1) % n):
                interval_count = count_in_interval(neighbor, t, u)
                if state_counts[neighbor] == 2 and interval_count % 2 == 0:
                    neighbor_data.append((neighbor, interval_count, "binary-even"))
                    continue
                if prefix_counts[t][neighbor] == 0 and count_in_interval(neighbor, u, len(movers)) == 0:
                    neighbor_data.append((neighbor, interval_count, "anchored-finished"))
                    continue
                ok = False
                break

            if not ok:
                continue

            witnesses.append(
                {
                    "t": t,
                    "u": u,
                    "processor": processor,
                    "neighbor_data": tuple(neighbor_data),
                    "subword": movers[t:u],
                    "mover_t": movers[t],
                    "mover_u": movers[u],
                }
            )
    return witnesses


def find_return_staircases(movers: tuple[int, ...], n: int) -> list[dict[str, object]]:
    first_occurrence, last_occurrence = first_last_occurrences(movers, n)

    witnesses: list[dict[str, object]] = []
    for t in range(len(movers)):
        seen: Counter[int] = Counter()
        support: set[int] = set()
        for u in range(t + 1, len(movers) + 1):
            mover = movers[u - 1]
            seen[mover] += 1
            support.add(mover)
            segment = contiguous_segment(support, n)
            if segment is None:
                continue
            if len(support) <= 1 or len(support) >= n:
                continue
            if any(count != 2 for count in seen.values()):
                continue
            if any(first_occurrence[vertex] < t for vertex in support):
                continue
            if any(last_occurrence[vertex] >= u for vertex in support):
                continue
            witnesses.append(
                {
                    "t": t,
                    "u": u,
                    "segment_start": segment[0],
                    "segment_end": segment[1],
                    "support": tuple(sorted(support)),
                    "subword": movers[t:u],
                }
            )
    return witnesses


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--movers", required=True)
    parser.add_argument("--n", type=int, default=9)
    parser.add_argument("--state-counts")
    parser.add_argument(
        "--mode",
        choices=("staircase", "cone", "binary-bounce", "even-return", "anchored-return"),
        default="staircase",
    )
    args = parser.parse_args()

    movers = parse_int_tuple(args.movers)
    if args.mode == "staircase":
        witnesses = find_return_staircases(movers, args.n)
    elif args.mode == "cone":
        witnesses = find_return_cones(movers, args.n)
    elif args.mode == "binary-bounce":
        if not args.state_counts:
            raise SystemExit("--state-counts is required for --mode binary-bounce")
        witnesses = find_binary_bounce_contexts(movers, parse_int_tuple(args.state_counts))
    elif args.mode == "anchored-return":
        if not args.state_counts:
            raise SystemExit("--state-counts is required for --mode anchored-return")
        witnesses = find_anchored_return_contexts(movers, parse_int_tuple(args.state_counts))
    else:
        if not args.state_counts:
            raise SystemExit("--state-counts is required for --mode even-return")
        witnesses = find_even_return_contexts(movers, parse_int_tuple(args.state_counts))
    print(f"count={len(witnesses)}")
    for witness in witnesses:
        if args.mode == "binary-bounce":
            print(
                f"t={witness['t']} u={witness['u']} processor={witness['processor']} "
                f"binary_neighbor={witness['binary_neighbor']} fixed_neighbor={witness['fixed_neighbor']} "
                f"mover_t={witness['mover_t']} mover_u={witness['mover_u']} subword={witness['subword']}"
            )
        elif args.mode == "even-return":
            print(
                f"t={witness['t']} u={witness['u']} processor={witness['processor']} "
                f"left={witness['left']} right={witness['right']} "
                f"neighbor_data={witness['neighbor_data']} mover_t={witness['mover_t']} "
                f"mover_u={witness['mover_u']} subword={witness['subword']}"
            )
        elif args.mode == "anchored-return":
            print(
                f"t={witness['t']} u={witness['u']} processor={witness['processor']} "
                f"neighbor_data={witness['neighbor_data']} mover_t={witness['mover_t']} "
                f"mover_u={witness['mover_u']} subword={witness['subword']}"
            )
        else:
            print(
                f"t={witness['t']} u={witness['u']} support={witness['support']} "
                f"segment=({witness['segment_start']},{witness['segment_end']}) subword={witness['subword']}"
            )


if __name__ == "__main__":
    main()
