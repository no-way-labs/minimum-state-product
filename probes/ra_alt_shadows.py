#!/usr/bin/env python3
"""Test alternative shadow constructions on the M_5=96 witness."""

from __future__ import annotations

from collections import deque
from typing import Callable

from ra_shadow_m5 import MS, START_CONFIG, build_m5_96_witness, rotate_cycle
from verifier import apply_move, privileged_set, verify_system


Config = tuple[int, ...]
VariantFn = Callable[[Config], Config]


def flip_binary(config: Config, proc: int) -> Config:
    shadow = list(config)
    shadow[proc] = 1 - shadow[proc]
    return tuple(shadow)


def shift_proc(config: Config, proc: int, delta: int) -> Config:
    shadow = list(config)
    shadow[proc] = (shadow[proc] + delta) % MS[proc]
    return tuple(shadow)


def variant1(config: Config) -> Config:
    return flip_binary(config, 1)


def variant2(config: Config) -> Config:
    return shift_proc(config, 3, 1)


def variant3(config: Config) -> Config:
    shadow = list(config)
    for proc in (0, 1, 2):
        shadow[proc] = 1 - shadow[proc]
    return tuple(shadow)


VARIANTS: list[tuple[str, str, VariantFn]] = [
    ("variant1", "Flip just proc 1 (middle binary)", variant1),
    ("variant2", "Shift proc 3 (ternary) by +1 mod 3", variant2),
    ("variant3", "Flip all binary procs 0,1,2", variant3),
]


def shortest_cycle(edges: dict[Config, list[tuple[int, Config]]]) -> tuple[int, list[int], list[Config]] | None:
    """Return the shortest directed cycle found in the explored bad graph."""
    best: tuple[int, list[int], list[Config]] | None = None
    for start in edges:
        queue = deque([start])
        dist = {start: 0}
        parent: dict[Config, Config | None] = {start: None}
        parent_move: dict[Config, int] = {}
        found: tuple[Config, int] | None = None

        while queue and found is None:
            node = queue.popleft()
            for mover, nxt in edges[node]:
                if nxt == start:
                    found = (node, mover)
                    break
                if nxt not in dist:
                    dist[nxt] = dist[node] + 1
                    parent[nxt] = node
                    parent_move[nxt] = mover
                    queue.append(nxt)

        if found is None:
            continue

        last_node, last_move = found
        path_nodes = []
        cur: Config | None = last_node
        while cur is not None:
            path_nodes.append(cur)
            cur = parent[cur]
        path_nodes.reverse()

        path_moves = [parent_move[node] for node in path_nodes[1:]]
        path_moves.append(last_move)
        cycle_nodes = path_nodes + [start]
        candidate = (len(path_moves), path_moves, cycle_nodes)
        if best is None or candidate[0] < best[0]:
            best = candidate
    return best


def explore_forced_orbit(
    start: Config,
    fs: list,
    good_cycle: set[Config],
    good_configs: set[Config],
) -> dict:
    if start in good_cycle:
        return {
            "start_status": "good_cycle",
            "reachable_bad": 0,
            "cycle_found": False,
            "cycle_length": None,
            "cycle_moves": [],
            "cycle_configs": [],
            "good_cycle_hits": 0,
            "good_tail_hits": 0,
        }

    if start in good_configs:
        return {
            "start_status": "good_tail",
            "reachable_bad": 0,
            "cycle_found": False,
            "cycle_length": None,
            "cycle_moves": [],
            "cycle_configs": [],
            "good_cycle_hits": 0,
            "good_tail_hits": 0,
        }

    queue = deque([start])
    visited_bad = {start}
    edges: dict[Config, list[tuple[int, Config]]] = {}
    good_cycle_hits = 0
    good_tail_hits = 0

    while queue:
        config = queue.popleft()
        next_edges: list[tuple[int, Config]] = []
        for proc in privileged_set(config, fs, MS):
            nxt = apply_move(config, proc, fs, MS)
            if nxt in good_cycle:
                good_cycle_hits += 1
                continue
            if nxt in good_configs:
                good_tail_hits += 1
                continue
            next_edges.append((proc, nxt))
            if nxt not in visited_bad:
                visited_bad.add(nxt)
                queue.append(nxt)
        edges[config] = next_edges

    cycle = shortest_cycle(edges)
    return {
        "start_status": "bad",
        "reachable_bad": len(visited_bad),
        "cycle_found": cycle is not None,
        "cycle_length": None if cycle is None else cycle[0],
        "cycle_moves": [] if cycle is None else cycle[1],
        "cycle_configs": [] if cycle is None else cycle[2],
        "good_cycle_hits": good_cycle_hits,
        "good_tail_hits": good_tail_hits,
    }


def format_moves(moves: list[int]) -> str:
    return "[" + ",".join(str(m) for m in moves) + "]"


def main() -> None:
    _, fs = build_m5_96_witness()
    result = verify_system(MS, fs, verbose=False)
    if not result["valid"]:
        raise SystemExit("M_5 witness failed verify_system(); aborting.")

    cycle = rotate_cycle(list(result["cycle"]), START_CONFIG)
    good_cycle = set(cycle)
    good_configs = set(result["good_configs"])

    print("Alternative shadow forced-orbit test on M_5=96 witness")
    print("=" * 72)
    print(f"ms = {MS}")
    print(f"good_cycle_length = {len(cycle)}")
    print(f"good_configs = {len(good_configs)}")
    print()

    variant_summaries = []
    for variant_key, description, transform in VARIANTS:
        print(f"{variant_key}: {description}")
        print("-" * 72)
        traps = []
        skipped_cycle = 0
        skipped_good_tail = 0

        for phase, c0 in enumerate(cycle):
            s0 = transform(c0)
            analysis = explore_forced_orbit(s0, fs, good_cycle, good_configs)
            status = analysis["start_status"]
            if status == "good_cycle":
                skipped_cycle += 1
                print(
                    f"phase {phase:2d}: C0={c0} S0={s0} status=skip_good_cycle"
                )
                continue
            if status == "good_tail":
                skipped_good_tail += 1
                print(
                    f"phase {phase:2d}: C0={c0} S0={s0} status=skip_good_tail"
                )
                continue

            trap = "YES" if analysis["cycle_found"] else "NO"
            if analysis["cycle_found"]:
                traps.append((phase, analysis["cycle_length"], s0, analysis))
            print(
                "phase "
                f"{phase:2d}: C0={c0} S0={s0} status=bad "
                f"reachable_bad={analysis['reachable_bad']} "
                f"good_cycle_hits={analysis['good_cycle_hits']} "
                f"good_tail_hits={analysis['good_tail_hits']} "
                f"closed_bad_orbit={trap} "
                f"cycle_length={analysis['cycle_length']}"
            )
            if analysis["cycle_found"]:
                print(
                    f"          witness_moves={format_moves(analysis['cycle_moves'])} "
                    f"witness_cycle={analysis['cycle_configs']}"
                )

        cycle_lengths = sorted({length for _, length, _, _ in traps})
        variant_summaries.append(
            {
                "variant": variant_key,
                "description": description,
                "trap_count": len(traps),
                "trap_phases": [phase for phase, _, _, _ in traps],
                "cycle_lengths": cycle_lengths,
                "skipped_cycle": skipped_cycle,
                "skipped_good_tail": skipped_good_tail,
            }
        )
        print()
        print(
            f"summary {variant_key}: traps={len(traps)}/18 "
            f"trap_phases={ [phase for phase, _, _, _ in traps] } "
            f"cycle_lengths={cycle_lengths} "
            f"skipped_good_cycle={skipped_cycle} "
            f"skipped_good_tail={skipped_good_tail}"
        )
        print()

    print("Overall summary")
    print("-" * 72)
    for summary in variant_summaries:
        print(
            f"{summary['variant']}: trap_count={summary['trap_count']}/18 "
            f"trap_phases={summary['trap_phases']} "
            f"cycle_lengths={summary['cycle_lengths']} "
            f"skipped_good_cycle={summary['skipped_cycle']} "
            f"skipped_good_tail={summary['skipped_good_tail']}"
        )


if __name__ == "__main__":
    main()
