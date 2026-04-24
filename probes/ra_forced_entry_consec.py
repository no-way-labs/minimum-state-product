#!/usr/bin/env python3
"""Forced-entry shadow analysis for the M_5 witness with 3 consecutive binary."""

from __future__ import annotations

import json
from collections import deque
from functools import lru_cache
from pathlib import Path
from typing import Any

from ra_shadow_m5 import MS, START_CONFIG, build_m5_96_witness, rotate_cycle
from verifier import apply_move, privileged_set, verify_system


RESULTS_PATH = Path("ra_forced_entry_consec_results.json")


def product(values: tuple[int, ...] | list[int]) -> int:
    result = 1
    for value in values:
        result *= value
    return result


def local_context(config: tuple[int, ...], proc: int, n: int) -> tuple[int, int, int]:
    return (config[(proc - 1) % n], config[proc], config[(proc + 1) % n])


def shift_config(config: tuple[int, ...], proc: int, delta: int, ms: tuple[int, ...]) -> tuple[int, ...]:
    shifted = list(config)
    shifted[proc] = (shifted[proc] + delta) % ms[proc]
    return tuple(shifted)


def config_list(config: tuple[int, ...]) -> list[int]:
    return list(config)


def build_forced_entry_data(
    cycle: list[tuple[int, ...]],
    fs: list,
    ms: tuple[int, ...],
) -> tuple[list[dict[str, Any]], dict[tuple[int, tuple[int, int, int]], dict[str, Any]], list[dict[str, Any]]]:
    n = len(ms)
    step_entries: list[dict[str, Any]] = []
    entry_map: dict[tuple[int, tuple[int, int, int]], dict[str, Any]] = {}

    for step, config in enumerate(cycle):
        privileged = privileged_set(config, fs, list(ms))
        if len(privileged) != 1:
            raise ValueError(f"cycle step {step} has {len(privileged)} privileged processors, expected 1")

        proc = privileged[0]
        context = local_context(config, proc, n)
        next_config = cycle[(step + 1) % len(cycle)]
        computed_next = apply_move(config, proc, fs, list(ms))
        if computed_next != next_config:
            raise ValueError(f"cycle closure mismatch at step {step}: {computed_next} != {next_config}")

        output_state = next_config[proc]
        record = {
            "step": step,
            "config": config_list(config),
            "proc": proc,
            "context": list(context),
            "output_state": output_state,
            "next_config": config_list(next_config),
        }
        step_entries.append(record)

        key = (proc, context)
        slot = entry_map.setdefault(
            key,
            {
                "proc": proc,
                "context": list(context),
                "output_state": output_state,
                "steps": [],
            },
        )
        if slot["output_state"] != output_state:
            raise ValueError(
                f"inconsistent forced entry for proc {proc}, context {context}: "
                f"{slot['output_state']} vs {output_state}"
            )
        slot["steps"].append(step)

    duplicates = [value for value in entry_map.values() if len(value["steps"]) > 1]
    return step_entries, entry_map, duplicates


def matching_moves(
    config: tuple[int, ...],
    entry_map: dict[tuple[int, tuple[int, int, int]], dict[str, Any]],
    fs: list,
    ms: tuple[int, ...],
) -> tuple[list[int], list[dict[str, Any]]]:
    n = len(ms)
    privileged = privileged_set(config, fs, list(ms))
    matches: list[dict[str, Any]] = []

    for proc in privileged:
        context = local_context(config, proc, n)
        key = (proc, context)
        if key not in entry_map:
            continue
        next_config = apply_move(config, proc, fs, list(ms))
        forced = entry_map[key]
        matches.append(
            {
                "proc": proc,
                "context": list(context),
                "output_state": forced["output_state"],
                "next_config": config_list(next_config),
                "cycle_steps": list(forced["steps"]),
            }
        )
    return privileged, matches


def shortest_return_length(
    start: tuple[int, ...],
    edge_map: dict[tuple[int, ...], list[dict[str, Any]]],
) -> int | None:
    queue: deque[tuple[tuple[int, ...], int]] = deque()
    seen: set[tuple[int, ...]] = {start}

    for edge in edge_map[start]:
        next_config = tuple(edge["next_config"])
        if next_config == start:
            return 1
        queue.append((next_config, 1))
        seen.add(next_config)

    while queue:
        config, dist = queue.popleft()
        for edge in edge_map.get(config, []):
            next_config = tuple(edge["next_config"])
            if next_config == start:
                return dist + 1
            if next_config in seen:
                continue
            seen.add(next_config)
            queue.append((next_config, dist + 1))
    return None


def has_cycle(edge_map: dict[tuple[int, ...], list[dict[str, Any]]]) -> bool:
    color: dict[tuple[int, ...], int] = {}

    def dfs(config: tuple[int, ...]) -> bool:
        color[config] = 1
        for edge in edge_map[config]:
            next_config = tuple(edge["next_config"])
            state = color.get(next_config, 0)
            if state == 1:
                return True
            if state == 0 and dfs(next_config):
                return True
        color[config] = 2
        return False

    for config in edge_map:
        if color.get(config, 0) == 0 and dfs(config):
            return True
    return False


def acyclic_path_summary(
    start: tuple[int, ...],
    edge_map: dict[tuple[int, ...], list[dict[str, Any]]],
    cycle_set: set[tuple[int, ...]],
) -> dict[str, Any]:
    @lru_cache(maxsize=None)
    def solve(config: tuple[int, ...]) -> dict[str, Any]:
        edges = edge_map[config]
        if not edges:
            return {
                "path_count": 1,
                "min_terminal_depth": 0,
                "max_terminal_depth": 0,
                "hits_good_cycle": config in cycle_set,
                "terminal_configs": [config],
            }

        path_count = 0
        min_depth: int | None = None
        max_depth = 0
        hits_good_cycle = config in cycle_set
        terminal_configs: set[tuple[int, ...]] = set()

        for edge in edges:
            next_config = tuple(edge["next_config"])
            child = solve(next_config)
            path_count += child["path_count"]
            child_min = child["min_terminal_depth"] + 1
            child_max = child["max_terminal_depth"] + 1
            min_depth = child_min if min_depth is None else min(min_depth, child_min)
            max_depth = max(max_depth, child_max)
            hits_good_cycle = hits_good_cycle or child["hits_good_cycle"]
            terminal_configs.update(child["terminal_configs"])

        return {
            "path_count": path_count,
            "min_terminal_depth": min_depth,
            "max_terminal_depth": max_depth,
            "hits_good_cycle": hits_good_cycle,
            "terminal_configs": sorted(terminal_configs),
        }

    summary = solve(start)
    return {
        "path_count": summary["path_count"],
        "min_terminal_depth": summary["min_terminal_depth"],
        "max_terminal_depth": summary["max_terminal_depth"],
        "hits_good_cycle": summary["hits_good_cycle"],
        "terminal_configs": [config_list(config) for config in summary["terminal_configs"]],
    }


def unique_prefix_trace(
    start: tuple[int, ...],
    entry_map: dict[tuple[int, tuple[int, int, int]], dict[str, Any]],
    fs: list,
    ms: tuple[int, ...],
    cycle_set: set[tuple[int, ...]],
) -> list[dict[str, Any]]:
    seen: dict[tuple[int, ...], int] = {}
    trace: list[dict[str, Any]] = []
    config = start

    while True:
        privileged, matches = matching_moves(config, entry_map, fs, ms)
        step = len(trace)
        row = {
            "step": step,
            "config": config_list(config),
            "in_good_cycle": config in cycle_set,
            "privileged": list(privileged),
            "match_count": len(matches),
            "matches": matches,
        }
        trace.append(row)

        if config in seen:
            row["event"] = "revisit"
            row["revisit_step"] = seen[config]
            break
        seen[config] = step

        if len(matches) == 0:
            row["event"] = "stuck"
            break
        if len(matches) > 1:
            row["event"] = "branch"
            break

        row["event"] = "advance"
        config = tuple(matches[0]["next_config"])

    return trace


def classify_case(
    start: tuple[int, ...],
    graph_info: dict[str, Any],
) -> str:
    if graph_info["return_to_start_length"] is not None and graph_info["all_bad_reachable"]:
        return "closed_all_bad_orbit"
    if graph_info["return_to_start_length"] is not None:
        return "returns_to_start_via_good_cycle"
    if graph_info["has_cycle"]:
        return "reaches_cycle_without_returning_to_start"
    if graph_info["all_bad_reachable"] and graph_info["has_terminal"]:
        return "all_bad_acyclic_and_stuck"
    if start in graph_info["good_cycle_configs"]:
        return "starts_in_good_cycle_without_return"
    return "other"


def analyze_start(
    base_config: tuple[int, ...],
    proc: int,
    delta: int,
    entry_map: dict[tuple[int, tuple[int, int, int]], dict[str, Any]],
    fs: list,
    ms: tuple[int, ...],
    cycle_set: set[tuple[int, ...]],
) -> dict[str, Any]:
    start = shift_config(base_config, proc, delta, ms)
    queue: deque[tuple[int, ...]] = deque([start])
    seen: set[tuple[int, ...]] = {start}
    distance = {start: 0}
    node_info: dict[tuple[int, ...], dict[str, Any]] = {}
    edge_map: dict[tuple[int, ...], list[dict[str, Any]]] = {}

    while queue:
        config = queue.popleft()
        privileged, matches = matching_moves(config, entry_map, fs, ms)
        node_info[config] = {
            "config": config_list(config),
            "distance": distance[config],
            "privileged": list(privileged),
            "match_count": len(matches),
            "matches": matches,
            "in_good_cycle": config in cycle_set,
        }
        edge_map[config] = matches

        for match in matches:
            next_config = tuple(match["next_config"])
            if next_config in seen:
                continue
            seen.add(next_config)
            distance[next_config] = distance[config] + 1
            queue.append(next_config)

    branch_nodes = [node for node, info in node_info.items() if info["match_count"] > 1]
    terminal_nodes = [node for node, info in node_info.items() if info["match_count"] == 0]
    good_cycle_nodes = sorted(node for node, info in node_info.items() if info["in_good_cycle"])
    first_branch_depth = min((distance[node] for node in branch_nodes), default=None)
    first_terminal_depth = min((distance[node] for node in terminal_nodes), default=None)
    shortest_good_cycle_depth = min((distance[node] for node in good_cycle_nodes), default=None)
    cycle_present = has_cycle(edge_map)
    return_to_start = shortest_return_length(start, edge_map)

    graph_info: dict[str, Any] = {
        "start_config": config_list(start),
        "start_in_good_cycle": start in cycle_set,
        "reachable_count": len(node_info),
        "edge_count": sum(len(edges) for edges in edge_map.values()),
        "has_cycle": cycle_present,
        "return_to_start_length": return_to_start,
        "all_bad_reachable": not good_cycle_nodes,
        "good_cycle_configs": [config_list(node) for node in good_cycle_nodes],
        "shortest_good_cycle_depth": shortest_good_cycle_depth,
        "branch_count": len(branch_nodes),
        "first_branch_depth": first_branch_depth,
        "terminal_count": len(terminal_nodes),
        "first_terminal_depth": first_terminal_depth,
        "has_terminal": bool(terminal_nodes),
        "terminal_configs": [config_list(node) for node in sorted(terminal_nodes)],
        "nodes": [node_info[node] for node in sorted(node_info)],
        "trace_until_nonunique": unique_prefix_trace(start, entry_map, fs, ms, cycle_set),
    }

    if not cycle_present:
        graph_info["acyclic_path_summary"] = acyclic_path_summary(start, edge_map, cycle_set)

    graph_info["classification"] = classify_case(start, graph_info)
    return graph_info


def compact_case_summary(case: dict[str, Any]) -> str:
    return (
        f"q={case['proc']} shift={case['shift_label']:>2} S0={tuple(case['start_config'])} "
        f"class={case['classification']} "
        f"close={case['return_to_start_length']} "
        f"good={case['shortest_good_cycle_depth']} "
        f"branch={case['first_branch_depth']} "
        f"zero_match={case['first_terminal_depth']}"
    )


def all_phase_sweep(
    cycle: list[tuple[int, ...]],
    entry_map: dict[tuple[int, tuple[int, int, int]], dict[str, Any]],
    fs: list,
    ms: tuple[int, ...],
    cycle_set: set[tuple[int, ...]],
) -> dict[str, Any]:
    counts: dict[str, int] = {}
    by_proc_shift: dict[str, dict[str, int]] = {}
    closed_all_bad_cases: list[dict[str, Any]] = []

    for cycle_index, base_config in enumerate(cycle):
        for proc in range(len(ms)):
            for delta in (+1, -1):
                result = analyze_start(base_config, proc, delta, entry_map, fs, ms, cycle_set)
                classification = result["classification"]
                counts[classification] = counts.get(classification, 0) + 1

                key = f"q{proc}_{'plus1' if delta == 1 else 'minus1'}"
                bucket = by_proc_shift.setdefault(key, {})
                bucket[classification] = bucket.get(classification, 0) + 1

                if classification == "closed_all_bad_orbit":
                    closed_all_bad_cases.append(
                        {
                            "cycle_index": cycle_index,
                            "base_config": config_list(base_config),
                            "proc": proc,
                            "delta": delta,
                            "start_config": result["start_config"],
                            "return_to_start_length": result["return_to_start_length"],
                        }
                    )

    return {
        "num_cycle_phases": len(cycle),
        "total_cases": len(cycle) * len(ms) * 2,
        "classification_counts": counts,
        "by_proc_shift": by_proc_shift,
        "closed_all_bad_cases": closed_all_bad_cases,
    }


def main() -> None:
    ms = tuple(MS)
    tables, fs = build_m5_96_witness()
    result = verify_system(list(ms), fs, verbose=False)
    if not result["valid"]:
        raise SystemExit("M_5 witness is not valid; aborting.")

    cycle = rotate_cycle(list(result["cycle"]), START_CONFIG)
    cycle_set = set(cycle)
    step_entries, entry_map, duplicates = build_forced_entry_data(cycle, fs, ms)

    base_cases = []
    for proc in range(len(ms)):
        for delta in (+1, -1):
            graph_info = analyze_start(START_CONFIG, proc, delta, entry_map, fs, ms, cycle_set)
            base_cases.append(
                {
                    "proc": proc,
                    "delta": delta,
                    "shift_label": "+1" if delta == 1 else "-1",
                    **graph_info,
                }
            )

    phase_sweep = all_phase_sweep(cycle, entry_map, fs, ms, cycle_set)

    payload = {
        "ms": list(ms),
        "product": product(ms),
        "good_cycle_length": len(cycle),
        "good_config_count": len(result["good_configs"]),
        "start_config": config_list(START_CONFIG),
        "good_cycle": [config_list(config) for config in cycle],
        "forced_entry_steps": step_entries,
        "unique_forced_entry_count": len(entry_map),
        "duplicate_forced_entries": duplicates,
        "base_config_results": base_cases,
        "all_phase_sweep": phase_sweep,
    }
    RESULTS_PATH.write_text(json.dumps(payload, indent=2))

    print("Forced-entry analysis on the M_5 witness")
    print("=" * 72)
    print(f"ms = {list(ms)}")
    print(f"product = {product(ms)}")
    print(f"verify_system.good_configs = {len(result['good_configs'])}")
    print(f"good cycle length = {len(cycle)}")
    print(f"C_0 = {START_CONFIG}")
    print()
    print("Forced-entry table from the rotated good cycle:")
    for entry in step_entries:
        print(
            f"  step {entry['step']:2d}: P{entry['proc']} "
            f"context={tuple(entry['context'])} -> {entry['output_state']} "
            f"config={tuple(entry['config'])}"
        )
    print()
    print(
        f"Unique mover entries = {len(entry_map)}; "
        f"duplicates = {len(duplicates)}"
    )
    for item in duplicates:
        print(
            f"  duplicate: P{item['proc']} context={tuple(item['context'])} "
            f"-> {item['output_state']} at good-cycle steps {item['steps']}"
        )
    print()
    print("Base-config results (shifting C_0 only):")
    for case in base_cases:
        print(f"  {compact_case_summary(case)}")
        trace = case["trace_until_nonunique"]
        last = trace[-1]
        print(
            f"    first event={last['event']} at step {last['step']}; "
            f"match_count={last['match_count']}; in_good_cycle={last['in_good_cycle']}"
        )
        if "acyclic_path_summary" in case:
            aps = case["acyclic_path_summary"]
            print(
                f"    DAG paths={aps['path_count']} "
                f"terminal_depths={aps['min_terminal_depth']}..{aps['max_terminal_depth']} "
                f"hits_good_cycle={aps['hits_good_cycle']}"
            )
    print()
    print("All-phase sweep summary:")
    print(f"  total cases = {phase_sweep['total_cases']}")
    for key, value in sorted(phase_sweep["classification_counts"].items()):
        print(f"  {key}: {value}")
    print(
        f"  closed all-bad cases: {len(phase_sweep['closed_all_bad_cases'])}"
    )
    print()
    print(f"Full JSON written to {RESULTS_PATH}")


if __name__ == "__main__":
    main()
