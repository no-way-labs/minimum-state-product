#!/usr/bin/env python3
"""Minimize completion-side singleton rules to a fatal fragment."""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from scripts.glb_three_sweep_scan import generate_words
from scripts.p2_completion_search import (
    build_initial_domains_from_cycle,
    has_fatal_forced_cycle_singletons,
    screening_data,
    tarjan_scc,
)
from scripts.p2_good_cycle_search import local_context
from scripts.p2_seeded_cycle_search import solve_good_cycle_from_movers
from scripts.p2_smt_completion import solve_cycle_with_smt


def parse_int_tuple(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def minimize_fatal_fragment(
    state_counts: tuple[int, ...],
    cycle_set: frozenset[tuple[int, ...]],
    forced_map: dict[tuple[int, tuple[int, int, int]], int],
) -> dict[tuple[int, tuple[int, int, int]], int]:
    kept = dict(forced_map)
    changed = True
    while changed:
        changed = False
        for key in list(kept):
            trial = dict(kept)
            trial.pop(key)
            if has_fatal_forced_cycle_singletons(state_counts, cycle_set, trial):
                kept = trial
                changed = True
    return kept


def fatal_scc_summary_from_forced(
    state_counts: tuple[int, ...],
    exempt_set: frozenset[tuple[int, ...]],
    forced_map: dict[tuple[int, tuple[int, int, int]], int],
) -> dict[str, object] | None:
    data = screening_data(state_counts)
    forced_edges: list[list[tuple[int, int]]] = [[] for _ in data.configs]

    for idx, config in enumerate(data.configs):
        if config in exempt_set:
            continue
        for processor, key in enumerate(data.config_keys[idx]):
            out_state = forced_map.get(key)
            if out_state is None or out_state == config[processor]:
                continue
            nxt = list(config)
            nxt[processor] = out_state
            forced_edges[idx].append((processor, data.index[tuple(nxt)]))

    adjacency = [[dst for _, dst in edges if data.configs[dst] not in exempt_set] for edges in forced_edges]
    required = set(range(len(state_counts)))

    for scc in tarjan_scc(adjacency):
        if len(scc) <= 1:
            continue
        scc_set = set(scc)
        seen = set()
        for node in scc:
            internal = [(p, d) for p, d in forced_edges[node] if d in scc_set]
            if len(forced_edges[node]) != 1 or len(internal) != 1:
                bad = True
                break
            seen.add(internal[0][0])
        else:
            bad = False
        if not bad and seen == required:
            continue

        return {
            "scc_size": len(scc),
            "all_binary": all(all(value in (0, 1) for value in data.configs[node]) for node in scc),
            "outdegree_hist": dict(sorted(Counter(len(forced_edges[node]) for node in scc).items())),
            "internal_mover_hist": dict(
                sorted(
                    Counter(
                        processor
                        for node in scc
                        for processor, dst in forced_edges[node]
                        if dst in scc_set
                    ).items()
                )
            ),
            "value_sets": [
                sorted({data.configs[node][processor] for node in scc})
                for processor in range(len(state_counts))
            ],
            "sample": [data.configs[node] for node in scc[:10]],
        }
    return None


def summarize_word(state_counts: tuple[int, ...], movers: tuple[int, ...], timeout_ms: int) -> None:
    cycle = solve_good_cycle_from_movers(state_counts, movers, timeout_ms=timeout_ms)
    print(f"cycle_found={cycle.found} message={cycle.message}")
    if not cycle.found or cycle.cycle is None:
        return

    completion = solve_cycle_with_smt(state_counts, cycle.cycle, movers, timeout_ms=max(10000, timeout_ms))
    print(f"completion_found={completion.found} message={completion.message}")
    if completion.found:
        return

    _, cycle_set, domains = build_initial_domains_from_cycle(state_counts, cycle.cycle, movers)
    forced_map = {key: next(iter(domain)) for key, domain in domains.items() if len(domain) == 1}
    print(f"full_forced_size={len(forced_map)}")

    fragment = minimize_fatal_fragment(state_counts, cycle_set, forced_map)
    print(f"minimal_fragment_size={len(fragment)}")
    for processor in range(len(state_counts)):
        entries = sorted((ctx, value) for (p, ctx), value in fragment.items() if p == processor)
        if entries:
            print(f"processor_{processor}={entries}")

    summary = fatal_scc_summary_from_forced(state_counts, cycle_set, fragment)
    print(f"fragment_scc={summary}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--state-counts", default="2,3,2,3,3,2,3,3,4")
    parser.add_argument("--movers")
    parser.add_argument("--kernel", choices=("reverse", "forward"))
    parser.add_argument("--index", type=int)
    parser.add_argument("--timeout-ms", type=int, default=1500)
    args = parser.parse_args()

    if args.movers:
        movers = parse_int_tuple(args.movers)
    else:
        if args.kernel is None or args.index is None:
            raise SystemExit("pass either --movers or both --kernel and --index")
        kernel_words = {
            "reverse": generate_words((1, 4), "reverse", "tail08"),
            "forward": generate_words((2, 5), "forward", "tail01"),
        }
        movers = kernel_words[args.kernel][args.index - 1]

    summarize_word(parse_int_tuple(args.state_counts), movers, args.timeout_ms)


if __name__ == "__main__":
    main()
