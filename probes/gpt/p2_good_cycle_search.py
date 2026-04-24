from __future__ import annotations

import argparse
import time
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from typing import Callable


Config = tuple[int, ...]
RuleKey = tuple[int, tuple[int, int, int]]
RuleMap = dict[RuleKey, int]
Transition = tuple[int, Config, tuple[tuple[RuleKey, int], ...]]


@dataclass
class SearchStats:
    nodes: int = 0
    backtracks: int = 0
    max_depth: int = 0


@dataclass(frozen=True)
class SearchResult:
    cycle: tuple[Config, ...] | None
    movers: tuple[int, ...] | None
    stats: SearchStats
    elapsed: float
    message: str


def successors(state_counts: tuple[int, ...], config: Config) -> list[tuple[int, Config]]:
    out: list[tuple[int, Config]] = []
    for i, m in enumerate(state_counts):
        current = config[i]
        for new_state in range(m):
            if new_state == current:
                continue
            nxt = list(config)
            nxt[i] = new_state
            out.append((i, tuple(nxt)))
    return out


@lru_cache(maxsize=None)
def transition_cache(state_counts: tuple[int, ...]) -> dict[Config, tuple[Transition, ...]]:
    transitions: dict[Config, tuple[Transition, ...]] = {}
    n = len(state_counts)
    configs = tuple(product(*(range(m) for m in state_counts)))
    for config in configs:
        options: list[Transition] = []
        for processor, m in enumerate(state_counts):
            current = config[processor]
            for new_state in range(m):
                if new_state == current:
                    continue
                nxt = list(config)
                nxt[processor] = new_state
                assignments = []
                for j in range(n):
                    key = (j, local_context(config, j))
                    required = new_state if j == processor else config[j]
                    assignments.append((key, required))
                options.append((processor, tuple(nxt), tuple(assignments)))
        options.sort(key=lambda item: item[0])
        transitions[config] = tuple(options)
    return transitions


def update_used_masks(used_masks: tuple[int, ...], processor: int, new_state: int) -> tuple[int, ...] | None:
    mask = used_masks[processor]
    bit = 1 << new_state
    if mask & bit:
        return used_masks
    if new_state != mask.bit_count():
        return None
    updated = list(used_masks)
    updated[processor] = mask | bit
    return tuple(updated)


def local_context(config: Config, processor: int) -> tuple[int, int, int]:
    n = len(config)
    return (config[(processor - 1) % n], config[processor], config[(processor + 1) % n])


def consistent_extension(rule_map: RuleMap, assignments: tuple[tuple[RuleKey, int], ...]) -> RuleMap | None:
    pending: list[tuple[RuleKey, int]] = []
    for key, required in assignments:
        existing = rule_map.get(key)
        if existing is None:
            pending.append((key, required))
            continue
        if existing != required:
            return None
    if not pending:
        return rule_map
    updated = dict(rule_map)
    for key, required in pending:
        updated[key] = required
    return updated


def search_good_cycle(
    state_counts: tuple[int, ...],
    max_depth: int | None = None,
    time_limit: float | None = None,
    prune_fn: Callable[[tuple[Config, ...], RuleMap], bool] | None = None,
) -> SearchResult:
    start = tuple(0 for _ in state_counts)
    visited = {start}
    path = [start]
    movers: list[int] = []
    stats = SearchStats()
    began = time.time()

    if max_depth is None:
        max_depth = 1
        for m in state_counts:
            max_depth *= m

    initial_used_masks = tuple(1 for _ in state_counts)
    transitions = transition_cache(state_counts)

    def dfs(
        current: Config,
        rule_map: RuleMap,
        moved_mask: int,
        used_masks: tuple[int, ...],
    ) -> tuple[tuple[Config, ...], tuple[int, ...]] | None:
        if time_limit is not None and time.time() - began > time_limit:
            raise TimeoutError

        stats.nodes += 1
        stats.max_depth = max(stats.max_depth, len(path))

        remaining_processors = len(state_counts) - moved_mask.bit_count()
        remaining_steps = max_depth - (len(path) - 1)
        if remaining_steps < remaining_processors:
            stats.backtracks += 1
            return None

        for processor, nxt, assignments in transitions[current]:
            next_used_masks = update_used_masks(used_masks, processor, nxt[processor])
            if next_used_masks is None:
                continue
            updated_rules = consistent_extension(rule_map, assignments)
            if updated_rules is None:
                continue
            if prune_fn is not None and prune_fn(tuple(path + [nxt]), updated_rules):
                stats.backtracks += 1
                continue

            new_mask = moved_mask | (1 << processor)
            if nxt == start:
                if len(path) >= len(state_counts) and new_mask.bit_count() == len(state_counts):
                    return tuple(path), tuple(movers + [processor])
                continue

            if len(path) >= max_depth or nxt in visited:
                continue

            visited.add(nxt)
            path.append(nxt)
            movers.append(processor)
            result = dfs(nxt, updated_rules, new_mask, next_used_masks)
            if result is not None:
                return result
            movers.pop()
            path.pop()
            visited.remove(nxt)

        stats.backtracks += 1
        return None

    try:
        found = dfs(start, {}, 0, initial_used_masks)
    except TimeoutError:
        return SearchResult(
            cycle=None,
            movers=None,
            stats=stats,
            elapsed=time.time() - began,
            message="timed out before proving existence or nonexistence",
        )

    if found is None:
        return SearchResult(
            cycle=None,
            movers=None,
            stats=stats,
            elapsed=time.time() - began,
            message="no locally consistent good cycle found",
        )

    cycle, cycle_movers = found
    return SearchResult(
        cycle=cycle,
        movers=cycle_movers,
        stats=stats,
        elapsed=time.time() - began,
        message=f"found locally consistent good cycle of length {len(cycle)}",
    )


def enumerate_good_cycles(
    state_counts: tuple[int, ...],
    max_depth: int | None = None,
    time_limit: float | None = None,
    max_cycles: int | None = None,
    prune_fn: Callable[[tuple[Config, ...], RuleMap], bool] | None = None,
):
    start = tuple(0 for _ in state_counts)
    visited = {start}
    path = [start]
    movers: list[int] = []
    began = time.time()
    yielded = 0

    if max_depth is None:
        max_depth = 1
        for m in state_counts:
            max_depth *= m

    initial_used_masks = tuple(1 for _ in state_counts)
    transitions = transition_cache(state_counts)

    def dfs(current: Config, rule_map: RuleMap, moved_mask: int, used_masks: tuple[int, ...]):
        nonlocal yielded
        if time_limit is not None and time.time() - began > time_limit:
            raise TimeoutError
        if max_cycles is not None and yielded >= max_cycles:
            return

        remaining_processors = len(state_counts) - moved_mask.bit_count()
        remaining_steps = max_depth - (len(path) - 1)
        if remaining_steps < remaining_processors:
            return

        for processor, nxt, assignments in transitions[current]:
            next_used_masks = update_used_masks(used_masks, processor, nxt[processor])
            if next_used_masks is None:
                continue
            updated_rules = consistent_extension(rule_map, assignments)
            if updated_rules is None:
                continue
            if prune_fn is not None and prune_fn(tuple(path + [nxt]), updated_rules):
                continue

            new_mask = moved_mask | (1 << processor)
            if nxt == start:
                if len(path) >= len(state_counts) and new_mask.bit_count() == len(state_counts):
                    yielded += 1
                    yield tuple(path), tuple(movers + [processor])
                    if max_cycles is not None and yielded >= max_cycles:
                        return
                continue

            if len(path) >= max_depth or nxt in visited:
                continue

            visited.add(nxt)
            path.append(nxt)
            movers.append(processor)
            yield from dfs(nxt, updated_rules, new_mask, next_used_masks)
            movers.pop()
            path.pop()
            visited.remove(nxt)

    try:
        yield from dfs(start, {}, 0, initial_used_masks)
    except TimeoutError:
        return


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("state_counts", help="comma-separated state counts")
    parser.add_argument("--time-limit", type=float, default=None)
    parser.add_argument("--max-depth", type=int, default=None)
    args = parser.parse_args()

    state_counts = tuple(int(part) for part in args.state_counts.split(","))
    result = search_good_cycle(state_counts, max_depth=args.max_depth, time_limit=args.time_limit)
    print(result.message)
    print(f"elapsed={result.elapsed:.3f}s nodes={result.stats.nodes} backtracks={result.stats.backtracks} max_depth={result.stats.max_depth}")
    if result.cycle is not None and result.movers is not None:
        print("cycle:")
        for config, mover in zip(result.cycle, result.movers, strict=True):
            print(f"  {config} --P{mover}-->")
        print(f"  {result.cycle[0]}")


if __name__ == "__main__":
    main()
