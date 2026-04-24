from __future__ import annotations

import argparse
import os
import sys
import time
from dataclasses import dataclass
from functools import lru_cache
from itertools import product

sys.path.insert(0, os.path.dirname(__file__))

from p2_ring import RingSystem, verify_system
from p2_good_cycle_search import local_context, search_good_cycle


Config = tuple[int, ...]
RuleKey = tuple[int, tuple[int, int, int]]
DomainMap = dict[RuleKey, frozenset[int]]


@dataclass(frozen=True)
class ScreeningData:
    configs: tuple[Config, ...]
    index: dict[Config, int]
    config_keys: tuple[tuple[RuleKey, ...], ...]


@dataclass
class SearchStats:
    nodes: int = 0
    backtracks: int = 0
    max_depth: int = 0


@dataclass(frozen=True)
class CompletionResult:
    found: bool
    message: str
    stats: SearchStats
    elapsed: float
    system: RingSystem | None


def all_keys(state_counts: tuple[int, ...]) -> list[RuleKey]:
    keys: list[RuleKey] = []
    n = len(state_counts)
    for processor in range(n):
        left_m = state_counts[(processor - 1) % n]
        self_m = state_counts[processor]
        right_m = state_counts[(processor + 1) % n]
        for ctx in product(range(left_m), range(self_m), range(right_m)):
            keys.append((processor, ctx))
    return keys


def cycle_rule_map_from_cycle(
    state_counts: tuple[int, ...],
    cycle: tuple[Config, ...],
    movers: tuple[int, ...],
) -> dict[RuleKey, int]:
    rule_map: dict[RuleKey, int] = {}
    extended = cycle[1:] + cycle[:1]
    for config, mover, nxt in zip(cycle, movers, extended, strict=True):
        for processor in range(len(state_counts)):
            key = (processor, local_context(config, processor))
            required = nxt[processor] if processor == mover else config[processor]
            existing = rule_map.get(key)
            if existing is not None and existing != required:
                raise ValueError("cycle construction produced inconsistent rule requirements")
            rule_map[key] = required
    return rule_map


def cycle_rule_map(state_counts: tuple[int, ...]) -> tuple[tuple[Config, ...], tuple[int, ...], dict[RuleKey, int]]:
    result = search_good_cycle(state_counts, time_limit=5)
    if result.cycle is None or result.movers is None:
        raise ValueError(f"no locally consistent good cycle available for {state_counts}")
    cycle = result.cycle
    movers = result.movers
    rule_map = cycle_rule_map_from_cycle(state_counts, cycle, movers)
    return cycle, movers, rule_map


def build_initial_domains_from_cycle(
    state_counts: tuple[int, ...],
    cycle: tuple[Config, ...],
    movers: tuple[int, ...],
) -> tuple[tuple[Config, ...], frozenset[Config], DomainMap]:
    forced = cycle_rule_map_from_cycle(state_counts, cycle, movers)
    domains: DomainMap = {}
    for key in all_keys(state_counts):
        processor, _ = key
        if key in forced:
            domains[key] = frozenset({forced[key]})
        else:
            domains[key] = frozenset(range(state_counts[processor]))
    return cycle, frozenset(cycle), domains


def build_initial_domains(state_counts: tuple[int, ...]) -> tuple[tuple[Config, ...], frozenset[Config], DomainMap]:
    cycle, movers, _ = cycle_rule_map(state_counts)
    _ = movers
    return build_initial_domains_from_cycle(state_counts, cycle, movers)


def iter_configs(state_counts: tuple[int, ...]) -> tuple[Config, ...]:
    return tuple(product(*(range(m) for m in state_counts)))


@lru_cache(maxsize=None)
def screening_data(state_counts: tuple[int, ...]) -> ScreeningData:
    configs = iter_configs(state_counts)
    index = {config: idx for idx, config in enumerate(configs)}
    config_keys = []
    for config in configs:
        keys = tuple((processor, local_context(config, processor)) for processor in range(len(state_counts)))
        config_keys.append(keys)
    return ScreeningData(configs=configs, index=index, config_keys=tuple(config_keys))


def propagate(
    state_counts: tuple[int, ...],
    cycle_set: frozenset[Config],
    configs: tuple[Config, ...],
    domains: DomainMap,
) -> DomainMap | None:
    changed = True
    current = domains
    while changed:
        changed = False
        updates: dict[RuleKey, frozenset[int]] = {}

        for config in configs:
            if config in cycle_set:
                continue

            maybe_movers: list[tuple[int, RuleKey, frozenset[int], int]] = []
            for processor in range(len(state_counts)):
                key = (processor, local_context(config, processor))
                domain = current[key]
                self_state = config[processor]
                if any(value != self_state for value in domain):
                    maybe_movers.append((processor, key, domain, self_state))

            if not maybe_movers:
                return None

            if len(maybe_movers) == 1:
                _, key, domain, self_state = maybe_movers[0]
                new_domain = frozenset(value for value in domain if value != self_state)
                if not new_domain:
                    return None
                if new_domain != domain:
                    updates[key] = new_domain

        if updates:
            next_domains = dict(current)
            for key, new_domain in updates.items():
                old_domain = next_domains[key]
                shrunk = old_domain & new_domain
                if not shrunk:
                    return None
                if shrunk != old_domain:
                    next_domains[key] = frozenset(shrunk)
                    changed = True
            current = next_domains

        if has_fatal_forced_cycle(state_counts, cycle_set, configs, current):
            return None

    return current


def has_fatal_forced_cycle(
    state_counts: tuple[int, ...],
    cycle_set: frozenset[Config],
    configs: tuple[Config, ...],
    domains: DomainMap,
) -> bool:
    index = {config: idx for idx, config in enumerate(configs)}
    forced_edges: list[list[tuple[int, int]]] = [[] for _ in configs]

    for idx, config in enumerate(configs):
        if config in cycle_set:
            continue
        for processor in range(len(state_counts)):
            key = (processor, local_context(config, processor))
            domain = domains[key]
            if len(domain) != 1:
                continue
            (out_state,) = tuple(domain)
            if out_state == config[processor]:
                continue
            nxt = list(config)
            nxt[processor] = out_state
            forced_edges[idx].append((processor, index[tuple(nxt)]))

    adjacency = [[dst for _, dst in edges if configs[dst] not in cycle_set] for edges in forced_edges]
    required_processors = set(range(len(state_counts)))

    for scc in tarjan_scc(adjacency):
        if len(scc) <= 1:
            continue
        scc_set = set(scc)
        seen_processors = set()
        for node in scc:
            internal_edges = [(processor, dst) for processor, dst in forced_edges[node] if dst in scc_set]
            if len(forced_edges[node]) != 1 or len(internal_edges) != 1:
                return True
            seen_processors.add(internal_edges[0][0])
        if seen_processors != required_processors:
            return True
    return False


def has_fatal_forced_cycle_singletons(
    state_counts: tuple[int, ...],
    exempt_set: frozenset[Config],
    forced_map: dict[RuleKey, int],
) -> bool:
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
    required_processors = set(range(len(state_counts)))

    for scc in tarjan_scc(adjacency):
        if len(scc) <= 1:
            continue
        scc_set = set(scc)
        seen_processors = set()
        for node in scc:
            internal_edges = [(processor, dst) for processor, dst in forced_edges[node] if dst in scc_set]
            if len(forced_edges[node]) != 1 or len(internal_edges) != 1:
                return True
            seen_processors.add(internal_edges[0][0])
        if seen_processors != required_processors:
            return True
    return False


def tarjan_scc(adjacency: list[list[int]]) -> list[list[int]]:
    index = 0
    indices = [-1] * len(adjacency)
    lowlinks = [0] * len(adjacency)
    stack: list[int] = []
    on_stack: set[int] = set()
    components: list[list[int]] = []

    def strongconnect(node: int) -> None:
        nonlocal index
        indices[node] = index
        lowlinks[node] = index
        index += 1
        stack.append(node)
        on_stack.add(node)

        for dst in adjacency[node]:
            if indices[dst] == -1:
                strongconnect(dst)
                lowlinks[node] = min(lowlinks[node], lowlinks[dst])
            elif dst in on_stack:
                lowlinks[node] = min(lowlinks[node], indices[dst])

        if lowlinks[node] != indices[node]:
            return

        component: list[int] = []
        while True:
            top = stack.pop()
            on_stack.remove(top)
            component.append(top)
            if top == node:
                break
        components.append(component)

    for node in range(len(adjacency)):
        if indices[node] == -1:
            strongconnect(node)

    return components


def choose_key(state_counts: tuple[int, ...], cycle_set: frozenset[Config], configs: tuple[Config, ...], domains: DomainMap) -> RuleKey | None:
    best_key = None
    best_score = None
    for key, domain in domains.items():
        if len(domain) == 1:
            continue
        processor, _ = key
        support = 0
        critical = 0
        for config in configs:
            if config in cycle_set:
                continue
            cfg_key = (processor, local_context(config, processor))
            if cfg_key != key:
                continue
            support += 1
            maybe_count = 0
            for j in range(len(state_counts)):
                other_key = (j, local_context(config, j))
                other_domain = domains[other_key]
                if any(value != config[j] for value in other_domain):
                    maybe_count += 1
            if maybe_count <= 2:
                critical += 1
        score = (critical, support, -len(domain))
        if best_score is None or score > best_score:
            best_score = score
            best_key = key
    return best_key


def build_system(state_counts: tuple[int, ...], domains: DomainMap) -> RingSystem:
    rules = []
    for processor in range(len(state_counts)):
        table = {}
        for key, domain in domains.items():
            if key[0] != processor:
                continue
            (value,) = tuple(domain)
            table[key[1]] = value
        rules.append(table)
    return RingSystem(state_counts=state_counts, rules=tuple(rules))


def search_completion(
    state_counts: tuple[int, ...],
    time_limit: float | None = None,
    cycle: tuple[Config, ...] | None = None,
    movers: tuple[int, ...] | None = None,
) -> CompletionResult:
    if cycle is None or movers is None:
        cycle, cycle_set, initial_domains = build_initial_domains(state_counts)
    else:
        cycle, cycle_set, initial_domains = build_initial_domains_from_cycle(state_counts, cycle, movers)
    configs = iter_configs(state_counts)
    stats = SearchStats()
    began = time.time()
    _ = cycle

    def dfs(domains: DomainMap, depth: int) -> RingSystem | None:
        if time_limit is not None and time.time() - began > time_limit:
            raise TimeoutError

        stats.nodes += 1
        stats.max_depth = max(stats.max_depth, depth)

        propagated = propagate(state_counts, cycle_set, configs, domains)
        if propagated is None:
            stats.backtracks += 1
            return None

        key = choose_key(state_counts, cycle_set, configs, propagated)
        if key is None:
            system = build_system(state_counts, propagated)
            result = verify_system(system)
            if result.valid:
                return system
            stats.backtracks += 1
            return None

        processor, context = key
        self_state = context[1]
        domain = propagated[key]
        ordered_values = sorted(domain, key=lambda value: (value == self_state, value))
        for value in ordered_values:
            next_domains = dict(propagated)
            next_domains[key] = frozenset({value})
            system = dfs(next_domains, depth + 1)
            if system is not None:
                return system

        stats.backtracks += 1
        return None

    try:
        system = dfs(initial_domains, 0)
    except TimeoutError:
        return CompletionResult(
            found=False,
            message="timed out before finding or excluding a completion",
            stats=stats,
            elapsed=time.time() - began,
            system=None,
        )

    if system is None:
        return CompletionResult(
            found=False,
            message="no completion found for the selected good cycle",
            stats=stats,
            elapsed=time.time() - began,
            system=None,
        )

    return CompletionResult(
        found=True,
        message="found a full valid system",
        stats=stats,
        elapsed=time.time() - began,
        system=system,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("state_counts", help="comma-separated state counts")
    parser.add_argument("--time-limit", type=float, default=None)
    args = parser.parse_args()

    state_counts = tuple(int(part) for part in args.state_counts.split(","))
    result = search_completion(state_counts, time_limit=args.time_limit)
    print(result.message)
    print(f"elapsed={result.elapsed:.3f}s nodes={result.stats.nodes} backtracks={result.stats.backtracks} max_depth={result.stats.max_depth}")
    if result.system is not None:
        verification = verify_system(result.system)
        print(verification.message)
        for processor, table in enumerate(result.system.rules):
            print(f"P{processor}:")
            for context in sorted(table):
                print(f"  {context} -> {table[context]}")


if __name__ == "__main__":
    main()
