from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Callable, Iterable


Config = tuple[int, ...]
Context = tuple[int, int, int]
RuleTable = dict[Context, int]


@dataclass(frozen=True)
class CycleSummary:
    length: int
    processors: tuple[int, ...]


@dataclass(frozen=True)
class VerificationResult:
    valid: bool
    message: str
    cycle_summaries: tuple[CycleSummary, ...]
    configuration_count: int


@dataclass(frozen=True)
class RingSystem:
    state_counts: tuple[int, ...]
    rules: tuple[RuleTable, ...]

    def __post_init__(self) -> None:
        n = len(self.state_counts)
        if n == 0:
            raise ValueError("state_counts must be non-empty")
        if len(self.rules) != n:
            raise ValueError("rules must match the number of processors")
        for i, m in enumerate(self.state_counts):
            if m <= 0:
                raise ValueError("state counts must be positive")
            expected = self.state_counts[(i - 1) % n] * m * self.state_counts[(i + 1) % n]
            if len(self.rules[i]) != expected:
                raise ValueError(f"processor {i} rule table has {len(self.rules[i])} entries, expected {expected}")
            for (left, self_state, right), out_state in self.rules[i].items():
                if not (0 <= left < self.state_counts[(i - 1) % n]):
                    raise ValueError(f"invalid left state {left} in processor {i} rule")
                if not (0 <= self_state < m):
                    raise ValueError(f"invalid self state {self_state} in processor {i} rule")
                if not (0 <= right < self.state_counts[(i + 1) % n]):
                    raise ValueError(f"invalid right state {right} in processor {i} rule")
                if not (0 <= out_state < m):
                    raise ValueError(f"invalid output state {out_state} in processor {i} rule")

    @property
    def size(self) -> int:
        total = 1
        for m in self.state_counts:
            total *= m
        return total

    def iter_configs(self) -> Iterable[Config]:
        return product(*(range(m) for m in self.state_counts))

    def successor_for_processor(self, config: Config, processor: int) -> Config | None:
        left = config[(processor - 1) % len(self.state_counts)]
        self_state = config[processor]
        right = config[(processor + 1) % len(self.state_counts)]
        next_state = self.rules[processor][(left, self_state, right)]
        if next_state == self_state:
            return None
        updated = list(config)
        updated[processor] = next_state
        return tuple(updated)

    def successors(self, config: Config) -> list[tuple[int, Config]]:
        moves: list[tuple[int, Config]] = []
        for processor in range(len(self.state_counts)):
            nxt = self.successor_for_processor(config, processor)
            if nxt is not None:
                moves.append((processor, nxt))
        return moves


def materialize_rule(
    state_counts: tuple[int, ...],
    processor: int,
    rule_fn: Callable[[int, int, int], int],
) -> RuleTable:
    left_m = state_counts[(processor - 1) % len(state_counts)]
    self_m = state_counts[processor]
    right_m = state_counts[(processor + 1) % len(state_counts)]
    table: RuleTable = {}
    for left, self_state, right in product(range(left_m), range(self_m), range(right_m)):
        out_state = rule_fn(left, self_state, right)
        if not (0 <= out_state < self_m):
            raise ValueError(
                f"processor {processor} rule returned {out_state} for context {(left, self_state, right)}"
            )
        table[(left, self_state, right)] = out_state
    return table


def build_dijkstra_solution_1(n: int, m: int) -> RingSystem:
    if n < 2:
        raise ValueError("Dijkstra solution 1 requires n >= 2")
    if m < 2:
        raise ValueError("Dijkstra solution 1 requires m >= 2")
    state_counts = (m,) * n
    rules: list[RuleTable] = []
    rules.append(
        materialize_rule(
            state_counts,
            0,
            lambda left, self_state, right: (self_state + 1) % m if left == self_state else self_state,
        )
    )
    for processor in range(1, n):
        rules.append(
            materialize_rule(
                state_counts,
                processor,
                lambda left, self_state, right: left if left != self_state else self_state,
            )
        )
    return RingSystem(state_counts=state_counts, rules=tuple(rules))


def build_dijkstra_solution_3(n: int) -> RingSystem:
    if n < 3:
        raise ValueError("Dijkstra solution 3 requires n >= 3")
    state_counts = (3,) * n
    rules: list[RuleTable] = []
    rules.append(
        materialize_rule(
            state_counts,
            0,
            lambda left, self_state, right: (self_state - 1) % 3 if (self_state + 1) % 3 == right else self_state,
        )
    )
    for processor in range(1, n - 1):
        rules.append(
            materialize_rule(
                state_counts,
                processor,
                lambda left, self_state, right: (
                    left if (self_state + 1) % 3 == left else right if (self_state + 1) % 3 == right else self_state
                ),
            )
        )
    rules.append(
        materialize_rule(
            state_counts,
            n - 1,
            lambda left, self_state, right: (left + 1) % 3 if left == right and (left + 1) % 3 != self_state else self_state,
        )
    )
    return RingSystem(state_counts=state_counts, rules=tuple(rules))


def verify_system(system: RingSystem) -> VerificationResult:
    configs = list(system.iter_configs())
    index = {config: idx for idx, config in enumerate(configs)}
    successors: list[list[tuple[int, int]]] = []
    for config in configs:
        moves = []
        for processor, next_config in system.successors(config):
            moves.append((processor, index[next_config]))
        if not moves:
            return VerificationResult(
                valid=False,
                message=f"configuration {config} has no legal moves",
                cycle_summaries=(),
                configuration_count=len(configs),
            )
        successors.append(moves)

    sccs = _tarjan_scc(successors)
    cycle_summaries: list[CycleSummary] = []
    processor_count = len(system.state_counts)
    required_processors = set(range(processor_count))

    for scc in sccs:
        is_cyclic = len(scc) > 1 or any(dst == scc[0] for _, dst in successors[scc[0]])
        if not is_cyclic:
            continue

        for node in scc:
            if len(successors[node]) != 1:
                return VerificationResult(
                    valid=False,
                    message=(
                        "cyclic strongly connected component contains a branching configuration: "
                        f"{configs[node]}"
                    ),
                    cycle_summaries=tuple(cycle_summaries),
                    configuration_count=len(configs),
                )

        seen_processors = []
        seen_set = set()
        for node in scc:
            processor, dst = successors[node][0]
            if dst not in scc:
                return VerificationResult(
                    valid=False,
                    message=(
                        "cyclic strongly connected component is not closed under the unique good move: "
                        f"{configs[node]} -> {configs[dst]}"
                    ),
                    cycle_summaries=tuple(cycle_summaries),
                    configuration_count=len(configs),
                )
            seen_processors.append(processor)
            seen_set.add(processor)

        if seen_set != required_processors:
            missing = sorted(required_processors - seen_set)
            return VerificationResult(
                valid=False,
                message=(
                    "fairness fails on a recurrent cycle; missing processors "
                    f"{missing} in a cycle of length {len(scc)}"
                ),
                cycle_summaries=tuple(cycle_summaries),
                configuration_count=len(configs),
            )

        cycle_summaries.append(CycleSummary(length=len(scc), processors=tuple(seen_processors)))

    if not cycle_summaries:
        return VerificationResult(
            valid=False,
            message="the transition graph has no recurrent cycles, which is impossible in a finite live system",
            cycle_summaries=(),
            configuration_count=len(configs),
        )

    return VerificationResult(
        valid=True,
        message=f"valid system with {len(cycle_summaries)} recurrent cycle(s)",
        cycle_summaries=tuple(cycle_summaries),
        configuration_count=len(configs),
    )


def n5_easy_lower_bound() -> int:
    return 72


def n5_product_obstruction_summary() -> str:
    return (
        "For n = 5, every processor must have at least 2 states. "
        "Any product below 72 has at most one non-binary processor, so it necessarily has "
        "four consecutive 2-state processors, which the seminar notes rule out."
    )


def _tarjan_scc(successors: list[list[tuple[int, int]]]) -> list[list[int]]:
    index = 0
    stack: list[int] = []
    on_stack: set[int] = set()
    indices = [-1] * len(successors)
    lowlinks = [0] * len(successors)
    components: list[list[int]] = []

    def strongconnect(node: int) -> None:
        nonlocal index
        indices[node] = index
        lowlinks[node] = index
        index += 1
        stack.append(node)
        on_stack.add(node)

        for _, dst in successors[node]:
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

    for node in range(len(successors)):
        if indices[node] == -1:
            strongconnect(node)

    return components
