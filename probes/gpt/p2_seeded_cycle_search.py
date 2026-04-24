from __future__ import annotations

import argparse
import os
import sys
import time
from dataclasses import dataclass

import z3

sys.path.append(os.path.dirname(os.path.dirname(__file__)))

from p2_ring import Config, RingSystem
from p2_witnesses import (
    build_n5_product_96_witness,
    build_n6_product_288_block_witness,
    build_n6_product_288_witness,
    build_n7_product_864_witness,
    build_n7_product_1152_witness,
)
from scripts.p2_smt_completion import solve_cycle_with_smt


@dataclass(frozen=True)
class SeededCycleResult:
    found: bool
    message: str
    cycle: tuple[Config, ...] | None
    elapsed: float


def extract_unique_recurrent_cycle(system: RingSystem) -> tuple[tuple[Config, ...], tuple[int, ...]]:
    configs = list(system.iter_configs())
    index = {config: idx for idx, config in enumerate(configs)}
    successors: list[list[tuple[int, int]]] = []
    for config in configs:
        moves = []
        for processor, next_config in system.successors(config):
            moves.append((processor, index[next_config]))
        successors.append(moves)

    sccs = _tarjan_scc(successors)
    cycles: list[list[int]] = []
    for scc in sccs:
        if len(scc) <= 1:
            continue
        if all(len(successors[node]) == 1 and successors[node][0][1] in scc for node in scc):
            cycles.append(scc)

    if len(cycles) != 1:
        raise ValueError(f"expected exactly one recurrent cycle, found {len(cycles)}")

    start = cycles[0][0]
    seen: set[int] = set()
    cycle: list[Config] = []
    movers: list[int] = []
    current = start
    while current not in seen:
        seen.add(current)
        cycle.append(configs[current])
        movers.append(successors[current][0][0])
        current = successors[current][0][1]
    return tuple(cycle), tuple(movers)


def solve_good_cycle_from_movers(
    state_counts: tuple[int, ...],
    movers: tuple[int, ...],
    timeout_ms: int | None = None,
) -> SeededCycleResult:
    began = time.time()
    solver = z3.Solver()
    if timeout_ms is not None:
        solver.set("timeout", timeout_ms)
    config_vars = _build_seeded_cycle_constraints(solver, state_counts, movers)
    return _finish_seeded_cycle_result(began, solver, config_vars, state_counts)


def solve_good_cycle_from_movers_lexmin(
    state_counts: tuple[int, ...],
    movers: tuple[int, ...],
    timeout_ms: int | None = None,
) -> SeededCycleResult:
    began = time.time()
    optimizer = z3.Optimize()
    if timeout_ms is not None:
        optimizer.set("timeout", timeout_ms)
    config_vars = _build_seeded_cycle_constraints(optimizer, state_counts, movers)
    for row in config_vars:
        for variable in row:
            optimizer.minimize(variable)
    return _finish_seeded_cycle_result(began, optimizer, config_vars, state_counts)


def _build_seeded_cycle_constraints(
    solver: z3.Solver | z3.Optimize,
    state_counts: tuple[int, ...],
    movers: tuple[int, ...],
) -> list[list[z3.ArithRef]]:
    length = len(movers)
    config_vars = [[z3.Int(f"c_{t}_{i}") for i in range(len(state_counts))] for t in range(length)]

    for t in range(length):
        for i, state_count in enumerate(state_counts):
            solver.add(config_vars[t][i] >= 0)
            solver.add(config_vars[t][i] < state_count)

    # Anchor the cycle at the all-zero configuration to quotient a large symmetry.
    for i in range(len(state_counts)):
        solver.add(config_vars[0][i] == 0)

    for t, mover in enumerate(movers):
        nxt = (t + 1) % length
        for i in range(len(state_counts)):
            if i != mover:
                solver.add(config_vars[nxt][i] == config_vars[t][i])
        solver.add(config_vars[nxt][mover] != config_vars[t][mover])

    for t in range(length):
        for u in range(t + 1, length):
            solver.add(z3.Or([config_vars[t][i] != config_vars[u][i] for i in range(len(state_counts))]))

    for processor in range(len(state_counts)):
        for t in range(length):
            output_t = config_vars[(t + 1) % length][processor] if movers[t] == processor else config_vars[t][processor]
            left_t = config_vars[t][(processor - 1) % len(state_counts)]
            self_t = config_vars[t][processor]
            right_t = config_vars[t][(processor + 1) % len(state_counts)]
            for u in range(t + 1, length):
                output_u = (
                    config_vars[(u + 1) % length][processor] if movers[u] == processor else config_vars[u][processor]
                )
                left_u = config_vars[u][(processor - 1) % len(state_counts)]
                self_u = config_vars[u][processor]
                right_u = config_vars[u][(processor + 1) % len(state_counts)]
                same_context = z3.And(left_t == left_u, self_t == self_u, right_t == right_u)
                solver.add(z3.Implies(same_context, output_t == output_u))

    return config_vars


def _finish_seeded_cycle_result(
    began: float,
    solver: z3.Solver | z3.Optimize,
    config_vars: list[list[z3.ArithRef]],
    state_counts: tuple[int, ...],
) -> SeededCycleResult:
    length = len(config_vars)
    status = solver.check()
    if status == z3.unsat:
        return SeededCycleResult(
            found=False,
            message="no locally consistent good cycle exists for this mover sequence",
            cycle=None,
            elapsed=time.time() - began,
        )
    if status == z3.unknown:
        return SeededCycleResult(
            found=False,
            message=f"seeded cycle solver returned unknown: {solver.reason_unknown()}",
            cycle=None,
            elapsed=time.time() - began,
        )

    model = solver.model()
    cycle = tuple(
        tuple(model.eval(config_vars[t][i]).as_long() for i in range(len(state_counts))) for t in range(length)
    )
    return SeededCycleResult(
        found=True,
        message=f"found a seeded good cycle of length {length}",
        cycle=cycle,
        elapsed=time.time() - began,
    )


def build_witness(name: str) -> RingSystem:
    builders = {
        "n5-96": build_n5_product_96_witness,
        "n6-288": build_n6_product_288_witness,
        "n6-288-block": build_n6_product_288_block_witness,
        "n7-864": build_n7_product_864_witness,
        "n7-1152": build_n7_product_1152_witness,
    }
    return builders[name]()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("state_counts", help="comma-separated state counts")
    parser.add_argument(
        "--witness",
        choices=("n5-96", "n6-288", "n6-288-block", "n7-864", "n7-1152"),
        default="n7-864",
    )
    parser.add_argument("--cycle-timeout-ms", type=int, default=30000)
    parser.add_argument("--completion-timeout-ms", type=int, default=10000)
    parser.add_argument("--skip-completion", action="store_true")
    parser.add_argument("--cycle-selector", choices=("any", "lexmin"), default="any")
    args = parser.parse_args()

    state_counts = tuple(int(part) for part in args.state_counts.split(","))
    witness = build_witness(args.witness)
    _, movers = extract_unique_recurrent_cycle(witness)
    print(f"using mover sequence from {args.witness}: length={len(movers)}")

    cycle_solver = solve_good_cycle_from_movers_lexmin if args.cycle_selector == "lexmin" else solve_good_cycle_from_movers
    cycle_result = cycle_solver(state_counts, movers, timeout_ms=args.cycle_timeout_ms)
    print(cycle_result.message)
    print(f"cycle search elapsed={cycle_result.elapsed:.3f}s")
    if not cycle_result.found or cycle_result.cycle is None or args.skip_completion:
        return

    completion = solve_cycle_with_smt(
        state_counts,
        cycle_result.cycle,
        movers,
        timeout_ms=args.completion_timeout_ms,
    )
    print(completion.message)
    print(f"completion elapsed={completion.elapsed:.3f}s")
    if completion.found:
        print("found valid system")


def _tarjan_scc(successors: list[list[tuple[int, int]]]) -> list[list[int]]:
    index = 0
    stack: list[int] = []
    on_stack: set[int] = set()
    indices = [-1] * len(successors)
    lowlink = [0] * len(successors)
    sccs: list[list[int]] = []

    def strongconnect(node: int) -> None:
        nonlocal index
        indices[node] = index
        lowlink[node] = index
        index += 1
        stack.append(node)
        on_stack.add(node)

        for _, successor in successors[node]:
            if indices[successor] == -1:
                strongconnect(successor)
                lowlink[node] = min(lowlink[node], lowlink[successor])
            elif successor in on_stack:
                lowlink[node] = min(lowlink[node], indices[successor])

        if lowlink[node] == indices[node]:
            component: list[int] = []
            while True:
                successor = stack.pop()
                on_stack.remove(successor)
                component.append(successor)
                if successor == node:
                    break
            sccs.append(component)

    for node in range(len(successors)):
        if indices[node] == -1:
            strongconnect(node)
    return sccs


if __name__ == "__main__":
    main()
