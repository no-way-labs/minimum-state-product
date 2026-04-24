#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import sys
import time
from dataclasses import dataclass

import z3


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from p2_ring import Config


@dataclass(frozen=True)
class AdjacentCycleResult:
    found: bool
    message: str
    cycle: tuple[Config, ...] | None
    movers: tuple[int, ...] | None
    elapsed: float


def parse_state_counts(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def solve_adjacent_good_cycle(
    state_counts: tuple[int, ...],
    length: int,
    timeout_ms: int | None = None,
    allow_same_successive_mover: bool = True,
) -> AdjacentCycleResult:
    if length < len(state_counts):
        return AdjacentCycleResult(
            found=False,
            message="length is below the fairness minimum",
            cycle=None,
            movers=None,
            elapsed=0.0,
        )

    began = time.time()
    n = len(state_counts)
    solver = z3.Solver()
    if timeout_ms is not None:
        solver.set("timeout", timeout_ms)

    config_vars = [[z3.Int(f"c_{t}_{i}") for i in range(n)] for t in range(length)]
    mover_vars = [z3.Int(f"m_{t}") for t in range(length)]
    seen_vars: list[list[list[z3.BoolRef]]] = []

    for t in range(length):
        for i, state_count in enumerate(state_counts):
            solver.add(config_vars[t][i] >= 0)
            solver.add(config_vars[t][i] < state_count)
        solver.add(mover_vars[t] >= 0)
        solver.add(mover_vars[t] < n)

    for t in range(length):
        per_time: list[list[z3.BoolRef]] = []
        for i, state_count in enumerate(state_counts):
            per_processor = [z3.Bool(f"seen_{t}_{i}_{state}") for state in range(state_count)]
            per_time.append(per_processor)
        seen_vars.append(per_time)

    # Quotient time rotation and state relabeling.
    for i in range(n):
        solver.add(config_vars[0][i] == 0)

    for i, state_count in enumerate(state_counts):
        solver.add(seen_vars[0][i][0])
        for state in range(1, state_count):
            solver.add(seen_vars[0][i][state] == z3.BoolVal(False))

    for t in range(1, length):
        for i, state_count in enumerate(state_counts):
            for state in range(state_count):
                solver.add(
                    seen_vars[t][i][state]
                    == z3.Or(seen_vars[t - 1][i][state], config_vars[t][i] == state)
                )
            for state in range(1, state_count):
                solver.add(z3.Implies(seen_vars[t][i][state], seen_vars[t][i][state - 1]))

    for t in range(length):
        nxt = (t + 1) % length
        change_literals = []
        for i in range(n):
            moved_here = mover_vars[t] == i
            solver.add(
                z3.If(
                    moved_here,
                    config_vars[nxt][i] != config_vars[t][i],
                    config_vars[nxt][i] == config_vars[t][i],
                )
            )
            change_literals.append(config_vars[nxt][i] != config_vars[t][i])
        solver.add(z3.PbEq([(lit, 1) for lit in change_literals], 1))

    # Fairness + no-single-move lemma.
    for i in range(n):
        mover_count = z3.Sum([z3.If(mover_vars[t] == i, 1, 0) for t in range(length)])
        solver.add(mover_count >= 2)
        if state_counts[i] == 2:
            solver.add(mover_count % 2 == 0)

    # Local mover succession on the ring: next mover must lie in {i-1, i, i+1}.
    allowed_deltas = {0, 1, n - 1} if allow_same_successive_mover else {1, n - 1}
    for t in range(length):
        nxt = (t + 1) % length
        solver.add(
            z3.Or(
                [
                    mover_vars[nxt] == (mover_vars[t] + delta) % n
                    for delta in sorted(allowed_deltas)
                ]
            )
        )

    for t in range(length):
        for u in range(t + 1, length):
            solver.add(z3.Or([config_vars[t][i] != config_vars[u][i] for i in range(n)]))

    for processor in range(n):
        for t in range(length):
            output_t = z3.If(
                mover_vars[t] == processor,
                config_vars[(t + 1) % length][processor],
                config_vars[t][processor],
            )
            left_t = config_vars[t][(processor - 1) % n]
            self_t = config_vars[t][processor]
            right_t = config_vars[t][(processor + 1) % n]
            for u in range(t + 1, length):
                output_u = z3.If(
                    mover_vars[u] == processor,
                    config_vars[(u + 1) % length][processor],
                    config_vars[u][processor],
                )
                left_u = config_vars[u][(processor - 1) % n]
                self_u = config_vars[u][processor]
                right_u = config_vars[u][(processor + 1) % n]
                same_context = z3.And(left_t == left_u, self_t == self_u, right_t == right_u)
                solver.add(z3.Implies(same_context, output_t == output_u))

    status = solver.check()
    if status == z3.unsat:
        return AdjacentCycleResult(
            found=False,
            message=f"no adjacent good cycle of length {length} exists",
            cycle=None,
            movers=None,
            elapsed=time.time() - began,
        )
    if status == z3.unknown:
        return AdjacentCycleResult(
            found=False,
            message=f"solver returned unknown: {solver.reason_unknown()}",
            cycle=None,
            movers=None,
            elapsed=time.time() - began,
        )

    model = solver.model()
    cycle = tuple(
        tuple(model.eval(config_vars[t][i]).as_long() for i in range(n))
        for t in range(length)
    )
    movers = tuple(model.eval(mover_vars[t]).as_long() for t in range(length))
    return AdjacentCycleResult(
        found=True,
        message=f"found adjacent good cycle of length {length}",
        cycle=cycle,
        movers=movers,
        elapsed=time.time() - began,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("state_counts", help="comma-separated state counts")
    parser.add_argument("--length", type=int, default=25)
    parser.add_argument("--timeout-ms", type=int, default=5000)
    parser.add_argument("--strict-adjacency", action="store_true")
    args = parser.parse_args()

    result = solve_adjacent_good_cycle(
        parse_state_counts(args.state_counts),
        args.length,
        timeout_ms=args.timeout_ms,
        allow_same_successive_mover=not args.strict_adjacency,
    )
    print(result.message)
    print(f"elapsed={result.elapsed:.3f}s")
    if result.found:
        print(f"movers={result.movers}")
        print(f"cycle_length={len(result.cycle)}")


if __name__ == "__main__":
    main()
