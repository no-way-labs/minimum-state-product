from __future__ import annotations

import argparse
import os
import sys
import time
from dataclasses import dataclass

import z3

sys.path.append(os.path.dirname(os.path.dirname(__file__)))

from p2_ring import Config
from scripts.p2_smt_completion import solve_cycle_with_smt


@dataclass(frozen=True)
class BoundedCycleResult:
    found: bool
    message: str
    cycle: tuple[Config, ...] | None
    movers: tuple[int, ...] | None
    elapsed: float


def solve_bounded_good_cycle(
    state_counts: tuple[int, ...],
    length: int,
    timeout_ms: int | None = None,
) -> BoundedCycleResult:
    if length < len(state_counts):
        return BoundedCycleResult(
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

    # Quotient time rotation and state relabeling by starting from the all-zero configuration.
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
            # Canonical state introduction: state s cannot appear before state s-1 has appeared.
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

    for i in range(n):
        solver.add(z3.Or([mover_vars[t] == i for t in range(length)]))

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
        return BoundedCycleResult(
            found=False,
            message=f"no locally consistent good cycle of length {length} exists",
            cycle=None,
            movers=None,
            elapsed=time.time() - began,
        )
    if status == z3.unknown:
        return BoundedCycleResult(
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
    return BoundedCycleResult(
        found=True,
        message=f"found locally consistent good cycle of length {length}",
        cycle=cycle,
        movers=movers,
        elapsed=time.time() - began,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("state_counts", help="comma-separated state counts")
    parser.add_argument("--length", type=int, help="exact cycle length to search")
    parser.add_argument("--length-from", type=int, dest="length_from")
    parser.add_argument("--length-to", type=int, dest="length_to")
    parser.add_argument("--timeout-ms", type=int, default=30000)
    parser.add_argument("--completion-timeout-ms", type=int, default=10000)
    parser.add_argument("--try-completion", action="store_true")
    args = parser.parse_args()

    state_counts = tuple(int(part) for part in args.state_counts.split(","))
    lengths: list[int]
    if args.length is not None:
        lengths = [args.length]
    else:
        if args.length_from is None or args.length_to is None:
            raise SystemExit("either --length or both --length-from/--length-to are required")
        lengths = list(range(args.length_from, args.length_to + 1))

    for length in lengths:
        result = solve_bounded_good_cycle(state_counts, length, timeout_ms=args.timeout_ms)
        print(result.message)
        print(f"length={length} elapsed={result.elapsed:.3f}s")
        if not result.found or result.cycle is None or result.movers is None:
            continue
        if not args.try_completion:
            return
        completion = solve_cycle_with_smt(
            state_counts,
            result.cycle,
            result.movers,
            timeout_ms=args.completion_timeout_ms,
        )
        print(completion.message)
        print(f"completion elapsed={completion.elapsed:.3f}s")
        if completion.found:
            print("found valid system")
            return


if __name__ == "__main__":
    main()
