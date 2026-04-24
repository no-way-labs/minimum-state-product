from __future__ import annotations

import argparse
import os
import sys
import time
from typing import Sequence

import z3

sys.path.append(os.path.dirname(os.path.dirname(__file__)))

from p2_ring import RingSystem, VerificationResult, verify_system
from scripts import verify_witnesses as vw


Config = tuple[int, ...]
Context = tuple[int, int, int]
RuleTable = dict[Context, int]


def family_state_counts(n: int) -> tuple[int, ...]:
    if n < 6:
        raise ValueError("one-bulk family requires n >= 6")
    return (2, 2, 2, 4) + (3,) * (n - 4)


def n6_boundary_rules() -> tuple[RuleTable, ...]:
    _state_counts, rules = vw.witness_n6()
    return tuple(dict(rule) for rule in rules)


def bulk_indices(n: int) -> list[int]:
    return list(range(5, n - 1))


def table_lookup_expr(
    left: z3.ArithRef,
    self_state: z3.ArithRef,
    right: z3.ArithRef,
    values: dict[Context, int | z3.ArithRef],
) -> z3.ArithRef:
    expr = None
    for key, value in sorted(values.items(), reverse=True):
        cond = z3.And(left == key[0], self_state == key[1], right == key[2])
        value_expr = z3.IntVal(value) if isinstance(value, int) else value
        expr = value_expr if expr is None else z3.If(cond, value_expr, expr)
    if expr is None:
        raise ValueError("empty lookup table")
    return expr


def build_bulk_rule_from_model(
    bulk_vars: dict[Context, z3.ArithRef],
    model: z3.ModelRef,
) -> RuleTable:
    return {
        key: model.eval(variable).as_long()
        for key, variable in sorted(bulk_vars.items())
    }


def build_family_system(n: int, bulk_rule: RuleTable) -> RingSystem:
    state_counts = family_state_counts(n)
    boundary = n6_boundary_rules()
    rules = [
        dict(boundary[0]),
        dict(boundary[1]),
        dict(boundary[2]),
        dict(boundary[3]),
        dict(boundary[4]),
    ]
    for _ in bulk_indices(n):
        rules.append(dict(bulk_rule))
    rules.append(dict(boundary[5]))
    return RingSystem(state_counts=state_counts, rules=tuple(rules))


def _solve_family_with_movers(
    n: int,
    movers: Sequence[int],
    timeout_ms: int | None = None,
    max_models: int = 20,
) -> tuple[bool, str, RingSystem | None]:
    state_counts = family_state_counts(n)
    boundary = n6_boundary_rules()
    length = len(movers)
    started = time.time()
    solver = z3.Solver()
    if timeout_ms is not None:
        solver.set("timeout", timeout_ms)

    config_vars = [[z3.Int(f"c_{t}_{i}") for i in range(n)] for t in range(length)]
    seen_vars: list[list[list[z3.BoolRef]]] = []
    bulk_vars = {(l, s, r): z3.Int(f"bulk_{l}_{s}_{r}") for l in range(3) for s in range(3) for r in range(3)}

    for variable in bulk_vars.values():
        solver.add(variable >= 0, variable < 3)

    for t in range(length):
        per_time: list[list[z3.BoolRef]] = []
        for i, state_count in enumerate(state_counts):
            solver.add(config_vars[t][i] >= 0, config_vars[t][i] < state_count)
            per_processor = [z3.Bool(f"seen_{t}_{i}_{state}") for state in range(state_count)]
            per_time.append(per_processor)
        seen_vars.append(per_time)

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

    for t, mover in enumerate(movers):
        nxt = (t + 1) % length
        change_literals = []
        for i in range(n):
            left = config_vars[t][(i - 1) % n]
            self_state = config_vars[t][i]
            right = config_vars[t][(i + 1) % n]
            if i <= 4:
                output = table_lookup_expr(left, self_state, right, boundary[i])
            elif i == n - 1:
                output = table_lookup_expr(left, self_state, right, boundary[5])
            else:
                output = table_lookup_expr(left, self_state, right, bulk_vars)

            if i == mover:
                solver.add(config_vars[nxt][i] == output)
                solver.add(output != config_vars[t][i])
            else:
                solver.add(config_vars[nxt][i] == config_vars[t][i])
            change_literals.append(config_vars[nxt][i] != config_vars[t][i])
        solver.add(z3.PbEq([(literal, 1) for literal in change_literals], 1))

    required = set(range(n))
    if set(movers) != required:
        return False, f"mover sequence omits processors {sorted(required - set(movers))}", None

    for t in range(length):
        for u in range(t + 1, length):
            solver.add(z3.Or([config_vars[t][i] != config_vars[u][i] for i in range(n)]))

    checked = 0
    while checked < max_models:
        status = solver.check()
        if status == z3.unsat:
            return False, f"no family cycle found for fixed mover sequence of length {length}", None
        if status == z3.unknown:
            return False, f"solver returned unknown for fixed mover sequence of length {length}: {solver.reason_unknown()}", None

        model = solver.model()
        bulk_rule = build_bulk_rule_from_model(bulk_vars, model)
        system = build_family_system(n, bulk_rule)
        verification = verify_system(system)
        checked += 1
        print(
            f"fixed-seed length={length} candidate={checked} elapsed={time.time()-started:.3f}s "
            f"verification={verification.message}"
        )
        if verification.valid:
            return True, f"found valid one-bulk family for fixed mover sequence of length {length}", system

        solver.add(z3.Or([variable != bulk_rule[key] for key, variable in bulk_vars.items()]))

    return False, f"checked {checked} bulk tables for fixed mover sequence with no valid family", None


def solve_family_cycle_with_inserted_bulk_moves(
    n: int,
    length: int,
    base_movers: Sequence[int],
    renamed_boundary: int,
    inserted_bulk: int,
    timeout_ms: int | None = None,
    max_models: int = 20,
) -> tuple[bool, str, RingSystem | None]:
    state_counts = family_state_counts(n)
    boundary = n6_boundary_rules()
    base = tuple(renamed_boundary if mover == n - 2 else mover for mover in base_movers)
    started = time.time()
    solver = z3.Solver()
    if timeout_ms is not None:
        solver.set("timeout", timeout_ms)

    config_vars = [[z3.Int(f"c_{t}_{i}") for i in range(n)] for t in range(length)]
    mover_vars = [z3.Int(f"m_{t}") for t in range(length)]
    proj_vars = [z3.Int(f"q_{t}") for t in range(length + 1)]
    seen_vars: list[list[list[z3.BoolRef]]] = []
    bulk_vars = {(l, s, r): z3.Int(f"bulk_{l}_{s}_{r}") for l in range(3) for s in range(3) for r in range(3)}

    for variable in bulk_vars.values():
        solver.add(variable >= 0, variable < 3)

    for t in range(length):
        solver.add(mover_vars[t] >= 0, mover_vars[t] < n)
        per_time: list[list[z3.BoolRef]] = []
        for i, state_count in enumerate(state_counts):
            solver.add(config_vars[t][i] >= 0, config_vars[t][i] < state_count)
            per_processor = [z3.Bool(f"seen_{t}_{i}_{state}") for state in range(state_count)]
            per_time.append(per_processor)
        seen_vars.append(per_time)
    for q in proj_vars:
        solver.add(q >= 0, q <= len(base))

    solver.add(proj_vars[0] == 0)
    solver.add(proj_vars[-1] == len(base))
    for t in range(length):
        is_inserted = mover_vars[t] == inserted_bulk
        solver.add(proj_vars[t + 1] == proj_vars[t] + z3.If(is_inserted, 0, 1))
        solver.add(z3.Implies(z3.Not(is_inserted), proj_vars[t] < len(base)))
        allowed = z3.Or([proj_vars[t] == idx for idx in range(len(base))])
        solver.add(allowed)
        solver.add(
            z3.Implies(
                z3.Not(is_inserted),
                z3.Or([z3.And(proj_vars[t] == idx, mover_vars[t] == base[idx]) for idx in range(len(base))]),
            )
        )

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

    for i in range(n):
        solver.add(z3.Or([mover_vars[t] == i for t in range(length)]))

    for t in range(length):
        nxt = (t + 1) % length
        change_literals = []
        for i in range(n):
            left = config_vars[t][(i - 1) % n]
            self_state = config_vars[t][i]
            right = config_vars[t][(i + 1) % n]
            if i <= 4:
                output = table_lookup_expr(left, self_state, right, boundary[i])
            elif i == n - 1:
                output = table_lookup_expr(left, self_state, right, boundary[5])
            else:
                output = table_lookup_expr(left, self_state, right, bulk_vars)

            moved_here = mover_vars[t] == i
            solver.add(
                z3.If(
                    moved_here,
                    config_vars[nxt][i] == output,
                    config_vars[nxt][i] == config_vars[t][i],
                )
            )
            solver.add(z3.Implies(moved_here, output != config_vars[t][i]))
            change_literals.append(config_vars[nxt][i] != config_vars[t][i])
        solver.add(z3.PbEq([(literal, 1) for literal in change_literals], 1))

    for t in range(length):
        for u in range(t + 1, length):
            solver.add(z3.Or([config_vars[t][i] != config_vars[u][i] for i in range(n)]))

    checked = 0
    while checked < max_models:
        status = solver.check()
        if status == z3.unsat:
            return False, f"no interleaved family cycle found at length {length}", None
        if status == z3.unknown:
            return False, f"solver returned unknown for interleaved family cycle at length {length}: {solver.reason_unknown()}", None

        model = solver.model()
        bulk_rule = build_bulk_rule_from_model(bulk_vars, model)
        system = build_family_system(n, bulk_rule)
        verification = verify_system(system)
        checked += 1
        print(
            f"interleaved length={length} candidate={checked} elapsed={time.time()-started:.3f}s "
            f"verification={verification.message}"
        )
        if verification.valid:
            return True, f"found valid interleaved one-bulk family at length {length}", system

        solver.add(z3.Or([variable != bulk_rule[key] for key, variable in bulk_vars.items()]))

    return False, f"checked {checked} interleaved bulk tables at length {length} with no valid family", None


def solve_family_cycle(
    n: int,
    length: int,
    timeout_ms: int | None = None,
    max_models: int = 20,
) -> tuple[bool, str, RingSystem | None]:
    state_counts = family_state_counts(n)
    boundary = n6_boundary_rules()
    started = time.time()
    solver = z3.Solver()
    if timeout_ms is not None:
        solver.set("timeout", timeout_ms)

    config_vars = [[z3.Int(f"c_{t}_{i}") for i in range(n)] for t in range(length)]
    mover_vars = [z3.Int(f"m_{t}") for t in range(length)]
    seen_vars: list[list[list[z3.BoolRef]]] = []
    bulk_vars = {(l, s, r): z3.Int(f"bulk_{l}_{s}_{r}") for l in range(3) for s in range(3) for r in range(3)}

    for variable in bulk_vars.values():
        solver.add(variable >= 0, variable < 3)

    for t in range(length):
        per_time: list[list[z3.BoolRef]] = []
        for i, state_count in enumerate(state_counts):
            solver.add(config_vars[t][i] >= 0, config_vars[t][i] < state_count)
            per_processor = [z3.Bool(f"seen_{t}_{i}_{state}") for state in range(state_count)]
            per_time.append(per_processor)
        seen_vars.append(per_time)
        solver.add(mover_vars[t] >= 0, mover_vars[t] < n)

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
            left = config_vars[t][(i - 1) % n]
            self_state = config_vars[t][i]
            right = config_vars[t][(i + 1) % n]
            if i <= 4:
                output = table_lookup_expr(left, self_state, right, boundary[i])
            elif i == n - 1:
                output = table_lookup_expr(left, self_state, right, boundary[5])
            else:
                output = table_lookup_expr(left, self_state, right, bulk_vars)

            moved_here = mover_vars[t] == i
            solver.add(
                z3.If(
                    moved_here,
                    config_vars[nxt][i] == output,
                    config_vars[nxt][i] == config_vars[t][i],
                )
            )
            solver.add(z3.Implies(moved_here, output != config_vars[t][i]))
            change_literals.append(config_vars[nxt][i] != config_vars[t][i])
        solver.add(z3.PbEq([(literal, 1) for literal in change_literals], 1))

    for i in range(n):
        solver.add(z3.Or([mover_vars[t] == i for t in range(length)]))

    for t in range(length):
        for u in range(t + 1, length):
            solver.add(z3.Or([config_vars[t][i] != config_vars[u][i] for i in range(n)]))

    checked = 0
    while checked < max_models:
        status = solver.check()
        if status == z3.unsat:
            return False, f"no family cycle found at length {length}", None
        if status == z3.unknown:
            return False, f"solver returned unknown at length {length}: {solver.reason_unknown()}", None

        model = solver.model()
        bulk_rule = build_bulk_rule_from_model(bulk_vars, model)
        system = build_family_system(n, bulk_rule)
        verification = verify_system(system)
        checked += 1
        print(
            f"length={length} candidate={checked} elapsed={time.time()-started:.3f}s "
            f"verification={verification.message}"
        )
        if verification.valid:
            return True, f"found valid one-bulk family at length {length}", system

        solver.add(z3.Or([variable != bulk_rule[key] for key, variable in bulk_vars.items()]))

    return False, f"checked {checked} bulk tables at length {length} with no valid family", None


def format_bulk_rule(rule: RuleTable) -> str:
    rows = []
    for key in sorted(rule):
        rows.append(f"{key}->{rule[key]}")
    return "\n".join(rows)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=9)
    parser.add_argument("--length-from", type=int, required=True)
    parser.add_argument("--length-to", type=int, required=True)
    parser.add_argument("--timeout-ms", type=int, default=10000)
    parser.add_argument("--max-models", type=int, default=20)
    parser.add_argument(
        "--movers",
        help="comma-separated fixed mover sequence; if set, ignores the length range and solves only for configs + bulk table",
    )
    parser.add_argument(
        "--interleave-n6-block",
        action="store_true",
        help="constrain the mover sequence to be the n6 block-witness sequence with extra moves by the new bulk processor inserted",
    )
    args = parser.parse_args()

    if args.movers:
        movers = tuple(int(part) for part in args.movers.split(",") if part.strip())
        found, message, system = _solve_family_with_movers(
            n=args.n,
            movers=movers,
            timeout_ms=args.timeout_ms,
            max_models=args.max_models,
        )
        print(message)
        if found and system is not None:
            print(f"state_counts={system.state_counts}")
            print("bulk rule:")
            print(format_bulk_rule(system.rules[5]))
        return

    if args.interleave_n6_block:
        from scripts.p2_seeded_cycle_search import extract_unique_recurrent_cycle
        from p2_witnesses import build_n6_product_288_block_witness

        _, base_movers = extract_unique_recurrent_cycle(build_n6_product_288_block_witness())
        for length in range(args.length_from, args.length_to + 1):
            found, message, system = solve_family_cycle_with_inserted_bulk_moves(
                n=args.n,
                length=length,
                base_movers=base_movers,
                renamed_boundary=args.n - 1,
                inserted_bulk=5,
                timeout_ms=args.timeout_ms,
                max_models=args.max_models,
            )
            print(message)
            if found and system is not None:
                print(f"state_counts={system.state_counts}")
                print("bulk rule:")
                print(format_bulk_rule(system.rules[5]))
                return
        return

    for length in range(args.length_from, args.length_to + 1):
        found, message, system = solve_family_cycle(
            n=args.n,
            length=length,
            timeout_ms=args.timeout_ms,
            max_models=args.max_models,
        )
        print(message)
        if found and system is not None:
            print(f"state_counts={system.state_counts}")
            print("bulk rule:")
            print(format_bulk_rule(system.rules[5]))
            return


if __name__ == "__main__":
    main()
