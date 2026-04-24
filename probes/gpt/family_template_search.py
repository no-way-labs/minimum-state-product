from __future__ import annotations

import argparse
import os
import sys
import time

import z3

sys.path.append(os.path.dirname(os.path.dirname(__file__)))

from p2_ring import RingSystem, verify_system
from p2_witnesses import build_n6_product_288_block_witness
from scripts.family_one_bulk_search import family_state_counts, n6_boundary_rules, table_lookup_expr
from scripts.p2_seeded_cycle_search import extract_unique_recurrent_cycle


Config = tuple[int, ...]
Context = tuple[int, int, int]
RuleValueMap = dict[Context, int | z3.ArithRef]
RuleTable = dict[Context, int]


def make_unknown_table(
    name: str,
    left_m: int,
    self_m: int,
    right_m: int,
) -> RuleValueMap:
    table: RuleValueMap = {}
    for left in range(left_m):
        for self_state in range(self_m):
            for right in range(right_m):
                variable = z3.Int(f"{name}_{left}_{self_state}_{right}")
                table[(left, self_state, right)] = variable
    return table


def collect_variables(*tables: RuleValueMap) -> list[z3.ArithRef]:
    variables: list[z3.ArithRef] = []
    for table in tables:
        for value in table.values():
            if isinstance(value, int):
                continue
            variables.append(value)
    return variables


def instantiate_table(table: RuleValueMap, model: z3.ModelRef) -> RuleTable:
    out: RuleTable = {}
    for key, value in table.items():
        out[key] = value if isinstance(value, int) else model.eval(value).as_long()
    return out


def build_template_tables(
    n: int,
    bulk_mode: str,
    free_p4: bool,
    free_last: bool,
) -> tuple[list[RuleValueMap], list[z3.ArithRef]]:
    state_counts = family_state_counts(n)
    fixed = n6_boundary_rules()
    tables: list[RuleValueMap] = []
    bulk_a = make_unknown_table("bulk_a", 3, 3, 3)
    bulk_b = bulk_a if bulk_mode == "one" else make_unknown_table("bulk_b", 3, 3, 3)
    p4_table = make_unknown_table("p4", 4, 3, 3) if free_p4 else dict(fixed[4])
    plast_table = make_unknown_table("plast", 3, 3, 2) if free_last else dict(fixed[5])

    for processor in range(n):
        if processor <= 3:
            tables.append(dict(fixed[processor]))
        elif processor == 4:
            tables.append(p4_table)
        elif processor == n - 1:
            tables.append(plast_table)
        else:
            bulk_idx = processor - 5
            tables.append(bulk_a if bulk_idx % 2 == 0 else bulk_b)

    variables = collect_variables(bulk_a, bulk_b if bulk_mode == "period2" else {}, p4_table, plast_table)
    return tables, variables


def instantiate_system(
    n: int,
    tables: list[RuleValueMap],
    model: z3.ModelRef,
) -> RingSystem:
    realized = [instantiate_table(table, model) for table in tables]
    return RingSystem(state_counts=family_state_counts(n), rules=tuple(realized))


def solve_interleaved_template(
    n: int,
    length: int,
    bulk_mode: str,
    free_p4: bool,
    free_last: bool,
    timeout_ms: int | None,
    max_models: int,
) -> tuple[bool, str, RingSystem | None]:
    state_counts = family_state_counts(n)
    tables, variables = build_template_tables(n, bulk_mode, free_p4, free_last)
    _, base_movers = extract_unique_recurrent_cycle(build_n6_product_288_block_witness())
    base = tuple(n - 1 if mover == 5 else mover for mover in base_movers)

    started = time.time()
    solver = z3.Solver()
    if timeout_ms is not None:
        solver.set("timeout", timeout_ms)

    for variable in variables:
        # Range depends on the processor's own state count, but every unknown here is ternary-valued.
        solver.add(variable >= 0, variable < 3)

    config_vars = [[z3.Int(f"c_{t}_{i}") for i in range(n)] for t in range(length)]
    mover_vars = [z3.Int(f"m_{t}") for t in range(length)]
    proj_vars = [z3.Int(f"q_{t}") for t in range(length + 1)]
    seen_vars: list[list[list[z3.BoolRef]]] = []

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
        is_inserted = mover_vars[t] == 5
        solver.add(proj_vars[t + 1] == proj_vars[t] + z3.If(is_inserted, 0, 1))
        solver.add(z3.Implies(z3.Not(is_inserted), proj_vars[t] < len(base)))
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
            output = table_lookup_expr(left, self_state, right, tables[i])
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
            return False, f"no template family cycle found at length {length}", None
        if status == z3.unknown:
            return False, f"solver returned unknown at length {length}: {solver.reason_unknown()}", None

        model = solver.model()
        system = instantiate_system(n, tables, model)
        verification = verify_system(system)
        checked += 1
        print(
            f"template length={length} candidate={checked} elapsed={time.time()-started:.3f}s "
            f"verification={verification.message}"
        )
        if verification.valid:
            return True, f"found valid template family at length {length}", system

        solver.add(z3.Or([variable != model.eval(variable) for variable in variables]))

    return False, f"checked {checked} template candidates at length {length} with no valid family", None


def solve_fixed_template(
    n: int,
    movers: tuple[int, ...],
    bulk_mode: str,
    free_p4: bool,
    free_last: bool,
    timeout_ms: int | None,
    max_models: int,
) -> tuple[bool, str, RingSystem | None]:
    state_counts = family_state_counts(n)
    tables, variables = build_template_tables(n, bulk_mode, free_p4, free_last)
    length = len(movers)

    started = time.time()
    solver = z3.Solver()
    if timeout_ms is not None:
        solver.set("timeout", timeout_ms)

    for variable in variables:
        solver.add(variable >= 0, variable < 3)

    config_vars = [[z3.Int(f"fc_{t}_{i}") for i in range(n)] for t in range(length)]
    seen_vars: list[list[list[z3.BoolRef]]] = []

    for t in range(length):
        per_time: list[list[z3.BoolRef]] = []
        for i, state_count in enumerate(state_counts):
            solver.add(config_vars[t][i] >= 0, config_vars[t][i] < state_count)
            per_processor = [z3.Bool(f"fseen_{t}_{i}_{state}") for state in range(state_count)]
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

    if set(movers) != set(range(n)):
        return False, f"mover sequence omits processors {sorted(set(range(n)) - set(movers))}", None

    for t, mover in enumerate(movers):
        nxt = (t + 1) % length
        change_literals = []
        for i in range(n):
            left = config_vars[t][(i - 1) % n]
            self_state = config_vars[t][i]
            right = config_vars[t][(i + 1) % n]
            output = table_lookup_expr(left, self_state, right, tables[i])
            if i == mover:
                solver.add(config_vars[nxt][i] == output)
                solver.add(output != config_vars[t][i])
            else:
                solver.add(config_vars[nxt][i] == config_vars[t][i])
            change_literals.append(config_vars[nxt][i] != config_vars[t][i])
        solver.add(z3.PbEq([(literal, 1) for literal in change_literals], 1))

    for t in range(length):
        for u in range(t + 1, length):
            solver.add(z3.Or([config_vars[t][i] != config_vars[u][i] for i in range(n)]))

    checked = 0
    while checked < max_models:
        status = solver.check()
        if status == z3.unsat:
            return False, f"no fixed-template family cycle found for length {length}", None
        if status == z3.unknown:
            return False, f"solver returned unknown for fixed-template length {length}: {solver.reason_unknown()}", None

        model = solver.model()
        system = instantiate_system(n, tables, model)
        verification = verify_system(system)
        checked += 1
        print(
            f"fixed-template length={length} candidate={checked} elapsed={time.time()-started:.3f}s "
            f"verification={verification.message}"
        )
        if verification.valid:
            return True, f"found valid fixed-template family at length {length}", system

        solver.add(z3.Or([variable != model.eval(variable) for variable in variables]))

    return False, f"checked {checked} fixed-template candidates at length {length} with no valid family", None


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=7)
    parser.add_argument("--length-from", type=int, required=True)
    parser.add_argument("--length-to", type=int, required=True)
    parser.add_argument("--timeout-ms", type=int, default=2000)
    parser.add_argument("--max-models", type=int, default=2)
    parser.add_argument("--bulk-mode", choices=("one", "period2"), default="one")
    parser.add_argument("--free-p4", action="store_true")
    parser.add_argument("--free-last", action="store_true")
    parser.add_argument("--movers", help="comma-separated fixed mover sequence")
    args = parser.parse_args()

    if args.movers:
        movers = tuple(int(part) for part in args.movers.split(",") if part.strip())
        found, message, system = solve_fixed_template(
            n=args.n,
            movers=movers,
            bulk_mode=args.bulk_mode,
            free_p4=args.free_p4,
            free_last=args.free_last,
            timeout_ms=args.timeout_ms,
            max_models=args.max_models,
        )
        print(message)
        if found and system is not None:
            print(f"state_counts={system.state_counts}")
            for i, table in enumerate(system.rules):
                print(f"P{i} entries={len(table)}")
        return

    for length in range(args.length_from, args.length_to + 1):
        found, message, system = solve_interleaved_template(
            n=args.n,
            length=length,
            bulk_mode=args.bulk_mode,
            free_p4=args.free_p4,
            free_last=args.free_last,
            timeout_ms=args.timeout_ms,
            max_models=args.max_models,
        )
        print(message)
        if found and system is not None:
            print(f"state_counts={system.state_counts}")
            for i, table in enumerate(system.rules):
                print(f"P{i} entries={len(table)}")
            return


if __name__ == "__main__":
    main()
