from __future__ import annotations

import argparse
import os
import sys
import time
from dataclasses import dataclass

import z3

sys.path.insert(0, os.path.dirname(__file__))

from p2_ring import RingSystem, verify_system
from p2_completion_search import (
    all_keys,
    build_initial_domains_from_cycle,
    iter_configs,
    propagate,
    has_fatal_forced_cycle_singletons,
)
from p2_cycle_screen import forced_rule_map
from p2_good_cycle_search import enumerate_good_cycles, local_context


Config = tuple[int, ...]
RuleKey = tuple[int, tuple[int, int, int]]


@dataclass(frozen=True)
class SmtCompletionResult:
    found: bool
    message: str
    elapsed: float
    system: RingSystem | None


def build_system_from_model(
    state_counts: tuple[int, ...],
    variables: dict[RuleKey, z3.ArithRef],
    model: z3.ModelRef,
) -> RingSystem:
    rules = []
    for processor in range(len(state_counts)):
        table = {}
        for key, variable in variables.items():
            if key[0] != processor:
                continue
            table[key[1]] = model.eval(variable).as_long()
        rules.append(table)
    return RingSystem(state_counts=state_counts, rules=tuple(rules))


def solve_cycle_with_smt(
    state_counts: tuple[int, ...],
    cycle: tuple[Config, ...],
    movers: tuple[int, ...],
    timeout_ms: int | None = None,
) -> SmtCompletionResult:
    began = time.time()
    cycle, cycle_set, domains = build_initial_domains_from_cycle(state_counts, cycle, movers)
    configs = iter_configs(state_counts)
    propagated = propagate(state_counts, cycle_set, configs, domains)
    if propagated is None:
        return SmtCompletionResult(
            found=False,
            message="propagation proves this cycle cannot complete",
            elapsed=time.time() - began,
            system=None,
        )

    solver = z3.Solver()
    if timeout_ms is not None:
        solver.set("timeout", timeout_ms)

    variables: dict[RuleKey, z3.IntNumRef | z3.ArithRef] = {}
    for key in all_keys(state_counts):
        processor, _ = key
        variable = z3.Int(f"r_{processor}_{len(variables)}")
        variables[key] = variable
        domain = sorted(propagated[key])
        if len(domain) == 1:
            solver.add(variable == domain[0])
        else:
            solver.add(z3.Or([variable == value for value in domain]))

    off_cycle = [config for config in configs if config not in cycle_set]
    rank: dict[Config, z3.ArithRef] = {}
    for idx, config in enumerate(off_cycle):
        variable = z3.Int(f"rank_{idx}")
        rank[config] = variable
        solver.add(variable >= 0)
        solver.add(variable < len(off_cycle))

    for config in off_cycle:
        enabled_literals = []
        for processor in range(len(state_counts)):
            key = (processor, local_context(config, processor))
            variable = variables[key]
            current = config[processor]
            for value in sorted(propagated[key]):
                if value == current:
                    continue
                lit = variable == value
                enabled_literals.append(lit)
                nxt = list(config)
                nxt[processor] = value
                next_config = tuple(nxt)
                if next_config in cycle_set:
                    continue
                solver.add(z3.Implies(lit, rank[next_config] < rank[config]))
        if not enabled_literals:
            return SmtCompletionResult(
                found=False,
                message=f"propagation leaves a dead configuration {config}",
                elapsed=time.time() - began,
                system=None,
            )
        solver.add(z3.Or(enabled_literals))

    status = solver.check()
    if status == z3.unsat:
        return SmtCompletionResult(
            found=False,
            message="SMT encoding proves this cycle has no acyclic completion",
            elapsed=time.time() - began,
            system=None,
        )
    if status == z3.unknown:
        return SmtCompletionResult(
            found=False,
            message=f"SMT solver returned unknown: {solver.reason_unknown()}",
            elapsed=time.time() - began,
            system=None,
        )

    system = build_system_from_model(state_counts, variables, solver.model())
    verification = verify_system(system)
    if not verification.valid:
        return SmtCompletionResult(
            found=False,
            message=f"SMT model failed verification: {verification.message}",
            elapsed=time.time() - began,
            system=system,
        )

    return SmtCompletionResult(
        found=True,
        message=verification.message,
        elapsed=time.time() - began,
        system=system,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("state_counts", help="comma-separated state counts")
    parser.add_argument("--screen-time-limit", type=float, default=30.0)
    parser.add_argument("--solver-timeout-ms", type=int, default=60000)
    parser.add_argument("--max-cycles", type=int, default=5000)
    parser.add_argument("--max-survivors", type=int, default=20)
    args = parser.parse_args()

    state_counts = tuple(int(part) for part in args.state_counts.split(","))
    started = time.time()
    screened = 0
    tried = 0

    for cycle, movers in enumerate_good_cycles(state_counts, time_limit=args.screen_time_limit, max_cycles=args.max_cycles):
        screened += 1
        cycle_set = frozenset(cycle)
        forced_map = forced_rule_map(cycle, movers)
        if has_fatal_forced_cycle_singletons(state_counts, cycle_set, forced_map):
            continue

        tried += 1
        print(f"trying survivor cycle {screened} length={len(cycle)}")
        result = solve_cycle_with_smt(state_counts, cycle, movers, timeout_ms=args.solver_timeout_ms)
        print(result.message)
        print(f"screened={screened} tried={tried} elapsed={time.time()-started:.3f}s")
        if result.system is not None and result.found:
            print("found valid system")
            return
        if tried >= args.max_survivors:
            break

    print(
        f"no valid SMT completion found among {tried} survivor cycles "
        f"within {screened} screened cycles in {time.time()-started:.3f}s"
    )


if __name__ == "__main__":
    main()
