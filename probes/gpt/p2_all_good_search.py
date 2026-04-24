from __future__ import annotations

import argparse
from collections import Counter, deque
from itertools import product


Var = tuple[int, tuple[int, int, int]]
FULL = 0b11
ONLY_FALSE = 0b01
ONLY_TRUE = 0b10


def iter_configs(state_counts: tuple[int, ...]):
    return product(*(range(m) for m in state_counts))


def build_problem(state_counts: tuple[int, ...]):
    constraints: list[tuple[Var, ...]] = []
    var_to_constraints: dict[Var, list[int]] = {}
    usage = Counter()

    for config in iter_configs(state_counts):
        constraint = []
        n = len(state_counts)
        for i in range(n):
            var = (i, (config[(i - 1) % n], config[i], config[(i + 1) % n]))
            constraint.append(var)
            usage[var] += 1
        idx = len(constraints)
        constraints.append(tuple(constraint))
        for var in constraint:
            var_to_constraints.setdefault(var, []).append(idx)

    domains = {var: FULL for var in var_to_constraints}
    processor_vars = {
        processor: [var for var in domains if var[0] == processor]
        for processor in range(len(state_counts))
    }
    return constraints, var_to_constraints, usage, domains, processor_vars


def force_value(
    domains: dict[Var, int],
    var: Var,
    mask: int,
    queue: deque[int],
    var_to_constraints: dict[Var, list[int]],
) -> bool:
    current = domains[var]
    new = current & mask
    if new == 0:
        return False
    if new == current:
        return True
    domains[var] = new
    queue.extend(var_to_constraints[var])
    return True


def propagate(
    domains: dict[Var, int],
    queue: deque[int],
    constraints: list[tuple[Var, ...]],
    var_to_constraints: dict[Var, list[int]],
    processor_vars: dict[int, list[Var]],
) -> bool:
    while queue:
        idx = queue.popleft()
        vars_in_constraint = constraints[idx]
        forced_true = [var for var in vars_in_constraint if domains[var] == ONLY_TRUE]
        possible_true = [var for var in vars_in_constraint if domains[var] & ONLY_TRUE]

        if len(forced_true) > 1 or not possible_true:
            return False

        if len(forced_true) == 1:
            true_var = forced_true[0]
            for var in vars_in_constraint:
                if var != true_var and not force_value(domains, var, ONLY_FALSE, queue, var_to_constraints):
                    return False
            continue

        if len(possible_true) == 1:
            true_var = possible_true[0]
            if not force_value(domains, true_var, ONLY_TRUE, queue, var_to_constraints):
                return False
            for var in vars_in_constraint:
                if var != true_var and not force_value(domains, var, ONLY_FALSE, queue, var_to_constraints):
                    return False

    for vars_for_processor in processor_vars.values():
        possible_true = [var for var in vars_for_processor if domains[var] & ONLY_TRUE]
        if not possible_true:
            return False
        if len(possible_true) == 1:
            if not force_value(domains, possible_true[0], ONLY_TRUE, queue, var_to_constraints):
                return False
            if queue and not propagate(domains, queue, constraints, var_to_constraints, processor_vars):
                return False

    return True


def choose_var(domains: dict[Var, int], usage: Counter) -> Var | None:
    candidates = [var for var, domain in domains.items() if domain == FULL]
    if not candidates:
        return None
    return max(candidates, key=lambda var: usage[var])


def solve_all_good_enabled_pattern(state_counts: tuple[int, ...]) -> dict[Var, bool] | None:
    constraints, var_to_constraints, usage, domains, processor_vars = build_problem(state_counts)
    queue = deque(range(len(constraints)))
    if not propagate(domains, queue, constraints, var_to_constraints, processor_vars):
        return None

    def backtrack(current_domains: dict[Var, int]) -> dict[Var, bool] | None:
        var = choose_var(current_domains, usage)
        if var is None:
            return {key: value == ONLY_TRUE for key, value in current_domains.items()}

        for choice in (ONLY_TRUE, ONLY_FALSE):
            next_domains = dict(current_domains)
            next_queue = deque()
            if not force_value(next_domains, var, choice, next_queue, var_to_constraints):
                continue
            if not propagate(next_domains, next_queue, constraints, var_to_constraints, processor_vars):
                continue
            solution = backtrack(next_domains)
            if solution is not None:
                return solution
        return None

    return backtrack(domains)


def summarize_solution(state_counts: tuple[int, ...], solution: dict[Var, bool]) -> str:
    per_processor = Counter()
    for (processor, _), enabled in solution.items():
        if enabled:
            per_processor[processor] += 1
    return (
        f"found enabled-pattern solution for {state_counts}; "
        f"moving contexts per processor = {[per_processor[i] for i in range(len(state_counts))]}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("state_counts", help="comma-separated state counts, e.g. 2,2,2,3,3")
    args = parser.parse_args()
    state_counts = tuple(int(part) for part in args.state_counts.split(","))
    solution = solve_all_good_enabled_pattern(state_counts)
    if solution is None:
        print(f"no all-good enabled-pattern solution exists for {state_counts}")
        return
    print(summarize_solution(state_counts, solution))


if __name__ == "__main__":
    main()
