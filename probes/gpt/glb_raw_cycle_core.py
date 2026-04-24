#!/usr/bin/env python3
"""Inspect raw anchored-cycle unsat cores without local-context consistency."""

from __future__ import annotations

import argparse
import os
import sys

import z3


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)


def parse_int_tuple(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def build_raw_cycle_solver(
    state_counts: tuple[int, ...],
    movers: tuple[int, ...],
    *,
    track_labels: bool,
) -> tuple[z3.Solver, list[list[z3.ArithRef]], dict[str, z3.BoolRef]]:
    n = len(state_counts)
    length = len(movers)
    solver = z3.Solver()
    if track_labels:
        solver.set(unsat_core=True)
        solver.set("smt.core.minimize", True)

    config_vars = [[z3.Int(f"c_{t}_{i}") for i in range(n)] for t in range(length)]
    tracked: dict[str, z3.BoolRef] = {}

    def add_or_track(name: str, expr: z3.BoolRef) -> None:
        if track_labels:
            tracked[name] = expr
            solver.assert_and_track(expr, z3.Bool(name))
        else:
            solver.add(expr)

    for t in range(length):
        for i, state_count in enumerate(state_counts):
            add_or_track(f"dom_lo_{t}_{i}", config_vars[t][i] >= 0)
            add_or_track(f"dom_hi_{t}_{i}", config_vars[t][i] < state_count)

    for i in range(n):
        add_or_track(f"anchor_{i}", config_vars[0][i] == 0)

    for t, mover in enumerate(movers):
        nxt = (t + 1) % length
        for i in range(n):
            if i != mover:
                add_or_track(f"stay_{t}_{i}", config_vars[nxt][i] == config_vars[t][i])
        add_or_track(f"move_{t}_{mover}", config_vars[nxt][mover] != config_vars[t][mover])

    for t in range(length):
        for u in range(t + 1, length):
            add_or_track(f"distinct_{t}_{u}", z3.Or([config_vars[t][i] != config_vars[u][i] for i in range(n)]))

    return solver, config_vars, tracked


def summarize_raw_core(state_counts: tuple[int, ...], movers: tuple[int, ...]) -> None:
    solver, _, _ = build_raw_cycle_solver(state_counts, movers, track_labels=True)
    status = solver.check()
    print(f"status={status}")
    if status != z3.unsat:
        return
    core = [str(label) for label in solver.unsat_core()]
    print(f"core_size={len(core)}")
    print("distinct_labels:")
    for label in core:
        if label.startswith("distinct_"):
            print(f"  {label}")
    print("other_labels:")
    for label in core:
        if not label.startswith("distinct_"):
            print(f"  {label}")


def realize_without_distinct(
    state_counts: tuple[int, ...],
    movers: tuple[int, ...],
    distinct_t: int,
    distinct_u: int,
) -> None:
    n = len(state_counts)
    length = len(movers)
    solver = z3.Solver()
    config_vars = [[z3.Int(f"c_{t}_{i}") for i in range(n)] for t in range(length)]

    for t in range(length):
        for i, state_count in enumerate(state_counts):
            solver.add(config_vars[t][i] >= 0)
            solver.add(config_vars[t][i] < state_count)

    for i in range(n):
        solver.add(config_vars[0][i] == 0)

    for t, mover in enumerate(movers):
        nxt = (t + 1) % length
        for i in range(n):
            if i != mover:
                solver.add(config_vars[nxt][i] == config_vars[t][i])
        solver.add(config_vars[nxt][mover] != config_vars[t][mover])

    for t in range(length):
        for u in range(t + 1, length):
            if (t, u) == (distinct_t, distinct_u):
                continue
            solver.add(z3.Or([config_vars[t][i] != config_vars[u][i] for i in range(n)]))

    n = len(state_counts)
    length = len(movers)
    solver.push()
    solver.add(z3.And([config_vars[distinct_t][i] == config_vars[distinct_u][i] for i in range(n)]))
    status = solver.check()
    print(f"realize_without_distinct_{distinct_t}_{distinct_u}: status={status}")
    if status != z3.sat:
        solver.pop()
        return
    model = solver.model()

    def value(expr: z3.ArithRef) -> int:
        return model.eval(expr, model_completion=True).as_long()

    for t in range(max(0, distinct_t - 1), min(length, distinct_u + 2)):
        config = tuple(value(config_vars[t][i]) for i in range(n))
        print(f"  t={t} mover={movers[t]} config={config}")
    solver.pop()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--state-counts", required=True)
    parser.add_argument("--movers", required=True)
    parser.add_argument("--realize-pair", help="pair t,u for a repeated config witness")
    args = parser.parse_args()

    state_counts = parse_int_tuple(args.state_counts)
    movers = parse_int_tuple(args.movers)
    summarize_raw_core(state_counts, movers)
    if args.realize_pair:
        t_str, u_str = args.realize_pair.split(",")
        realize_without_distinct(state_counts, movers, int(t_str), int(u_str))


if __name__ == "__main__":
    main()
