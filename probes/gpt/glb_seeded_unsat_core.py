#!/usr/bin/env python3
"""Inspect unsat cores for fixed mover words in the seeded cycle solver."""

from __future__ import annotations

import argparse
import os
import re
import sys

import z3


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)


def parse_int_tuple(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


CTX_RE = re.compile(r"ctx_(\d+)_(\d+)_(\d+)$")


def parse_ctx_label(label: str) -> tuple[int, int, int] | None:
    match = CTX_RE.match(label)
    if not match:
        return None
    return tuple(int(part) for part in match.groups())


def forced_value(solver: z3.Solver, expr: z3.ArithRef) -> int | None:
    if solver.check() != z3.sat:
        return None
    model = solver.model()
    value = model.eval(expr).as_long()
    solver.push()
    solver.add(expr != value)
    status = solver.check()
    solver.pop()
    if status == z3.unsat:
        return value
    return None


def build_seeded_cycle_core_solver(
    state_counts: tuple[int, ...],
    movers: tuple[int, ...],
    *,
    track_labels: bool,
) -> tuple[z3.Solver, list[list[z3.IntNumRef]], dict[str, z3.BoolRef]]:
    length = len(movers)
    n = len(state_counts)
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

    for processor in range(n):
        for t in range(length):
            output_t = (
                config_vars[(t + 1) % length][processor]
                if movers[t] == processor
                else config_vars[t][processor]
            )
            left_t = config_vars[t][(processor - 1) % n]
            self_t = config_vars[t][processor]
            right_t = config_vars[t][(processor + 1) % n]
            for u in range(t + 1, length):
                output_u = (
                    config_vars[(u + 1) % length][processor]
                    if movers[u] == processor
                    else config_vars[u][processor]
                )
                left_u = config_vars[u][(processor - 1) % n]
                self_u = config_vars[u][processor]
                right_u = config_vars[u][(processor + 1) % n]
                same_context = z3.And(left_t == left_u, self_t == self_u, right_t == right_u)
                add_or_track(f"ctx_{processor}_{t}_{u}", z3.Implies(same_context, output_t == output_u))

    return solver, config_vars, tracked


def unsat_core_labels(state_counts: tuple[int, ...], movers: tuple[int, ...]) -> tuple[str, list[str]]:
    length = len(movers)
    solver, _, _ = build_seeded_cycle_core_solver(state_counts, movers, track_labels=True)
    status = solver.check()
    if status != z3.unsat:
        return str(status), []
    return str(status), [str(label) for label in solver.unsat_core()]


def summarize_unsat_core(state_counts: tuple[int, ...], movers: tuple[int, ...]) -> None:
    length = len(movers)
    n = len(state_counts)
    solver, config_vars, tracked = build_seeded_cycle_core_solver(state_counts, movers, track_labels=True)
    status = solver.check()
    print(f"status={status}")
    if status != z3.unsat:
        return

    core = [str(label) for label in solver.unsat_core()]
    print(f"core_size={len(core)}")
    print("context_labels:")
    for label in core:
        if label.startswith("ctx_"):
            print(f"  {label}")
    print("move_labels:")
    for label in core:
        if label.startswith("move_"):
            print(f"  {label}")
    print("other_labels:")
    for label in core:
        if not label.startswith("ctx_") and not label.startswith("move_"):
            print(f"  {label}")

    for label in core:
        parsed = parse_ctx_label(label)
        if parsed is None:
            continue
        processor, t, u = parsed
        witness = z3.Solver()
        for other_label in core:
            if other_label == label:
                continue
            witness.add(tracked[other_label])
        witness_status = witness.check()
        print(f"context_witness {label}: status={witness_status}")
        if witness_status != z3.sat:
            continue

        left_t = config_vars[t][(processor - 1) % n]
        self_t = config_vars[t][processor]
        right_t = config_vars[t][(processor + 1) % n]
        left_u = config_vars[u][(processor - 1) % n]
        self_u = config_vars[u][processor]
        right_u = config_vars[u][(processor + 1) % n]
        output_t = config_vars[(t + 1) % length][processor] if movers[t] == processor else config_vars[t][processor]
        output_u = config_vars[(u + 1) % length][processor] if movers[u] == processor else config_vars[u][processor]

        entries = [
            ("left_t", left_t),
            ("self_t", self_t),
            ("right_t", right_t),
            ("left_u", left_u),
            ("self_u", self_u),
            ("right_u", right_u),
            ("output_t", output_t),
            ("output_u", output_u),
        ]
        rendered = []
        for name, expr in entries:
            value = forced_value(witness, expr)
            rendered.append(f"{name}={value if value is not None else '?'}")
        print(f"  {' '.join(rendered)}")

        same_context_witness = z3.Solver()
        for other_label in core:
            if other_label == label:
                continue
            same_context_witness.add(tracked[other_label])
        same_context_witness.add(left_t == left_u, self_t == self_u, right_t == right_u, output_t != output_u)
        realized_status = same_context_witness.check()
        print(f"  realized_same_context status={realized_status}")
        if realized_status == z3.sat:
            realized_entries = []
            for name, expr in entries:
                domain = []
                if "left" in name or "right" in name:
                    index = (processor - 1) % n if "left" in name else (processor + 1) % n
                    domain = range(state_counts[index])
                else:
                    domain = range(state_counts[processor])
                values = []
                for value in domain:
                    same_context_witness.push()
                    same_context_witness.add(expr == value)
                    if same_context_witness.check() == z3.sat:
                        values.append(value)
                    same_context_witness.pop()
                realized_entries.append(f"{name}={values}")
            print(f"  {' '.join(realized_entries)}")


def realize_label_full(state_counts: tuple[int, ...], movers: tuple[int, ...], label: str) -> None:
    parsed = parse_ctx_label(label)
    if parsed is None:
        raise ValueError(f"expected a ctx label, got {label!r}")

    length = len(movers)
    n = len(state_counts)
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
            solver.add(z3.Or([config_vars[t][i] != config_vars[u][i] for i in range(n)]))

    processor, t, u = parsed
    output_t = config_vars[(t + 1) % length][processor] if movers[t] == processor else config_vars[t][processor]
    output_u = config_vars[(u + 1) % length][processor] if movers[u] == processor else config_vars[u][processor]
    left_t = config_vars[t][(processor - 1) % n]
    self_t = config_vars[t][processor]
    right_t = config_vars[t][(processor + 1) % n]
    left_u = config_vars[u][(processor - 1) % n]
    self_u = config_vars[u][processor]
    right_u = config_vars[u][(processor + 1) % n]

    for other_processor in range(n):
        for other_t in range(length):
            other_output_t = (
                config_vars[(other_t + 1) % length][other_processor]
                if movers[other_t] == other_processor
                else config_vars[other_t][other_processor]
            )
            other_left_t = config_vars[other_t][(other_processor - 1) % n]
            other_self_t = config_vars[other_t][other_processor]
            other_right_t = config_vars[other_t][(other_processor + 1) % n]
            for other_u in range(other_t + 1, length):
                if (other_processor, other_t, other_u) == parsed:
                    continue
                other_output_u = (
                    config_vars[(other_u + 1) % length][other_processor]
                    if movers[other_u] == other_processor
                    else config_vars[other_u][other_processor]
                )
                other_left_u = config_vars[other_u][(other_processor - 1) % n]
                other_self_u = config_vars[other_u][other_processor]
                other_right_u = config_vars[other_u][(other_processor + 1) % n]
                same_context = z3.And(
                    other_left_t == other_left_u,
                    other_self_t == other_self_u,
                    other_right_t == other_right_u,
                )
                solver.add(z3.Implies(same_context, other_output_t == other_output_u))

    solver.add(left_t == left_u, self_t == self_u, right_t == right_u, output_t != output_u)
    status = solver.check()
    print(f"full_realization {label}: status={status}")
    if status != z3.sat:
        return

    entries = [
        ("left_t", left_t),
        ("self_t", self_t),
        ("right_t", right_t),
        ("left_u", left_u),
        ("self_u", self_u),
        ("right_u", right_u),
        ("output_t", output_t),
        ("output_u", output_u),
    ]
    rendered = []
    for name, expr in entries:
        index = processor
        if "left" in name:
            index = (processor - 1) % n
        elif "right" in name:
            index = (processor + 1) % n
        values = []
        for value in range(state_counts[index]):
            solver.push()
            solver.add(expr == value)
            if solver.check() == z3.sat:
                values.append(value)
            solver.pop()
        rendered.append(f"{name}={values}")
    print(f"  {' '.join(rendered)}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--state-counts", default="2,3,3,3,3,3,3,3,2")
    parser.add_argument("--movers", required=True, help="comma-separated mover word")
    parser.add_argument("--realize-label", help="realize a specific ctx_p_t_u label against the full system")
    args = parser.parse_args()

    state_counts = parse_int_tuple(args.state_counts)
    movers = parse_int_tuple(args.movers)
    summarize_unsat_core(state_counts, movers)
    if args.realize_label:
        realize_label_full(state_counts, movers, args.realize_label)


if __name__ == "__main__":
    main()
