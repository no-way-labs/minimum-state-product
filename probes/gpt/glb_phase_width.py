#!/usr/bin/env python3
"""Compute low-defect Z3 phase quotients on recurrent good cycles.

For a given witness system, we seek processor-local maps

    phi_i : states(P_i) -> Z/3Z

such that along the recurrent good cycle:

- all three phase values appear somewhere in the image, and
- each configuration has at most K defect edges
  (`phi_{i+1}(x_{i+1}) != phi_i(x_i)`), and
- the unique mover is adjacent to at least one defect edge.

The minimum feasible `K` is the phase-defect width of the chosen witness.
"""

from __future__ import annotations

import argparse
import os
import sys
from dataclasses import dataclass

import z3


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from p2_ring import RingSystem
from scripts import verify_witnesses as vw
from scripts.sol3_adapt import build_system, one_binary_family, sol3_adapt_v1


@dataclass(frozen=True)
class WidthResult:
    label: str
    state_counts: tuple[int, ...]
    min_width: int | None
    status: str


def extract_good_cycle(system: RingSystem) -> tuple[list[tuple[int, ...]], list[int]]:
    successors = {cfg: system.successors(cfg) for cfg in system.iter_configs()}
    for start in successors:
        path: list[tuple[int, ...]] = []
        position: dict[tuple[int, ...], int] = {}
        cur = start
        while cur not in position:
            position[cur] = len(path)
            path.append(cur)
            moves = successors[cur]
            if len(moves) != 1:
                break
            cur = moves[0][1]
        if cur not in position:
            continue
        cycle = path[position[cur] :]
        cycle_set = set(cycle)
        if cycle and all(len(successors[cfg]) == 1 and successors[cfg][0][1] in cycle_set for cfg in cycle):
            movers = [successors[cfg][0][0] for cfg in cycle]
            return cycle, movers
    raise RuntimeError("no recurrent single-successor cycle found")


def phase_width_status(system: RingSystem, width: int, timeout_ms: int, label: str) -> z3.CheckSatResult:
    state_counts = system.state_counts
    n = len(state_counts)
    cycle, movers = extract_good_cycle(system)
    phase_vars = {
        (processor, state): z3.Int(f"phi_{label}_{width}_{processor}_{state}")
        for processor, m in enumerate(state_counts)
        for state in range(m)
    }

    solver = z3.Solver()
    solver.set(timeout=timeout_ms)
    for var in phase_vars.values():
        solver.add(var >= 0, var <= 2)
    solver.add(phase_vars[(0, 0)] == 0)

    all_vars = list(phase_vars.values())
    solver.add(z3.Or(*[var == 1 for var in all_vars]))
    solver.add(z3.Or(*[var == 2 for var in all_vars]))

    for cfg, mover in zip(cycle, movers):
        defects = []
        for processor in range(n):
            left_phase = phase_vars[(processor, cfg[processor])]
            right_phase = phase_vars[((processor + 1) % n, cfg[(processor + 1) % n])]
            defects.append((right_phase - left_phase) % 3 != 0)
        solver.add(z3.PbLe([(defect, 1) for defect in defects], width))
        solver.add(z3.Or(defects[(mover - 1) % n], defects[mover]))

    return solver.check()


def compute_min_width(system: RingSystem, timeout_ms: int, label: str) -> WidthResult:
    for width in range(2, len(system.state_counts) + 1):
        status = phase_width_status(system, width, timeout_ms, label)
        if status == z3.sat:
            return WidthResult(label=label, state_counts=system.state_counts, min_width=width, status="sat")
        if status == z3.unknown:
            return WidthResult(label=label, state_counts=system.state_counts, min_width=None, status="unknown")
    return WidthResult(label=label, state_counts=system.state_counts, min_width=None, status="unsat")


def iter_named_systems(group: str) -> list[tuple[str, RingSystem]]:
    systems: list[tuple[str, RingSystem]] = []
    if group in {"small", "all"}:
        systems.extend(
            [
                ("n5_opt", RingSystem(*vw.witness_n5())),
                ("n6_opt", RingSystem(*vw.witness_n6())),
                ("n7_opt", RingSystem(*vw.witness_n7())),
                ("n8_opt", RingSystem(*vw.witness_n8())),
            ]
        )
    if group in {"family", "all"}:
        for n in range(5, 13):
            systems.append((f"one_binary_n{n}", build_system(one_binary_family(n, 0), sol3_adapt_v1)))
    return systems


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--group", choices=("small", "family", "all"), default="all")
    parser.add_argument("--timeout-ms", type=int, default=3000)
    args = parser.parse_args()

    for label, system in iter_named_systems(args.group):
        result = compute_min_width(system, args.timeout_ms, label)
        print(
            f"{result.label}: state_counts={result.state_counts} "
            f"min_width={result.min_width} status={result.status}"
        )


if __name__ == "__main__":
    main()
