#!/usr/bin/env python3
"""Phase-oriented probes for the token-ring lower-bound investigation.

This is not a search script. It extracts a few proof-facing summaries:

- the exact recurrent cycle of the one-binary Sol-3 witness
- distances from binary processors to larger-state "support" processors
  in the known small optimal witnesses
- canonical two-binary boundary-family failures under Sol-3-v1
"""

from __future__ import annotations

import argparse
import os
import sys
from typing import Iterable


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from p2_ring import RingSystem, verify_system
from scripts.sol3_adapt import build_system, one_binary_family, sol3_adapt_v1
from scripts import verify_witnesses as vw


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


def print_step_summary(n: int) -> None:
    system = build_system(one_binary_family(n, 0), sol3_adapt_v1)
    cycle, movers = extract_good_cycle(system)
    print(f"one-binary Sol-3-v1, n={n}, state_counts={system.state_counts}")
    print(f"cycle_length={len(cycle)}")
    print(f"movers={movers}")
    for idx, cfg in enumerate(cycle):
        print(f"{idx:02d} mover={movers[idx]} cfg={cfg}")
    print()
    print("unique mover contexts by processor:")
    for processor in range(n):
        seen: list[tuple[tuple[int, int, int], int]] = []
        for cfg, mover in zip(cycle, movers):
            if mover != processor:
                continue
            left = cfg[(processor - 1) % n]
            self_state = cfg[processor]
            right = cfg[(processor + 1) % n]
            next_cfg = system.successor_for_processor(cfg, processor)
            assert next_cfg is not None
            item = ((left, self_state, right), next_cfg[processor])
            if item not in seen:
                seen.append(item)
        print(f"  P{processor} m={system.state_counts[processor]} contexts={seen}")


def witness_catalog() -> Iterable[tuple[str, tuple[int, ...], tuple[dict, ...]]]:
    for label, fn in (
        ("n5", vw.witness_n5),
        ("n6", vw.witness_n6),
        ("n7", vw.witness_n7),
        ("n8", vw.witness_n8),
    ):
        yield (label, *fn())


def ring_distance(i: int, j: int, n: int) -> int:
    return min((i - j) % n, (j - i) % n)


def print_support_summary() -> None:
    print("known small witnesses: binary distance to any processor with >=4 states")
    for label, state_counts, rules in witness_catalog():
        _ = rules
        n = len(state_counts)
        binaries = [i for i, m in enumerate(state_counts) if m == 2]
        support = [i for i, m in enumerate(state_counts) if m >= 4]
        distances = []
        for binary in binaries:
            best = min(ring_distance(binary, sup, n) for sup in support) if support else None
            distances.append((binary, best))
        print(f"{label} state_counts={state_counts} support={support} binary_distances={distances}")


def print_two_binary_probe() -> None:
    cases = [
        (2, 2, 3, 3, 3, 3, 3, 3, 3),
        (2, 3, 3, 3, 2, 3, 3, 3, 3),
        (2, 3, 3, 3, 3, 3, 3, 3, 2),
    ]
    print("canonical product-8748 two-binary probes under Sol-3-v1")
    for state_counts in cases:
        system = build_system(state_counts, sol3_adapt_v1)
        result = verify_system(system)
        print(
            f"state_counts={state_counts} valid={result.valid} "
            f"message={result.message}"
        )
        if "branching configuration:" in result.message:
            text = result.message.split("branching configuration:", 1)[1].strip()
            cfg = tuple(int(part.strip()) for part in text.strip("()").split(","))
            print(f"  privileged_moves={system.successors(cfg)}")


def cyclic_chains(n: int, start: int, end: int) -> list[list[int]]:
    forward = [start]
    cur = start
    while cur != end:
        cur = (cur + 1) % n
        forward.append(cur)

    backward = [start]
    cur = start
    while cur != end:
        cur = (cur - 1) % n
        backward.append(cur)

    return [forward, backward]


def print_support_chain_summary() -> None:
    print("minimal quaternary-zone radius whose mover chains cover every binary move")
    for label, state_counts, rules in witness_catalog():
        system = RingSystem(state_counts=state_counts, rules=rules)
        _, movers = extract_good_cycle(system)
        n = len(state_counts)
        support = [i for i, m in enumerate(state_counts) if m >= 4]
        binaries = [i for i, m in enumerate(state_counts) if m == 2 and i != 0]
        if len(support) != 1:
            print(f"{label} state_counts={state_counts} requires a unique >=4-state processor")
            continue
        support_proc = support[0]
        answer = None
        for radius in range(n):
            zone = {(support_proc + offset) % n for offset in range(-radius, radius + 1)}
            all_moves_covered = True
            for binary in binaries:
                binary_steps = [step for step, mover in enumerate(movers) if mover == binary]
                for step in binary_steps:
                    covered = False
                    for start in zone:
                        for chain in cyclic_chains(n, start, binary):
                            length = len(chain)
                            segment = [movers[(step - length + 1 + idx) % len(movers)] for idx in range(length)]
                            if segment == chain:
                                covered = True
                                break
                        if covered:
                            break
                    if not covered:
                        all_moves_covered = False
                        break
                if not all_moves_covered:
                    break
            if all_moves_covered:
                answer = radius
                break
        print(
            f"{label} state_counts={state_counts} support={support_proc} "
            f"binary_moves={binaries} min_support_chain_radius={answer}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--mode",
        choices=("step", "support", "support-chains", "two-binary", "all"),
        default="all",
    )
    parser.add_argument("--n", type=int, default=9, help="ring size for --mode step")
    args = parser.parse_args()

    if args.mode in {"step", "all"}:
        print_step_summary(args.n)
        print()
    if args.mode in {"support", "all"}:
        print_support_summary()
        print()
    if args.mode in {"support-chains", "all"}:
        print_support_chain_summary()
        print()
    if args.mode in {"two-binary", "all"}:
        print_two_binary_probe()


if __name__ == "__main__":
    main()
