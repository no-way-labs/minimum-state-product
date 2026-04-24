#!/usr/bin/env python3
"""Probe cut-chain variation in mixed Sol-3 systems.

The main quantity is the linear variation after cutting the ring at P0:

    V(cfg) = |{ i in {0,...,n-2} : cfg[i] != cfg[i+1] }|

For the one-binary Sol-3-v1 family, this exposes a strong asymmetry:
the only processor that can increase V is the top endpoint P_{n-1}.
"""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from p2_ring import RingSystem, verify_system
from scripts.sol3_adapt import build_system, one_binary_family, sol3_adapt_v1


def parse_state_counts(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


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


def path_variation(cfg: tuple[int, ...]) -> int:
    return sum(1 for idx in range(len(cfg) - 1) if cfg[idx] != cfg[idx + 1])


def summarize_variation(system: RingSystem) -> dict[str, object]:
    delta_counts: Counter[int] = Counter()
    positive_movers: Counter[int] = Counter()
    positive_examples: dict[int, tuple[tuple[int, ...], int, tuple[int, ...], int]] = {}

    for cfg in system.iter_configs():
        before = path_variation(cfg)
        for mover, nxt in system.successors(cfg):
            delta = path_variation(nxt) - before
            delta_counts[delta] += 1
            if delta > 0:
                positive_movers[mover] += 1
                positive_examples.setdefault(mover, (cfg, mover, nxt, delta))

    summary: dict[str, object] = {
        "delta_counts": dict(sorted(delta_counts.items())),
        "positive_movers": dict(sorted(positive_movers.items())),
        "only_top_increases": all(mover == len(system.state_counts) - 1 for mover in positive_movers),
        "positive_examples": positive_examples,
    }

    try:
        cycle, movers = extract_good_cycle(system)
    except RuntimeError:
        summary["good_cycle_variations"] = None
        summary["good_cycle_movers"] = None
        return summary

    summary["good_cycle_variations"] = [path_variation(cfg) for cfg in cycle]
    summary["good_cycle_movers"] = movers
    return summary


def print_summary(label: str, system: RingSystem) -> None:
    verification = verify_system(system)
    summary = summarize_variation(system)
    print(f"{label}:")
    print(f"  state_counts={system.state_counts}")
    print(f"  valid={verification.valid} message={verification.message}")
    print(f"  path_variation_delta_counts={summary['delta_counts']}")
    print(f"  positive_variation_movers={summary['positive_movers']}")
    print(f"  only_top_increases={summary['only_top_increases']}")
    if summary["good_cycle_variations"] is not None:
        values = summary["good_cycle_variations"]
        print(f"  good_cycle_variation_values={sorted(set(values))}")
        print(f"  good_cycle_length={len(values)}")
    examples = summary["positive_examples"]
    for mover in sorted(examples):
        cfg, _, nxt, delta = examples[mover]
        print(f"  sample_positive_delta mover={mover} delta={delta} cfg={cfg} nxt={nxt}")


def canonical_cases() -> list[tuple[str, tuple[int, ...]]]:
    return [
        ("two_binary_adjacent", (2, 2, 3, 3, 3, 3, 3, 3, 3)),
        ("two_binary_separated", (2, 3, 3, 3, 2, 3, 3, 3, 3)),
        ("endpoint_binary_pair", (2, 3, 3, 3, 3, 3, 3, 3, 2)),
    ]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--mode",
        choices=("family", "canonical", "custom", "all"),
        default="all",
    )
    parser.add_argument("--n-min", type=int, default=5)
    parser.add_argument("--n-max", type=int, default=12)
    parser.add_argument(
        "--state-counts",
        action="append",
        help="comma-separated state counts for custom Sol-3-v1 probes",
    )
    args = parser.parse_args()

    if args.mode in {"family", "all"}:
        for n in range(args.n_min, args.n_max + 1):
            system = build_system(one_binary_family(n, 0), sol3_adapt_v1)
            print_summary(f"one_binary_n{n}", system)
            print()

    if args.mode in {"canonical", "all"}:
        for label, state_counts in canonical_cases():
            system = build_system(state_counts, sol3_adapt_v1)
            print_summary(label, system)
            print()

    if args.mode in {"custom", "all"} and args.state_counts:
        for idx, text in enumerate(args.state_counts):
            state_counts = parse_state_counts(text)
            system = build_system(state_counts, sol3_adapt_v1)
            print_summary(f"custom_{idx}", system)
            print()


if __name__ == "__main__":
    main()
