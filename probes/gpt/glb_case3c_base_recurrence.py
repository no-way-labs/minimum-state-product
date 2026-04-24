#!/usr/bin/env python3
"""Derive and apply the canonical base-family recurrence for true Case 3c.

This script packages the fixed edit laws observed under the lexmin selector:

- reverse base: shift plus a fixed 9-rule gain set
- forward base: shift, remove a fixed 5-rule loss set, add a fixed 14-rule gain set

The laws are derived from the `n = 9 -> 10` anchor and can then be applied
cheaply to generate predicted canonical spines for larger n.
"""

from __future__ import annotations

import argparse
import os
import sys
from dataclasses import dataclass


REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(__file__))))
if REPO_ROOT not in sys.path:
    sys.path.insert(0, REPO_ROOT)

from probes.gpt.glb_case3c_forced_spine_probe import probe_summary
from probes.gpt.glb_case3c_spine_shift_compare import shift_rule


AnchoredRule = tuple[str, tuple[int, int, int], int]


@dataclass(frozen=True)
class RecurrenceLaw:
    orientation: str
    base_n: int
    base_spine: frozenset[AnchoredRule]
    losses: frozenset[AnchoredRule]
    gains: frozenset[AnchoredRule]
    cycle_selector: str
    derive_timeout_ms: int

    @property
    def size_slope(self) -> int:
        return len(self.gains) - len(self.losses)


def derive_law(
    orientation: str,
    base_n: int = 9,
    timeout_ms: int = 1200,
    cycle_selector: str = "lexmin",
) -> RecurrenceLaw:
    low_summary = probe_summary(base_n, orientation, False, timeout_ms, cycle_selector)
    high_summary = probe_summary(base_n + 1, orientation, False, timeout_ms, cycle_selector)

    if low_summary["missing_cycles"] or high_summary["missing_cycles"]:
        raise ValueError(
            f"cannot derive {orientation} law with missing cycles at "
            f"n={base_n} or n={base_n + 1}"
        )

    low = frozenset(low_summary["normalized_common_spine_rules"])
    high = frozenset(high_summary["normalized_common_spine_rules"])
    shifted_low = frozenset(shift_rule(rule) for rule in low)
    losses = frozenset(shifted_low - high)
    gains = frozenset(high - shifted_low)

    return RecurrenceLaw(
        orientation=orientation,
        base_n=base_n,
        base_spine=low,
        losses=losses,
        gains=gains,
        cycle_selector=cycle_selector,
        derive_timeout_ms=timeout_ms,
    )


def generate_spine(n: int, law: RecurrenceLaw) -> frozenset[AnchoredRule]:
    if n < law.base_n:
        raise ValueError(f"n={n} is below base_n={law.base_n}")

    spine = law.base_spine
    for _ in range(law.base_n, n):
        shifted = frozenset(shift_rule(rule) for rule in spine)
        spine = frozenset((shifted - law.losses) | law.gains)
    return spine


def expected_size(n: int, law: RecurrenceLaw) -> int:
    if n < law.base_n:
        raise ValueError(f"n={n} is below base_n={law.base_n}")
    return len(law.base_spine) + (n - law.base_n) * law.size_slope


def verify_range(
    orientation: str,
    verify_to: int,
    derive_timeout_ms: int,
    verify_timeout_ms: int,
    cycle_selector: str,
) -> list[dict[str, object]]:
    law = derive_law(orientation, timeout_ms=derive_timeout_ms, cycle_selector=cycle_selector)
    rows: list[dict[str, object]] = []
    for n in range(law.base_n, verify_to + 1):
        predicted = generate_spine(n, law)
        actual_summary = probe_summary(n, orientation, False, verify_timeout_ms, cycle_selector)
        actual = frozenset(actual_summary["normalized_common_spine_rules"])
        rows.append(
            {
                "n": n,
                "predicted_size": len(predicted),
                "expected_size": expected_size(n, law),
                "actual_size": len(actual),
                "match": predicted == actual,
                "missing_cycles": actual_summary["missing_cycles"],
            }
        )
    return rows


def print_law(law: RecurrenceLaw) -> None:
    print(
        f"orientation={law.orientation} base_n={law.base_n} "
        f"selector={law.cycle_selector} derive_timeout_ms={law.derive_timeout_ms}"
    )
    print(f"  base_size={len(law.base_spine)} size_slope={law.size_slope}")
    print(f"  losses={len(law.losses)} gains={len(law.gains)}")
    print(f"  loss_rules={sorted(law.losses)}")
    print(f"  gain_rules={sorted(law.gains)}")


def print_generation(orientation: str, end_n: int, law: RecurrenceLaw) -> None:
    print(f"generated sizes for orientation={orientation}")
    for n in range(law.base_n, end_n + 1):
        print(f"  n={n} size={len(generate_spine(n, law))} expected_size={expected_size(n, law)}")


def print_verification(rows: list[dict[str, object]], orientation: str) -> None:
    print(f"verification for orientation={orientation}")
    for row in rows:
        print(
            f"  n={row['n']} predicted={row['predicted_size']} "
            f"expected={row['expected_size']} actual={row['actual_size']} "
            f"match={row['match']} missing_cycles={row['missing_cycles']}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--orientation", choices=("reverse", "forward", "both"), default="both")
    parser.add_argument("--end-n", type=int, default=20)
    parser.add_argument("--derive-timeout-ms", type=int, default=1200)
    parser.add_argument("--verify-to", type=int, default=None)
    parser.add_argument("--verify-timeout-ms", type=int, default=5000)
    parser.add_argument("--cycle-selector", choices=("any", "lexmin"), default="lexmin")
    args = parser.parse_args()

    orientations = ("reverse", "forward") if args.orientation == "both" else (args.orientation,)
    for orientation in orientations:
        law = derive_law(
            orientation,
            timeout_ms=args.derive_timeout_ms,
            cycle_selector=args.cycle_selector,
        )
        print_law(law)
        print_generation(orientation, args.end_n, law)
        if args.verify_to is not None:
            rows = verify_range(
                orientation,
                args.verify_to,
                args.derive_timeout_ms,
                args.verify_timeout_ms,
                args.cycle_selector,
            )
            print_verification(rows, orientation)


if __name__ == "__main__":
    main()
