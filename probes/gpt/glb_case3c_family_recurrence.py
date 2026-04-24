#!/usr/bin/env python3
"""Package canonical recurrence laws for the true Case 3c residue families.

This extends the base-family recurrence packaging to all four currently stable
lexmin families:

- reverse base, anchored at n = 9
- forward base, anchored at n = 9
- reverse upper-wiggle, anchored at n = 10
- forward upper-wiggle, anchored at n = 11
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
FamilyKey = tuple[str, bool]


DEFAULT_BASE_N: dict[FamilyKey, int] = {
    ("reverse", False): 9,
    ("forward", False): 9,
    ("reverse", True): 10,
    ("forward", True): 11,
}


def family_name(orientation: str, include_upper_wiggle: bool) -> str:
    return f"{orientation}_{'upper' if include_upper_wiggle else 'base'}"


def parse_family_name(text: str) -> FamilyKey:
    families = {
        "reverse-base": ("reverse", False),
        "forward-base": ("forward", False),
        "reverse-upper": ("reverse", True),
        "forward-upper": ("forward", True),
    }
    try:
        return families[text]
    except KeyError as exc:
        raise ValueError(f"unsupported family: {text}") from exc


def iter_families(selection: str) -> tuple[FamilyKey, ...]:
    if selection == "all":
        return (
            ("reverse", False),
            ("forward", False),
            ("reverse", True),
            ("forward", True),
        )
    if selection == "base":
        return (("reverse", False), ("forward", False))
    if selection == "upper":
        return (("reverse", True), ("forward", True))
    return (parse_family_name(selection),)


@dataclass(frozen=True)
class RecurrenceLaw:
    orientation: str
    include_upper_wiggle: bool
    base_n: int
    base_spine: frozenset[AnchoredRule]
    losses: frozenset[AnchoredRule]
    gains: frozenset[AnchoredRule]
    cycle_selector: str
    derive_timeout_ms: int

    @property
    def family_name(self) -> str:
        return family_name(self.orientation, self.include_upper_wiggle)

    @property
    def size_slope(self) -> int:
        return len(self.gains) - len(self.losses)


def derive_law(
    orientation: str,
    include_upper_wiggle: bool = False,
    base_n: int | None = None,
    timeout_ms: int = 1200,
    cycle_selector: str = "lexmin",
) -> RecurrenceLaw:
    if base_n is None:
        base_n = DEFAULT_BASE_N[(orientation, include_upper_wiggle)]

    low_summary = probe_summary(base_n, orientation, include_upper_wiggle, timeout_ms, cycle_selector)
    high_summary = probe_summary(
        base_n + 1, orientation, include_upper_wiggle, timeout_ms, cycle_selector
    )

    if low_summary["missing_cycles"] or high_summary["missing_cycles"]:
        raise ValueError(
            f"cannot derive {family_name(orientation, include_upper_wiggle)} law with missing "
            f"cycles at n={base_n} or n={base_n + 1}"
        )

    low = frozenset(low_summary["normalized_common_spine_rules"])
    high = frozenset(high_summary["normalized_common_spine_rules"])
    shifted_low = frozenset(shift_rule(rule) for rule in low)
    losses = frozenset(shifted_low - high)
    gains = frozenset(high - shifted_low)

    return RecurrenceLaw(
        orientation=orientation,
        include_upper_wiggle=include_upper_wiggle,
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
    law: RecurrenceLaw,
    verify_to: int,
    verify_timeout_ms: int,
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for n in range(law.base_n, verify_to + 1):
        predicted = generate_spine(n, law)
        actual_summary = probe_summary(
            n,
            law.orientation,
            law.include_upper_wiggle,
            verify_timeout_ms,
            law.cycle_selector,
        )
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
        f"family={law.family_name} base_n={law.base_n} selector={law.cycle_selector} "
        f"derive_timeout_ms={law.derive_timeout_ms}"
    )
    print(f"  base_size={len(law.base_spine)} size_slope={law.size_slope}")
    print(f"  losses={len(law.losses)} gains={len(law.gains)}")
    print(f"  loss_rules={sorted(law.losses)}")
    print(f"  gain_rules={sorted(law.gains)}")


def print_generation(end_n: int, law: RecurrenceLaw) -> None:
    print(f"generated sizes for family={law.family_name}")
    for n in range(law.base_n, end_n + 1):
        print(f"  n={n} size={len(generate_spine(n, law))} expected_size={expected_size(n, law)}")


def print_verification(rows: list[dict[str, object]], family: str) -> None:
    print(f"verification for family={family}")
    for row in rows:
        print(
            f"  n={row['n']} predicted={row['predicted_size']} "
            f"expected={row['expected_size']} actual={row['actual_size']} "
            f"match={row['match']} missing_cycles={row['missing_cycles']}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--family",
        choices=("reverse-base", "forward-base", "reverse-upper", "forward-upper", "base", "upper", "all"),
        default="all",
    )
    parser.add_argument("--end-n", type=int, default=20)
    parser.add_argument("--derive-timeout-ms", type=int, default=1200)
    parser.add_argument("--verify-to", type=int, default=None)
    parser.add_argument("--verify-timeout-ms", type=int, default=5000)
    parser.add_argument("--cycle-selector", choices=("any", "lexmin"), default="lexmin")
    args = parser.parse_args()

    for orientation, include_upper_wiggle in iter_families(args.family):
        law = derive_law(
            orientation,
            include_upper_wiggle=include_upper_wiggle,
            timeout_ms=args.derive_timeout_ms,
            cycle_selector=args.cycle_selector,
        )
        print_law(law)
        print_generation(args.end_n, law)
        if args.verify_to is not None:
            rows = verify_range(law, args.verify_to, args.verify_timeout_ms)
            print_verification(rows, law.family_name)


if __name__ == "__main__":
    main()
