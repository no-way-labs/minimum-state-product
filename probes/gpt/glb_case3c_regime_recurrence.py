#!/usr/bin/env python3
"""Package canonical recurrence laws for the symbolic Case 3c regime families.

This lifts the representative-family recurrence work to the symbolic regimes
from M3. Each regime is represented by a canonical gap-pattern sequence:

- local_11k: (1,1,n-5)
- asymmetric_1ab: (1,2,n-6)
- semi_symmetric_2plus: (2,2,n-7)
- reverse_upper_trailing2: (1,n-6,2)

The script derives a tail-shift recurrence from consecutive n-values on the
canonical sequence, then verifies the law against direct forced-spine probes.
"""

from __future__ import annotations

import argparse
import os
import sys
from dataclasses import dataclass


REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(__file__))))
if REPO_ROOT not in sys.path:
    sys.path.insert(0, REPO_ROOT)

from probes.gpt.glb_case3c_forced_spine_probe import probe_summary_for_gaps
from probes.gpt.glb_case3c_gap_pattern_probe import symbolic_regime_label
from probes.gpt.glb_case3c_spine_shift_compare import shift_rule


AnchoredRule = tuple[str, tuple[int, int, int], int]
FamilyKey = tuple[str, bool]
RegimeKey = tuple[str, str, bool]


@dataclass(frozen=True)
class CanonicalRegimeSpec:
    label: str
    min_n: int
    supported_families: frozenset[FamilyKey]

    def gaps(self, n: int) -> tuple[int, int, int]:
        if n < self.min_n:
            raise ValueError(f"regime {self.label} requires n >= {self.min_n}")
        if self.label == "local_11k":
            return (1, 1, n - 5)
        if self.label == "asymmetric_1ab":
            return (1, 2, n - 6)
        if self.label == "semi_symmetric_2plus":
            return (2, 2, n - 7)
        if self.label == "reverse_upper_trailing2":
            return (1, n - 6, 2)
        raise ValueError(f"unsupported regime: {self.label}")


REGIME_SPECS: dict[str, CanonicalRegimeSpec] = {
    "local_11k": CanonicalRegimeSpec(
        label="local_11k",
        min_n=9,
        supported_families=frozenset(
            {
                ("reverse", False),
                ("forward", False),
                ("reverse", True),
                ("forward", True),
            }
        ),
    ),
    "asymmetric_1ab": CanonicalRegimeSpec(
        label="asymmetric_1ab",
        min_n=9,
        supported_families=frozenset(
            {
                ("reverse", False),
                ("forward", False),
                ("reverse", True),
                ("forward", True),
            }
        ),
    ),
    "semi_symmetric_2plus": CanonicalRegimeSpec(
        label="semi_symmetric_2plus",
        min_n=9,
        supported_families=frozenset(
            {
                ("reverse", False),
                ("forward", False),
                ("reverse", True),
                ("forward", True),
            }
        ),
    ),
    "reverse_upper_trailing2": CanonicalRegimeSpec(
        label="reverse_upper_trailing2",
        min_n=9,
        supported_families=frozenset({("reverse", True)}),
    ),
}


DEFAULT_BASE_N: dict[RegimeKey, int] = {
    ("local_11k", "reverse", False): 9,
    ("local_11k", "forward", False): 9,
    ("local_11k", "reverse", True): 9,
    ("local_11k", "forward", True): 9,
    ("asymmetric_1ab", "reverse", False): 9,
    ("asymmetric_1ab", "forward", False): 9,
    ("asymmetric_1ab", "reverse", True): 10,
    ("asymmetric_1ab", "forward", True): 11,
    ("semi_symmetric_2plus", "reverse", False): 9,
    ("semi_symmetric_2plus", "forward", False): 9,
    ("semi_symmetric_2plus", "reverse", True): 9,
    ("semi_symmetric_2plus", "forward", True): 9,
    ("reverse_upper_trailing2", "reverse", True): 9,
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
class RegimeLaw:
    regime_label: str
    orientation: str
    include_upper_wiggle: bool
    base_n: int
    base_gaps: tuple[int, int, int]
    base_spine: frozenset[AnchoredRule]
    losses: frozenset[AnchoredRule]
    gains: frozenset[AnchoredRule]
    cycle_selector: str
    assignment_mode: str
    derive_timeout_ms: int

    @property
    def family_name(self) -> str:
        return family_name(self.orientation, self.include_upper_wiggle)

    @property
    def size_slope(self) -> int:
        return len(self.gains) - len(self.losses)


def validate_regime_spec(
    spec: CanonicalRegimeSpec,
    orientation: str,
    include_upper_wiggle: bool,
    n: int,
) -> tuple[int, int, int]:
    family = (orientation, include_upper_wiggle)
    if family not in spec.supported_families:
        raise ValueError(f"regime {spec.label} does not support family {family_name(*family)}")

    gaps = spec.gaps(n)
    actual = symbolic_regime_label(gaps, orientation, include_upper_wiggle)
    if actual != spec.label:
        raise ValueError(
            f"canonical gaps {gaps} classify as {actual}, expected {spec.label} for "
            f"{family_name(orientation, include_upper_wiggle)}"
        )
    return gaps


def derive_law(
    regime_label: str,
    orientation: str,
    include_upper_wiggle: bool = False,
    base_n: int | None = None,
    timeout_ms: int = 1200,
    cycle_selector: str = "lexmin",
    assignment_mode: str = "actual_completion",
) -> RegimeLaw:
    spec = REGIME_SPECS[regime_label]
    if base_n is None:
        base_n = DEFAULT_BASE_N[(regime_label, orientation, include_upper_wiggle)]

    low_gaps = validate_regime_spec(spec, orientation, include_upper_wiggle, base_n)
    high_gaps = validate_regime_spec(spec, orientation, include_upper_wiggle, base_n + 1)
    low_summary = probe_summary_for_gaps(
        low_gaps,
        orientation,
        include_upper_wiggle,
        timeout_ms,
        cycle_selector,
        assignment_mode=assignment_mode,
    )
    high_summary = probe_summary_for_gaps(
        high_gaps,
        orientation,
        include_upper_wiggle,
        timeout_ms,
        cycle_selector,
        assignment_mode=assignment_mode,
    )

    if low_summary["missing_cycles"] or high_summary["missing_cycles"]:
        raise ValueError(
            f"cannot derive {regime_label}/{family_name(orientation, include_upper_wiggle)} "
            f"with missing cycles at n={base_n} or n={base_n + 1}"
        )

    low = frozenset(low_summary["normalized_common_spine_rules"])
    high = frozenset(high_summary["normalized_common_spine_rules"])
    shifted_low = frozenset(shift_rule(rule) for rule in low)
    losses = frozenset(shifted_low - high)
    gains = frozenset(high - shifted_low)

    return RegimeLaw(
        regime_label=regime_label,
        orientation=orientation,
        include_upper_wiggle=include_upper_wiggle,
        base_n=base_n,
        base_gaps=low_gaps,
        base_spine=low,
        losses=losses,
        gains=gains,
        cycle_selector=cycle_selector,
        assignment_mode=assignment_mode,
        derive_timeout_ms=timeout_ms,
    )


def generate_spine(n: int, law: RegimeLaw) -> frozenset[AnchoredRule]:
    if n < law.base_n:
        raise ValueError(f"n={n} is below base_n={law.base_n}")

    spine = law.base_spine
    for _ in range(law.base_n, n):
        shifted = frozenset(shift_rule(rule) for rule in spine)
        spine = frozenset((shifted - law.losses) | law.gains)
    return spine


def expected_size(n: int, law: RegimeLaw) -> int:
    if n < law.base_n:
        raise ValueError(f"n={n} is below base_n={law.base_n}")
    return len(law.base_spine) + (n - law.base_n) * law.size_slope


def verify_range(
    law: RegimeLaw,
    verify_to: int,
    verify_timeout_ms: int,
) -> list[dict[str, object]]:
    spec = REGIME_SPECS[law.regime_label]
    rows: list[dict[str, object]] = []
    for n in range(law.base_n, verify_to + 1):
        gaps = validate_regime_spec(spec, law.orientation, law.include_upper_wiggle, n)
        predicted = generate_spine(n, law)
        actual_summary = probe_summary_for_gaps(
            gaps,
            law.orientation,
            law.include_upper_wiggle,
            verify_timeout_ms,
            law.cycle_selector,
            assignment_mode=law.assignment_mode,
        )
        actual = frozenset(actual_summary["normalized_common_spine_rules"])
        rows.append(
            {
                "n": n,
                "gaps": gaps,
                "predicted_size": len(predicted),
                "expected_size": expected_size(n, law),
                "actual_size": len(actual),
                "match": predicted == actual,
                "missing_cycles": actual_summary["missing_cycles"],
            }
        )
    return rows


def print_law(law: RegimeLaw) -> None:
    print(
        f"regime={law.regime_label} family={law.family_name} base_n={law.base_n} "
        f"base_gaps={law.base_gaps} selector={law.cycle_selector} "
        f"assignment_mode={law.assignment_mode} "
        f"derive_timeout_ms={law.derive_timeout_ms}"
    )
    print(f"  base_size={len(law.base_spine)} size_slope={law.size_slope}")
    print(f"  losses={len(law.losses)} gains={len(law.gains)}")
    print(f"  loss_rules={sorted(law.losses)}")
    print(f"  gain_rules={sorted(law.gains)}")


def print_generation(end_n: int, law: RegimeLaw) -> None:
    spec = REGIME_SPECS[law.regime_label]
    print(f"generated sizes for regime={law.regime_label} family={law.family_name}")
    for n in range(law.base_n, end_n + 1):
        print(
            f"  n={n} gaps={validate_regime_spec(spec, law.orientation, law.include_upper_wiggle, n)} "
            f"size={len(generate_spine(n, law))} expected_size={expected_size(n, law)}"
        )


def print_verification(rows: list[dict[str, object]], law: RegimeLaw) -> None:
    print(f"verification for regime={law.regime_label} family={law.family_name}")
    for row in rows:
        print(
            f"  n={row['n']} gaps={row['gaps']} predicted={row['predicted_size']} "
            f"expected={row['expected_size']} actual={row['actual_size']} "
            f"match={row['match']} missing_cycles={row['missing_cycles']}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--regime",
        choices=tuple(sorted(REGIME_SPECS)) + ("all",),
        default="all",
    )
    parser.add_argument(
        "--family",
        choices=("reverse-base", "forward-base", "reverse-upper", "forward-upper", "base", "upper", "all"),
        default="all",
    )
    parser.add_argument("--end-n", type=int, default=20)
    parser.add_argument("--base-n", type=int, default=None)
    parser.add_argument("--derive-timeout-ms", type=int, default=1200)
    parser.add_argument("--verify-to", type=int, default=None)
    parser.add_argument("--verify-timeout-ms", type=int, default=5000)
    parser.add_argument("--cycle-selector", choices=("any", "lexmin"), default="lexmin")
    parser.add_argument(
        "--assignment-mode",
        choices=("predicted_completion", "actual_completion"),
        default="actual_completion",
    )
    args = parser.parse_args()

    regimes = tuple(sorted(REGIME_SPECS)) if args.regime == "all" else (args.regime,)
    families = iter_families(args.family)

    for regime_label in regimes:
        spec = REGIME_SPECS[regime_label]
        for orientation, include_upper_wiggle in families:
            if (orientation, include_upper_wiggle) not in spec.supported_families:
                continue
            law = derive_law(
                regime_label,
                orientation,
                include_upper_wiggle=include_upper_wiggle,
                base_n=args.base_n,
                timeout_ms=args.derive_timeout_ms,
                cycle_selector=args.cycle_selector,
                assignment_mode=args.assignment_mode,
            )
            print_law(law)
            print_generation(args.end_n, law)
            if args.verify_to is not None:
                rows = verify_range(law, args.verify_to, args.verify_timeout_ms)
                print_verification(rows, law)


if __name__ == "__main__":
    main()
