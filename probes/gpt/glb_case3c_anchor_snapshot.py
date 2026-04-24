#!/usr/bin/env python3
"""Emit exact canonical anchor data for the current Case 3c regime catalogue."""

from __future__ import annotations

import argparse
import os
import sys
from dataclasses import dataclass


REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(__file__))))
if REPO_ROOT not in sys.path:
    sys.path.insert(0, REPO_ROOT)

from probes.gpt.glb_case3c_regime_recurrence import derive_law
from probes.gpt.glb_case3c_template_catalogue import CASES, template_for_case


AnchoredRule = tuple[str, tuple[int, int, int], int]


@dataclass(frozen=True)
class SnapshotCase:
    regime_label: str
    orientation: str
    include_upper_wiggle: bool
    base_n: int

    @property
    def family(self) -> str:
        return f"{self.orientation}_{'upper' if self.include_upper_wiggle else 'base'}"

    @property
    def case_id(self) -> str:
        return f"{self.regime_label}/{self.family}"


def iter_snapshot_cases() -> tuple[SnapshotCase, ...]:
    return tuple(
        SnapshotCase(
            regime_label=case.regime_label,
            orientation=case.orientation,
            include_upper_wiggle=case.include_upper_wiggle,
            base_n=case.base_n,
        )
        for case in CASES
    )


def select_cases(
    case_ids: set[str],
    regimes: set[str],
    families: set[str],
) -> tuple[SnapshotCase, ...]:
    selected: list[SnapshotCase] = []
    for case in iter_snapshot_cases():
        if case_ids and case.case_id not in case_ids:
            continue
        if regimes and case.regime_label not in regimes:
            continue
        if families and case.family not in families:
            continue
        selected.append(case)
    return tuple(selected)


def emit_python_entry(case: SnapshotCase, timeout_ms: int, cycle_selector: str) -> None:
    law = derive_law(
        case.regime_label,
        case.orientation,
        case.include_upper_wiggle,
        base_n=case.base_n,
        timeout_ms=timeout_ms,
        cycle_selector=cycle_selector,
        assignment_mode="actual_completion",
    )
    template_id = template_for_case(case.regime_label, case.orientation, case.include_upper_wiggle)
    print(
        "    "
        f"({case.regime_label!r}, {case.orientation!r}, {case.include_upper_wiggle!r}): "
        "StaticAnchor("
    )
    print(f"        regime_label={case.regime_label!r},")
    print(f"        orientation={case.orientation!r},")
    print(f"        include_upper_wiggle={case.include_upper_wiggle!r},")
    print(f"        base_n={case.base_n},")
    print(f"        base_gaps={law.base_gaps!r},")
    print(f"        template_id={template_id!r},")
    print(f"        base_spine=frozenset({sorted(law.base_spine)!r}),")
    print("    ),")


def emit_summary(case: SnapshotCase, timeout_ms: int, cycle_selector: str) -> None:
    law = derive_law(
        case.regime_label,
        case.orientation,
        case.include_upper_wiggle,
        base_n=case.base_n,
        timeout_ms=timeout_ms,
        cycle_selector=cycle_selector,
        assignment_mode="actual_completion",
    )
    template_id = template_for_case(case.regime_label, case.orientation, case.include_upper_wiggle)
    print(
        f"case={case.case_id} template={template_id} base_n={case.base_n} "
        f"base_gaps={law.base_gaps} base_size={len(law.base_spine)}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case-id", action="append", default=[])
    parser.add_argument("--regime", action="append", default=[])
    parser.add_argument("--family", action="append", default=[])
    parser.add_argument("--mode", choices=("summary", "python"), default="summary")
    parser.add_argument("--timeout-ms", type=int, default=1200)
    parser.add_argument("--cycle-selector", choices=("any", "lexmin"), default="lexmin")
    args = parser.parse_args()

    selected = select_cases(
        set(args.case_id),
        set(args.regime),
        set(args.family),
    )
    if not selected:
        raise SystemExit("no matching cases")

    for case in selected:
        if args.mode == "python":
            emit_python_entry(case, args.timeout_ms, args.cycle_selector)
        else:
            emit_summary(case, args.timeout_ms, args.cycle_selector)


if __name__ == "__main__":
    main()
