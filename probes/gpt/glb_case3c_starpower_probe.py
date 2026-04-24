#!/usr/bin/env python3
"""Probe whether the observed n=9 three-sweep residue rules persist for larger n.

This is not a proof engine. It tests the strongest candidate all-n rule that the
L=33/L=35 notes suggest on the representative true Case 3c family:

- reverse tail08 residue: bottom wiggle in first reverse sweep => local UNSAT,
  otherwise completion UNSAT;
- forward tail01 residue: bottom wiggle in first forward sweep => completion
  UNSAT, otherwise local UNSAT.

The representative architecture is:
    (2,3,2,3,3,2,3,...,3,4)
with binaries at 0,2,5 and a quaternary at n-1.
"""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from scripts.glb_three_sweep_assignment_scan import assignment_rows


def parse_int_tuple(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def representative_case3c_state_counts(n: int) -> tuple[int, ...]:
    if n < 9:
        raise ValueError("representative true Case 3c family requires n >= 9")
    return (2, 3, 2, 3, 3, 2) + (3,) * (n - 7) + (4,)


def predicted_status(orientation: str, assignment: tuple[int, ...]) -> str:
    bottom_slot = assignment[0]
    if orientation == "reverse":
        return "seed_unsat" if bottom_slot == 0 else "completion_unsat"
    if orientation == "forward":
        return "completion_unsat" if bottom_slot == 0 else "seed_unsat"
    raise ValueError(f"unsupported orientation: {orientation}")


def family_spec(n: int, orientation: str, include_upper_wiggle: bool) -> tuple[tuple[int, ...], tuple[int, ...]]:
    if orientation == "reverse":
        interior_edges = (1, 4) + ((n - 2,) if include_upper_wiggle else ())
        tail = (0, n - 1)
        return interior_edges, tail
    if orientation == "forward":
        interior_edges = (2, 5) + ((n - 2,) if include_upper_wiggle else ())
        tail = (0, 1)
        return interior_edges, tail
    raise ValueError(f"unsupported orientation: {orientation}")


def run_family(
    n: int,
    orientation: str,
    include_upper_wiggle: bool,
    timeout_ms: int,
) -> dict[str, object]:
    state_counts = representative_case3c_state_counts(n)
    interior_edges, tail = family_spec(n, orientation, include_upper_wiggle)
    rows = assignment_rows(state_counts, interior_edges, orientation, tail, timeout_ms)

    mismatches: list[tuple[tuple[int, ...], str, str, int | None]] = []
    fragment_counter: Counter[tuple[str, int | None]] = Counter()
    for assignment, _, status, fragment_size in rows:
        predicted = predicted_status(orientation, assignment)
        fragment_counter[(status, fragment_size)] += 1
        if status != predicted:
            mismatches.append((assignment, predicted, status, fragment_size))

    return {
        "n": n,
        "orientation": orientation,
        "include_upper_wiggle": include_upper_wiggle,
        "state_counts": state_counts,
        "interior_edges": interior_edges,
        "tail": tail,
        "fragment_counter": dict(sorted(fragment_counter.items(), key=str)),
        "mismatches": mismatches,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-values", default="9,10,11,12")
    parser.add_argument(
        "--orientation",
        choices=("reverse", "forward", "both"),
        default="both",
    )
    parser.add_argument("--include-upper-wiggle", action="store_true")
    parser.add_argument("--timeout-ms", type=int, default=1500)
    args = parser.parse_args()

    n_values = parse_int_tuple(args.n_values)
    orientations = ("reverse", "forward") if args.orientation == "both" else (args.orientation,)

    for n in n_values:
        for orientation in orientations:
            result = run_family(
                n=n,
                orientation=orientation,
                include_upper_wiggle=args.include_upper_wiggle,
                timeout_ms=args.timeout_ms,
            )
            print(
                f"n={result['n']} orientation={result['orientation']} "
                f"upper_wiggle={'yes' if result['include_upper_wiggle'] else 'no'}"
            )
            print(f"  state_counts={result['state_counts']}")
            print(f"  interior_edges={result['interior_edges']} tail={result['tail']}")
            print(f"  summary={result['fragment_counter']}")
            print(f"  mismatches={len(result['mismatches'])}")
            for assignment, predicted, actual, fragment_size in result["mismatches"][:8]:
                print(
                    f"    assignment={assignment} predicted={predicted} "
                    f"actual={actual} fragment_size={fragment_size}"
                )


if __name__ == "__main__":
    main()
