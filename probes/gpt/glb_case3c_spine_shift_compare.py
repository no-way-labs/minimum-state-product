#!/usr/bin/env python3
"""Compare forced singleton spines across neighboring n via tail-shift embedding.

The default comparison uses cycle-normalized forced spines, since raw anchored
rules are solver-label dependent on some branches.
"""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from scripts.glb_case3c_fragment_anatomy import assignment_records, summarize_completion_fragments
from scripts.glb_case3c_starpower_probe import family_spec, representative_case3c_state_counts


AnchoredRule = tuple[str, tuple[int, int, int], int]


def shifted_tail_label(label: str) -> str:
    if label.startswith("Q-"):
        return f"Q-{int(label[2:]) + 1}"
    if label == "Q":
        return "Q-1"
    return label


def shift_rule(rule: AnchoredRule) -> AnchoredRule:
    label, ctx, out_state = rule
    return shifted_tail_label(label), ctx, out_state


def forced_common_spine(
    n: int,
    orientation: str,
    include_upper_wiggle: bool,
    timeout_ms: int,
    use_raw: bool,
) -> set[AnchoredRule]:
    state_counts = representative_case3c_state_counts(n)
    interior_edges, tail = family_spec(n, orientation, include_upper_wiggle)
    records = assignment_records(state_counts, interior_edges, orientation, tail, timeout_ms)
    summary = summarize_completion_fragments(records, state_counts)
    key = "forced_common_spine_rules" if use_raw else "normalized_forced_common_spine_rules"
    return set(summary[key])


def print_comparison(
    n_lo: int,
    n_hi: int,
    orientation: str,
    include_upper_wiggle: bool,
    timeout_ms: int,
    use_raw: bool,
) -> None:
    if n_hi != n_lo + 1:
        raise ValueError("comparison is defined for neighboring n values only")

    low = forced_common_spine(n_lo, orientation, include_upper_wiggle, timeout_ms, use_raw)
    high = forced_common_spine(n_hi, orientation, include_upper_wiggle, timeout_ms, use_raw)
    shifted_low = {shift_rule(rule) for rule in low}

    preserved = shifted_low & high
    lost = shifted_low - high
    gained = high - shifted_low

    def processor_hist(rules: set[AnchoredRule]) -> dict[str, int]:
        return dict(sorted(Counter(label for label, _, _ in rules).items()))

    print(
        f"n_lo={n_lo} n_hi={n_hi} orientation={orientation} "
        f"upper_wiggle={'yes' if include_upper_wiggle else 'no'} "
        f"mode={'raw' if use_raw else 'normalized'}"
    )
    print(f"  low_size={len(low)} shifted_low_size={len(shifted_low)} high_size={len(high)}")
    print(f"  preserved={len(preserved)} lost={len(lost)} gained={len(gained)}")
    print(f"  preserved_hist={processor_hist(preserved)}")
    print(f"  lost_hist={processor_hist(lost)}")
    print(f"  gained_hist={processor_hist(gained)}")
    print(f"  sample_preserved={sorted(preserved)[:12]}")
    print(f"  sample_lost={sorted(lost)[:12]}")
    print(f"  sample_gained={sorted(gained)[:12]}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-lo", type=int, required=True)
    parser.add_argument("--n-hi", type=int, required=True)
    parser.add_argument("--orientation", choices=("reverse", "forward", "both"), default="both")
    parser.add_argument("--include-upper-wiggle", action="store_true")
    parser.add_argument("--timeout-ms", type=int, default=1200)
    parser.add_argument("--raw", action="store_true", help="use raw anchored rules instead of normalized spines")
    args = parser.parse_args()

    orientations = ("reverse", "forward") if args.orientation == "both" else (args.orientation,)
    for orientation in orientations:
        print_comparison(
            args.n_lo,
            args.n_hi,
            orientation,
            args.include_upper_wiggle,
            args.timeout_ms,
            args.raw,
        )


if __name__ == "__main__":
    main()
