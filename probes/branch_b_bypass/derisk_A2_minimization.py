#!/usr/bin/env python3
"""A2 derisk check: exhaustive n=5 cycle enumeration for ms=(2,2,2,3,3).

The plan asks for:
1. Enumerate all good cycles in the M5 family.
2. Check whether every cycle is at min-CL, meaning fc[p] = m[p].
3. If higher-fc cycles exist, test whether any admit an exact min-CL subcycle
   of length sum(m) with fire-count vector equal to m.

This script reuses the existing good-cycle enumerator rather than rebuilding
the search.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[2]
GPT_SCRIPTS = ROOT / "gpt" / "scripts"
sys.path.insert(0, str(GPT_SCRIPTS))

from p2_good_cycle_search import enumerate_good_cycles  # type: ignore


STATE_COUNTS = (2, 2, 2, 3, 3)
N = len(STATE_COUNTS)
MIN_CL = sum(STATE_COUNTS)
MAX_DEPTH = 1
for _m in STATE_COUNTS:
    MAX_DEPTH *= _m


@dataclass(frozen=True)
class CycleSummary:
    fire_counts: tuple[int, ...]
    length: int
    cw_steps: int
    ccw_steps: int
    stay_steps: int
    mover_word: tuple[int, ...]


def step_counts(word: tuple[int, ...]) -> tuple[int, int, int]:
    cw = 0
    ccw = 0
    for idx, mover in enumerate(word):
        nxt = word[(idx + 1) % len(word)]
        delta = (nxt - mover) % N
        if delta == 1:
            cw += 1
        elif delta == N - 1:
            ccw += 1
    stay = len(word) - cw - ccw
    return cw, ccw, stay


def fire_counts(word: tuple[int, ...]) -> tuple[int, ...]:
    counts = [0] * N
    for mover in word:
        counts[mover] += 1
    return tuple(counts)


def is_zero_winding_cwpos(summary: CycleSummary) -> bool:
    return summary.cw_steps == summary.ccw_steps and summary.cw_steps > 0


def window_is_exact_min_cycle(
    cycle: tuple[tuple[int, ...], ...], movers: tuple[int, ...], start: int
) -> tuple[bool, tuple[int, ...] | None]:
    """Check whether a length-MIN_CL window is an exact min-CL good subcycle."""
    if len(movers) < MIN_CL:
        return False, None

    start_cfg = cycle[start]
    seen = {start_cfg}
    fc = [0] * N
    window_word = []

    for offset in range(MIN_CL):
        mover = movers[(start + offset) % len(movers)]
        window_word.append(mover)
        fc[mover] += 1
        nxt_cfg = cycle[(start + offset + 1) % len(cycle)]
        if offset + 1 < MIN_CL:
            if nxt_cfg in seen:
                return False, None
            seen.add(nxt_cfg)
        elif nxt_cfg != start_cfg:
            return False, None

    if tuple(fc) != STATE_COUNTS:
        return False, None
    if any(count == 0 for count in fc):
        return False, None
    return True, tuple(window_word)


def summarize_cycle(movers: tuple[int, ...]) -> CycleSummary:
    cw, ccw, stay = step_counts(movers)
    return CycleSummary(
        fire_counts=fire_counts(movers),
        length=len(movers),
        cw_steps=cw,
        ccw_steps=ccw,
        stay_steps=stay,
        mover_word=movers,
    )


def main() -> None:
    total_good_cycles = 0
    min_cl_cycles = 0
    zero_winding_cwpos_cycles = 0
    zero_winding_cwpos_min_cl_cycles = 0

    higher_fc_by_vector: dict[tuple[int, ...], int] = defaultdict(int)
    low_fc_off_min_by_vector: dict[tuple[int, ...], int] = defaultdict(int)
    higher_fc_reducible = 0
    higher_fc_irreducible = 0
    representative_higher_fc: CycleSummary | None = None

    for cycle, movers in enumerate_good_cycles(
        STATE_COUNTS,
        max_depth=MAX_DEPTH,
        max_cycles=None,
        time_limit=None,
    ):
        total_good_cycles += 1
        summary = summarize_cycle(movers)

        if summary.fire_counts == STATE_COUNTS:
            min_cl_cycles += 1
        elif any(fc > bound for fc, bound in zip(summary.fire_counts, STATE_COUNTS, strict=True)):
            higher_fc_by_vector[summary.fire_counts] += 1
            if representative_higher_fc is None:
                representative_higher_fc = summary

            reducible = False
            for start in range(summary.length):
                ok, _window = window_is_exact_min_cycle(cycle, movers, start)
                if ok:
                    reducible = True
                    break
            if reducible:
                higher_fc_reducible += 1
            else:
                higher_fc_irreducible += 1
        else:
            low_fc_off_min_by_vector[summary.fire_counts] += 1

        if is_zero_winding_cwpos(summary):
            zero_winding_cwpos_cycles += 1
            if summary.fire_counts == STATE_COUNTS:
                zero_winding_cwpos_min_cl_cycles += 1

    higher_fc_total = sum(higher_fc_by_vector.values())
    low_fc_off_min_total = sum(low_fc_off_min_by_vector.values())

    if higher_fc_total == 0:
        reducible_status = "yes"
    elif higher_fc_irreducible == 0:
        reducible_status = "yes"
    elif higher_fc_reducible == 0:
        reducible_status = "no"
    else:
        reducible_status = "partial"

    verdict = "pass" if total_good_cycles == min_cl_cycles else "fail"

    higher_fc_list = [
        {"fc": list(fc_vec), "count": count}
        for fc_vec, count in sorted(higher_fc_by_vector.items(), key=lambda item: (sum(item[0]), item[0]))
    ]
    low_fc_list = [
        {"fc": list(fc_vec), "count": count}
        for fc_vec, count in sorted(low_fc_off_min_by_vector.items(), key=lambda item: (sum(item[0]), item[0]))
    ]

    print(f"A2 tested families: {[list(STATE_COUNTS)]}")
    print(f"A2 total good cycles found: {total_good_cycles}")
    print(f"A2 good cycles at min-CL: {min_cl_cycles}")
    print(f"A2 higher-fc cycles (if any): {higher_fc_list}")
    print(f"A2 reducible to min-CL: {reducible_status}")
    print(f"A2 verdict: {verdict}")
    print()
    print("Supporting notes:")
    print(f"- Exact min-CL target: fc = {list(STATE_COUNTS)}, cycle length = {MIN_CL}")
    print(f"- Higher-fc cycles: {higher_fc_total}")
    print(f"- Higher-fc cycles reducible to an exact min-CL subcycle: {higher_fc_reducible}/{higher_fc_total}")
    print(f"- Off-min-CL cycles with no coordinate above m: {low_fc_off_min_total}")
    if low_fc_list:
        print(f"- Off-min-CL low-fc vectors: {low_fc_list}")
    print(f"- Zero-winding with cwStepCount > 0 cycles in this family: {zero_winding_cwpos_cycles}")
    print(f"- Zero-winding with cwStepCount > 0 cycles already at min-CL: {zero_winding_cwpos_min_cl_cycles}")
    if representative_higher_fc is not None:
        print(
            "- Representative irreducible higher-fc cycle: "
            f"fc={list(representative_higher_fc.fire_counts)}, "
            f"L={representative_higher_fc.length}, "
            f"(cw,ccw,stay)=({representative_higher_fc.cw_steps},"
            f"{representative_higher_fc.ccw_steps},{representative_higher_fc.stay_steps}), "
            f"word={list(representative_higher_fc.mover_word)}"
        )


if __name__ == "__main__":
    main()
