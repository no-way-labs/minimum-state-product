from __future__ import annotations

import argparse
import os
import sys
from itertools import product

sys.path.append(os.path.dirname(os.path.dirname(__file__)))

from p2_ring import RingSystem
from scripts import verify_witnesses as vw
from scripts.family_tail_search import solve_fixed_tail
from scripts.p2_seeded_cycle_search import extract_unique_recurrent_cycle


REPLACEMENT_WORDS = (
    (7, 8),
    (8, 7),
    (7, 8, 7),
    (8, 7, 8),
)


def base_movers_n8() -> tuple[int, ...]:
    state_counts, rules = vw.witness_n8()
    cycle, movers = extract_unique_recurrent_cycle(RingSystem(state_counts=state_counts, rules=rules))
    _ = cycle
    return movers


def expand_replacements(
    base: tuple[int, ...],
    choice: tuple[int, ...],
) -> tuple[int, ...]:
    movers: list[int] = []
    occ = 0
    for mover in base:
        if mover != 7:
            movers.append(mover)
            continue
        movers.extend(REPLACEMENT_WORDS[choice[occ]])
        occ += 1
    if occ != len(choice):
        raise ValueError(f"expected {len(choice)} replaced occurrences, saw {occ}")
    return tuple(movers)


def enumerate_nonuniform_choices(base: tuple[int, ...]) -> list[tuple[int, ...]]:
    count_7 = sum(1 for mover in base if mover == 7)
    return list(product(range(len(REPLACEMENT_WORDS)), repeat=count_7))


def scan_nonuniform(
    free_last: bool,
    timeout_ms: int,
    start_index: int,
    limit: int | None,
    progress_every: int,
) -> None:
    base = base_movers_n8()
    choices = enumerate_nonuniform_choices(base)
    end_index = len(choices) if limit is None else min(len(choices), start_index + limit)

    unknowns = 0
    checked = 0
    for choice_index in range(start_index, end_index):
        movers = expand_replacements(base, choices[choice_index])
        found, message, _ = solve_fixed_tail(
            n=9,
            movers=movers,
            bulk_mode="one",
            free_last=free_last,
            timeout_ms=timeout_ms,
            max_models=1,
        )
        checked += 1
        if found:
            print(f"FOUND choice_index={choice_index} choice={choices[choice_index]} length={len(movers)}", flush=True)
            return
        if "unknown" in message:
            unknowns += 1
            print(
                f"unknown choice_index={choice_index} choice={choices[choice_index]} "
                f"length={len(movers)} message={message}",
                flush=True,
            )
        if checked % progress_every == 0:
            print(
                f"progress checked={checked} range={start_index}:{end_index} "
                f"unknowns={unknowns} free_last={free_last}",
                flush=True,
            )

    print(
        f"done checked={checked} range={start_index}:{end_index} "
        f"unknowns={unknowns} free_last={free_last}",
        flush=True,
    )


def scan_extra_single_8(
    free_last: bool,
    timeout_ms: int,
    start_choice_index: int,
    start_gap: int,
    limit: int | None,
    progress_every: int,
) -> None:
    base = base_movers_n8()
    choices = enumerate_nonuniform_choices(base)

    checked = 0
    unknowns = 0
    for choice_index in range(start_choice_index, len(choices)):
        replaced = expand_replacements(base, choices[choice_index])
        gap_start = start_gap if choice_index == start_choice_index else 0
        for gap in range(gap_start, len(replaced) + 1):
            movers = replaced[:gap] + (8,) + replaced[gap:]
            found, message, _ = solve_fixed_tail(
                n=9,
                movers=movers,
                bulk_mode="one",
                free_last=free_last,
                timeout_ms=timeout_ms,
                max_models=1,
            )
            checked += 1
            if found:
                print(
                    f"FOUND choice_index={choice_index} gap={gap} choice={choices[choice_index]} "
                    f"length={len(movers)}",
                    flush=True,
                )
                return
            if "unknown" in message:
                unknowns += 1
                print(
                    f"unknown choice_index={choice_index} gap={gap} choice={choices[choice_index]} "
                    f"length={len(movers)} message={message}",
                    flush=True,
                )
            if checked % progress_every == 0:
                print(
                    f"progress checked={checked} choice_index={choice_index} gap={gap} "
                    f"unknowns={unknowns} free_last={free_last}",
                    flush=True,
                )
            if limit is not None and checked >= limit:
                print(
                    f"partial checked={checked} choice_index={choice_index} gap={gap} "
                    f"unknowns={unknowns} free_last={free_last}",
                    flush=True,
                )
                return

    print(
        f"done checked={checked} unknowns={unknowns} free_last={free_last}",
        flush=True,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("nonuniform", "extra-single-8"), required=True)
    parser.add_argument("--free-last", action="store_true")
    parser.add_argument("--timeout-ms", type=int, default=300)
    parser.add_argument("--progress-every", type=int, default=64)
    parser.add_argument("--start-index", type=int, default=0)
    parser.add_argument("--start-choice-index", type=int, default=0)
    parser.add_argument("--start-gap", type=int, default=0)
    parser.add_argument("--limit", type=int)
    args = parser.parse_args()

    if args.mode == "nonuniform":
        scan_nonuniform(
            free_last=args.free_last,
            timeout_ms=args.timeout_ms,
            start_index=args.start_index,
            limit=args.limit,
            progress_every=args.progress_every,
        )
        return

    scan_extra_single_8(
        free_last=args.free_last,
        timeout_ms=args.timeout_ms,
        start_choice_index=args.start_choice_index,
        start_gap=args.start_gap,
        limit=args.limit,
        progress_every=args.progress_every,
    )


if __name__ == "__main__":
    main()
