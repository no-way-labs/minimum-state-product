"""Sweep all distinct cyclic orientations of candidate n=9 multisets.

Usage:
    python3 n9_sweep.py

Runs p2_smt_completion pipeline on every distinct necklace of each
candidate multiset. Logs results to n9_sweep_results.txt. Stops early
if a valid witness is found.

Note: n=9 config spaces are large (7776+), so each orientation may take
30-60+ minutes. This script is designed to run unattended for many hours.
"""

from __future__ import annotations

import argparse
import math
import os
import sys
import time
from itertools import permutations

sys.path.insert(0, os.path.dirname(__file__))
sys.setrecursionlimit(50000)

from p2_smt_completion import solve_cycle_with_smt
from p2_good_cycle_search import enumerate_good_cycles, local_context
from p2_cycle_screen import forced_rule_map
from p2_completion_search import has_fatal_forced_cycle_singletons


def distinct_necklaces(multiset: tuple[int, ...]) -> list[tuple[int, ...]]:
    """Return all distinct cyclic arrangements of a multiset."""
    n = len(multiset)
    seen: set[tuple[int, ...]] = set()
    results: list[tuple[int, ...]] = []
    for perm in set(permutations(multiset)):
        # canonical rotation = lexicographic minimum
        rotations = [perm[i:] + perm[:i] for i in range(n)]
        canon = min(rotations)
        if canon not in seen:
            seen.add(canon)
            results.append(canon)
    results.sort()
    return results


def run_orientation(
    state_counts: tuple[int, ...],
    screen_time_limit: float = 600.0,
    max_cycles: int = 10_000_000,
    solver_timeout_ms: int = 300_000,
    max_survivors: int = 20,
) -> dict:
    """Run the full pipeline on one orientation. Returns a result dict."""
    started = time.time()
    screened = 0
    tried = 0

    for cycle, movers in enumerate_good_cycles(
        state_counts, time_limit=screen_time_limit, max_cycles=max_cycles
    ):
        screened += 1
        cycle_set = frozenset(cycle)
        fm = forced_rule_map(cycle, movers)
        if has_fatal_forced_cycle_singletons(state_counts, cycle_set, fm):
            continue

        tried += 1
        print(f"  survivor cycle {screened} length={len(cycle)}")
        result = solve_cycle_with_smt(
            state_counts, cycle, movers, timeout_ms=solver_timeout_ms
        )
        print(f"  {result.message}")
        if result.found and result.system is not None:
            elapsed = time.time() - started
            return {
                "found": True,
                "screened": screened,
                "tried": tried,
                "elapsed": elapsed,
                "system": result.system,
            }
        if tried >= max_survivors:
            break

    elapsed = time.time() - started
    return {
        "found": False,
        "screened": screened,
        "tried": tried,
        "elapsed": elapsed,
        "system": None,
    }


def parse_state_counts(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def default_candidates() -> list[tuple[tuple[int, ...], str]]:
    return [
        ((2, 2, 2, 4, 3, 3, 3, 3, 3), "single-quaternary, product 7776"),
        ((2, 2, 2, 4, 4, 3, 3, 3, 3), "two-quaternary, product 10368"),
        ((2, 2, 2, 5, 3, 3, 3, 3, 3), "single-5-state, product 9720"),
    ]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--multiset",
        help="comma-separated state counts for a single target multiset",
    )
    parser.add_argument(
        "--start-orientation",
        type=int,
        default=1,
        help="1-based orientation index to start from",
    )
    parser.add_argument(
        "--end-orientation",
        type=int,
        help="1-based orientation index to stop at",
    )
    parser.add_argument(
        "--screen-time-limit",
        type=float,
        default=600.0,
        help="good-cycle screen time limit per orientation",
    )
    parser.add_argument(
        "--max-cycles",
        type=int,
        default=10_000_000,
        help="maximum good cycles to enumerate per orientation",
    )
    parser.add_argument(
        "--solver-timeout-ms",
        type=int,
        default=300_000,
        help="SMT timeout per survivor cycle",
    )
    parser.add_argument(
        "--max-survivors",
        type=int,
        default=20,
        help="maximum survivor cycles to hand to SMT per orientation",
    )
    parser.add_argument(
        "--log-path",
        default=os.path.join(os.path.dirname(__file__), "n9_sweep_results.txt"),
        help="path to the append-only sweep log",
    )
    args = parser.parse_args()

    log_path = args.log_path

    if args.multiset:
        multiset = parse_state_counts(args.multiset)
        candidates = [(multiset, "custom target")]
    else:
        candidates = default_candidates()

    with open(log_path, "a") as log:
        log.write(f"\n{'='*60}\n")
        log.write(f"n=9 sweep started at {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
        log.write(f"{'='*60}\n\n")
        log.flush()

        for multiset, desc in candidates:
            product = math.prod(multiset)
            necklaces = distinct_necklaces(multiset)
            start_idx = max(0, args.start_orientation - 1)
            end_idx = (
                len(necklaces)
                if args.end_orientation is None
                else min(len(necklaces), args.end_orientation)
            )
            subset_requested = start_idx != 0 or end_idx != len(necklaces)
            if start_idx >= len(necklaces):
                raise SystemExit(
                    f"start orientation {args.start_orientation} exceeds {len(necklaces)} orientations"
                )
            if end_idx <= start_idx:
                raise SystemExit(
                    f"empty orientation range: start={args.start_orientation} end={args.end_orientation}"
                )
            header = f"Multiset {multiset} ({desc}), product={product}, {len(necklaces)} orientations"
            print(f"\n{'='*60}")
            print(header)
            print(f"{'='*60}")
            log.write(f"{header}\n")
            log.write(f"{'-'*60}\n")
            if subset_requested:
                range_note = (
                    f"Processing orientation range {start_idx + 1}-{end_idx} "
                    f"out of {len(necklaces)}\n"
                )
                print(range_note.strip())
                log.write(range_note)
            log.flush()

            # Check which orientations were already completed
            try:
                with open(log_path, "r") as existing:
                    done_text = existing.read()
            except FileNotFoundError:
                done_text = ""

            witness_found = False
            for i in range(start_idx, end_idx):
                orientation = necklaces[i]
                orient_str = ','.join(map(str, orientation))
                # Skip already-completed orientations
                if f"] {orient_str}\n  screened=" in done_text:
                    print(f"  [{i+1}/{len(necklaces)}] {orient_str} -- already done, skipping")
                    continue

                label = f"  [{i+1}/{len(necklaces)}] {orient_str}"
                print(f"\n{label}")
                log.write(f"\n{label}\n")
                log.flush()

                result = run_orientation(
                    orientation,
                    screen_time_limit=args.screen_time_limit,
                    max_cycles=args.max_cycles,
                    solver_timeout_ms=args.solver_timeout_ms,
                    max_survivors=args.max_survivors,
                )

                status = (
                    f"  screened={result['screened']} "
                    f"survivors={result['tried']} "
                    f"elapsed={result['elapsed']:.1f}s "
                    f"{'WITNESS FOUND!' if result['found'] else 'dead'}"
                )
                print(status)
                log.write(f"{status}\n")
                log.flush()

                if result["found"]:
                    system = result["system"]
                    detail = f"  WITNESS: state_counts={system.state_counts}\n"
                    for pi, table in enumerate(system.rules):
                        detail += f"    P{pi}: {dict(sorted(table.items()))}\n"
                    print(detail)
                    log.write(detail)
                    log.flush()
                    witness_found = True
                    break

            if witness_found:
                summary = f"\nMultiset {multiset}: WITNESS FOUND\n\n"
            elif subset_requested:
                summary = (
                    f"\nMultiset {multiset}: no witness in orientations "
                    f"{start_idx + 1}-{end_idx}\n\n"
                )
            else:
                summary = f"\nMultiset {multiset}: ALL ORIENTATIONS DEAD\n\n"
            print(summary)
            log.write(summary)
            log.flush()

            if witness_found:
                print("Stopping — witness found.")
                log.write("Stopping — witness found.\n")
                return

        if args.multiset and subset_requested:
            log.write("\nRequested orientation range exhausted without witness.\n")
            print("\nRequested orientation range exhausted without witness.")
        else:
            log.write("\nAll candidate multisets exhausted without witness.\n")
            print("\nAll candidate multisets exhausted without witness.")


if __name__ == "__main__":
    main()
