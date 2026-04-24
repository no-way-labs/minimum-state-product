"""Sweep all distinct cyclic orientations of candidate n=8 multisets.

Usage:
    python3 n8_sweep.py

Runs p2_smt_completion pipeline on every distinct necklace of each
candidate multiset. Logs results to n8_sweep_results.txt. Stops early
if a valid witness is found.
"""

from __future__ import annotations

import math
import os
import sys
import time
from itertools import permutations

sys.path.insert(0, os.path.dirname(__file__))

from p2_smt_completion import main as smt_main
from p2_good_cycle_search import enumerate_good_cycles, local_context
from p2_cycle_screen import forced_rule_map
from p2_completion_search import has_fatal_forced_cycle_singletons
from p2_smt_completion import solve_cycle_with_smt


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
    found = False

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
            found = True
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


def main() -> None:
    log_path = os.path.join(os.path.dirname(__file__), "n8_sweep_results.txt")

    # Candidate multisets in priority order
    candidates = [
        ((2, 2, 2, 4, 3, 3, 3, 3), "single-quaternary, product 2592"),
        ((2, 2, 2, 4, 4, 3, 3, 3), "two-quaternary, product 3456"),
        ((2, 2, 2, 5, 3, 3, 3, 3), "single-5-state, product 3240"),
    ]

    with open(log_path, "a") as log:
        log.write(f"\n{'='*60}\n")
        log.write(f"n=8 sweep started at {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
        log.write(f"{'='*60}\n\n")
        log.flush()

        for multiset, desc in candidates:
            product = math.prod(multiset)
            necklaces = distinct_necklaces(multiset)
            header = f"Multiset {multiset} ({desc}), product={product}, {len(necklaces)} orientations"
            print(f"\n{'='*60}")
            print(header)
            print(f"{'='*60}")
            log.write(f"{header}\n")
            log.write(f"{'-'*60}\n")
            log.flush()

            witness_found = False
            for i, orientation in enumerate(necklaces):
                label = f"  [{i+1}/{len(necklaces)}] {','.join(map(str, orientation))}"
                print(f"\n{label}")
                log.write(f"\n{label}\n")
                log.flush()

                result = run_orientation(orientation)

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

            summary = (
                f"\nMultiset {multiset}: "
                f"{'WITNESS FOUND' if witness_found else 'ALL ORIENTATIONS DEAD'}\n\n"
            )
            print(summary)
            log.write(summary)
            log.flush()

            if witness_found:
                print("Stopping — witness found.")
                log.write("Stopping — witness found.\n")
                return

        log.write("\nAll candidate multisets exhausted without witness.\n")
        print("\nAll candidate multisets exhausted without witness.")


if __name__ == "__main__":
    main()
