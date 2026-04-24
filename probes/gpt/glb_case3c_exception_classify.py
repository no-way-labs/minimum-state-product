#!/usr/bin/env python3
"""Classify zero-singleton Case 3c exceptions after analytic filters."""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from scripts.glb_case3c_l29_scan import enumerate_words_with_edge_counts
from scripts.glb_completion_diagnose import forced_scc_summary
from scripts.glb_return_staircase import (
    find_anchored_return_contexts,
    find_binary_bounce_contexts,
    find_return_cones,
)
from scripts.glb_seeded_unsat_core import unsat_core_labels
from scripts.p2_seeded_cycle_search import solve_good_cycle_from_movers
from scripts.p2_smt_completion import solve_cycle_with_smt


def parse_int_tuple(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def first_ctx(labels: list[str]) -> str | None:
    return next((label for label in labels if label.startswith("ctx_")), None)


def classify_branch(
    state_counts: tuple[int, ...],
    edge_counts: tuple[int, ...],
    cycle_timeout_ms: int,
    completion_timeout_ms: int,
) -> None:
    words = enumerate_words_with_edge_counts(len(state_counts), edge_counts)
    exceptions: list[tuple[int, ...]] = []
    for word in words:
        if find_return_cones(word, len(state_counts)):
            continue
        if find_binary_bounce_contexts(word, state_counts):
            continue
        if find_anchored_return_contexts(word, state_counts):
            continue
        exceptions.append(word)

    print(f"state_counts={state_counts}")
    print(f"edge_counts={edge_counts}")
    print(f"words={len(words)}")
    print(f"exceptions={len(exceptions)}")

    outcome_counter: Counter[str] = Counter()
    ctx_counter: Counter[str | None] = Counter()
    scc_counter: Counter[tuple[int | None, bool | None]] = Counter()

    for index, word in enumerate(exceptions, start=1):
        cycle = solve_good_cycle_from_movers(state_counts, word, timeout_ms=cycle_timeout_ms)
        if not cycle.found:
            if "unknown" in cycle.message:
                outcome = "seed_unknown"
                detail = cycle.message
            else:
                outcome = "seed_unsat"
                status, labels = unsat_core_labels(state_counts, word)
                assert status == "unsat"
                detail = first_ctx(labels)
                ctx_counter[detail] += 1
            outcome_counter[outcome] += 1
            print(f"{index}: outcome={outcome} detail={detail} word={word}")
            continue

        completion = solve_cycle_with_smt(
            state_counts,
            cycle.cycle,
            word,
            timeout_ms=completion_timeout_ms,
        )
        if completion.found:
            outcome_counter["completion_sat"] += 1
            print(f"{index}: outcome=completion_sat word={word}")
            continue

        if "unknown" in completion.message:
            outcome_counter["completion_unknown"] += 1
            print(f"{index}: outcome=completion_unknown detail={completion.message} word={word}")
            continue

        summary = forced_scc_summary(state_counts, cycle.cycle, word)
        key = (
            None if summary is None else summary["scc_size"],
            None if summary is None else summary["all_binary"],
        )
        scc_counter[key] += 1
        outcome_counter["completion_unsat"] += 1
        print(
            f"{index}: outcome=completion_unsat detail={completion.message} "
            f"scc={key} word={word}"
        )

    print(f"outcome_counter={dict(sorted(outcome_counter.items()))}")
    print(f"ctx_counter={dict(sorted(ctx_counter.items(), key=lambda item: (str(item[0]), item[1])))}")
    print(f"scc_counter={dict(sorted(scc_counter.items()))}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--state-counts", required=True)
    parser.add_argument("--edge-counts", required=True)
    parser.add_argument("--cycle-timeout-ms", type=int, default=1500)
    parser.add_argument("--completion-timeout-ms", type=int, default=15000)
    args = parser.parse_args()

    classify_branch(
        parse_int_tuple(args.state_counts),
        parse_int_tuple(args.edge_counts),
        args.cycle_timeout_ms,
        args.completion_timeout_ms,
    )


if __name__ == "__main__":
    main()
