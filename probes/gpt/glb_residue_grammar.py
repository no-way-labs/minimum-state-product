#!/usr/bin/env python3
"""Classify mover words into the explicit three-sweep residue grammar."""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter, defaultdict


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from scripts.glb_block_signature import split_blocks
from scripts.glb_case3c_l29_scan import enumerate_words_with_edge_counts
from scripts.glb_case3c_vector_scan import feasible_edge_vectors
from scripts.glb_return_staircase import (
    find_anchored_return_contexts,
    find_binary_bounce_contexts,
    find_return_cones,
)


def parse_int_tuple(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def step_kind(left: int, right: int, n: int) -> str:
    if (right - left) % n == 1:
        return "F"
    if (left - right) % n == 1:
        return "R"
    return "?"


def parse_sweep_block(block: tuple[int, ...], n: int) -> tuple[str, tuple[str, ...]] | None:
    if len(block) < 3 or block[0] != 0 or block[-1] != 0:
        return None
    orientation = step_kind(block[0], block[1], n)
    if orientation not in {"F", "R"}:
        return None

    wiggles: list[str] = []
    i = 0
    while i < len(block) - 1:
        kind = step_kind(block[i], block[i + 1], n)
        if kind == orientation:
            i += 1
            continue
        if i + 2 >= len(block):
            return None
        a, b, c = block[i], block[i + 1], block[i + 2]
        if a != c:
            return None
        if step_kind(b, c, n) != orientation:
            return None
        low = min(a, b)
        high = max(a, b)
        wiggles.append(f"{low}{high}{low}")
        i += 2

    return orientation, tuple(wiggles)


def classify_word(movers: tuple[int, ...], n: int) -> dict[str, object] | None:
    blocks = split_blocks(movers)
    if len(blocks) != 4:
        return None

    short_modes = {
        (0, 8, 0): "short080",
        (0, 1, 0): "short010",
    }
    tail_modes = {
        (0, 8): "tail08",
        (0, 1): "tail01",
        (0, 1, 2, 1): "tail121",
    }

    short_positions = [i for i, block in enumerate(blocks) if block in short_modes]
    if len(short_positions) > 1:
        return None

    if short_positions:
        short_pos = short_positions[0]
        boundary_mode = short_modes[blocks[short_pos]]
        sweep_positions = [i for i in range(4) if i != short_pos]
    else:
        if blocks[-1] not in tail_modes:
            return None
        boundary_mode = tail_modes[blocks[-1]]
        sweep_positions = [0, 1, 2]

    sweeps: list[tuple[str, tuple[str, ...]]] = []
    for pos in sweep_positions:
        parsed = parse_sweep_block(blocks[pos], n)
        if parsed is None:
            return None
        sweeps.append(parsed)

    orientations = {orientation for orientation, _ in sweeps}
    if len(orientations) != 1:
        return None

    orientation = next(iter(orientations))
    return {
        "orientation": orientation,
        "boundary_mode": boundary_mode,
        "sweep_wiggles": tuple(wiggles for _, wiggles in sweeps),
        "blocks": blocks,
    }


def mode_classify_word(movers: tuple[int, ...], n: int) -> None:
    result = classify_word(movers, n)
    print(f"blocks={split_blocks(movers)}")
    print(f"classification={result}")


def mode_scan_zero_vectors(state_counts: tuple[int, ...], mover_length: int) -> None:
    n = len(state_counts)
    vectors = [edge_counts for edge_counts in feasible_edge_vectors(state_counts, mover_length) if all(value >= 3 for value in edge_counts)]
    print(f"state_counts={state_counts}")
    print(f"mover_length={mover_length}")
    print(f"zero_vectors={len(vectors)}")

    overall_counter: Counter[str] = Counter()
    signature_counter: Counter[tuple[str, str, tuple[tuple[str, ...], ...]] | str] = Counter()

    for index, edge_counts in enumerate(vectors, start=1):
        words = enumerate_words_with_edge_counts(n, edge_counts)
        survivors = []
        bad = []
        for word in words:
            if find_return_cones(word, n):
                continue
            if find_binary_bounce_contexts(word, state_counts):
                continue
            if find_anchored_return_contexts(word, state_counts):
                continue
            survivors.append(word)
            classification = classify_word(word, n)
            if classification is None:
                bad.append(word)
                signature_counter["unclassified"] += 1
            else:
                key = (
                    classification["orientation"],
                    classification["boundary_mode"],
                    classification["sweep_wiggles"],
                )
                signature_counter[key] += 1

        overall_counter["survivors"] += len(survivors)
        overall_counter["unclassified"] += len(bad)
        print(
            f"vector {index}/{len(vectors)} edge_counts={edge_counts} "
            f"survivors={len(survivors)} unclassified={len(bad)}"
        )
        if bad:
            print(f"  first_bad={bad[0]}")

    print(f"overall={dict(sorted(overall_counter.items()))}")
    print("signature_counter:")
    for key, count in signature_counter.most_common():
        print(f"  {key}: {count}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("classify-word", "scan-zero-vectors"), default="classify-word")
    parser.add_argument("--movers")
    parser.add_argument("--state-counts", default="2,3,2,3,3,2,3,3,4")
    parser.add_argument("--mover-length", type=int, default=33)
    parser.add_argument("--n", type=int, default=9)
    args = parser.parse_args()

    if args.mode == "classify-word":
        if not args.movers:
            raise SystemExit("--movers is required for --mode classify-word")
        mode_classify_word(parse_int_tuple(args.movers), args.n)
    else:
        mode_scan_zero_vectors(parse_int_tuple(args.state_counts), args.mover_length)


if __name__ == "__main__":
    main()
