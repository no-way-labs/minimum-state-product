#!/usr/bin/env python3
"""Dimension formulas for additive contiguous-window models.

For functions on X = Π_i [m_i], consider the linear model

    f(x) = const + Σ_i g_i(x_i, x_{i+1}, ..., x_{i+w-1})

with cyclic indexing.

Using the standard interaction decomposition, the dimension is

    dim_w = Σ_{S subset [n] : S is contained in some width-w window}
            Π_{i in S} (m_i - 1)

and the codimension is the complementary weighted sum.

This script computes these dimensions and highlights two special cases:

- width n-1: codimension = Π_i (m_i - 1)
- width n-2: codimension is the weighted sum over vertex covers of C_n
"""

from __future__ import annotations

import argparse
import itertools
import os
import sys
from functools import reduce
from operator import mul


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
if CLAUDE_DIR not in sys.path:
    sys.path.insert(0, CLAUDE_DIR)

from cup2_theorem import build_system as build_cup2_system  # type: ignore


def product(values):
    return reduce(mul, values, 1)


def build_ms(family: str, n: int) -> list[int]:
    if family == "cup2":
        ms, _ = build_cup2_system(n)
        return ms
    if family == "sol3":
        return [3] * n
    raise ValueError(f"unknown family {family}")


def windows(n: int, width: int):
    for start in range(n):
        yield {(start + j) % n for j in range(width)}


def subset_weight(ms: list[int], subset_mask: int) -> int:
    weight = 1
    idx = 0
    while subset_mask:
        if subset_mask & 1:
            weight *= ms[idx] - 1
        subset_mask >>= 1
        idx += 1
    return weight


def contained_in_some_window(mask: int, win_masks: list[int]) -> bool:
    return any(mask & ~w == 0 for w in win_masks)


def dimension(ms: list[int], width: int) -> tuple[int, int]:
    n = len(ms)
    total = product(ms)
    win_masks = []
    for w in windows(n, width):
        mask = 0
        for i in w:
            mask |= 1 << i
        win_masks.append(mask)

    dim = 0
    for mask in range(1 << n):
        if contained_in_some_window(mask, win_masks):
            dim += subset_weight(ms, mask)
    codim = total - dim
    return dim, codim


def weighted_vertex_cover_codim(ms: list[int]) -> int:
    """Codimension for width n-2, computed as weighted sum over vertex covers."""
    n = len(ms)
    total = 0
    for mask in range(1 << n):
        ok = True
        for i in range(n):
            if not ((mask >> i) & 1) and not ((mask >> ((i + 1) % n)) & 1):
                ok = False
                break
        if ok:
            total += subset_weight(ms, mask)
    return total


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--width", type=int, default=None)
    args = parser.parse_args()

    ms = build_ms(args.family, args.n)
    total = product(ms)
    print(f"family={args.family} n={args.n} ms={ms} total={total}")

    widths = [args.width] if args.width is not None else list(range(1, len(ms)))
    for width in widths:
        dim, codim = dimension(ms, width)
        print(
            f"width={width}: dim={dim}, codim={codim}, dim/total={dim/total:.6f}"
        )
        if width == len(ms) - 1:
            full_interaction = product([m - 1 for m in ms])
            print(f"  width=n-1 check: product(m_i-1)={full_interaction}")
        if width == len(ms) - 2:
            vc = weighted_vertex_cover_codim(ms)
            print(f"  width=n-2 check: weighted_vertex_cover_codim={vc}")


if __name__ == "__main__":
    main()
