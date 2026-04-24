#!/usr/bin/env python3
"""Tabulate EC bridge values on canonical distance-class representatives."""

from __future__ import annotations

import argparse
import os
import sys


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
LB_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory", "lb_obstruction")
if LB_DIR not in sys.path:
    sys.path.insert(0, LB_DIR)

from ec_bridge_geometry_probe import simple_conflict_state_forbid


def canonical_turnaround_word(n: int, v: int) -> tuple[int, ...]:
    """Canonical simple two-turnaround word with turnaround vertex v >= 1."""
    if not (1 <= v <= n - 1):
        raise ValueError(f"need 1 <= v <= n-1, got v={v}")
    seg1 = list(range(0, v + 1))
    seg2 = list(range(v - 1, -1, -1))
    seg3 = list(range(n - 1, v - 1, -1))
    seg4 = list(range(v + 1, n))
    word = tuple(seg1 + seg2 + seg3 + seg4)
    if len(word) != 2 * n:
        raise AssertionError((n, v, len(word), word))
    return word


def representative_word(n: int, d: int) -> tuple[int, ...]:
    """Choose the class representative with turnaround vertex v = 1 + d."""
    if not (0 <= d <= n // 2):
        raise ValueError(f"need 0 <= d <= floor(n/2), got d={d}")
    v = 1 + d
    if v > n - 1:
        raise ValueError((n, d, v))
    return canonical_turnaround_word(n, v)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-from", type=int, required=True)
    parser.add_argument("--n-to", type=int, required=True)
    args = parser.parse_args()

    for n in range(args.n_from, args.n_to + 1):
        ms = [2, 2, 2] + [3] * (n - 3)
        print(f"n={n}")
        for d in range(0, n // 2 + 1):
            word = representative_word(n, d)
            value = simple_conflict_state_forbid(word, ms)
            print(f"  d={d} v={1+d} value={value:.12f} word={word}")


if __name__ == "__main__":
    main()
