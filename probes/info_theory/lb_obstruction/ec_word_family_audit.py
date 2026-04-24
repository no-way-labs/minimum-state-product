#!/usr/bin/env python3
"""Audit whether the direct EC word family matches the tested full class."""

from __future__ import annotations

import argparse
import os
import sys


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
LB_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory", "lb_obstruction")
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
for path in [LB_DIR, CLAUDE_DIR]:
    if path not in sys.path:
        sys.path.insert(0, path)

from cic_case3a_proof5 import enumerate_fc2_walks, is_sweep  # type: ignore
from ec_baf_conflict_state_probe import valid_good_cycles
from ec_bridge_geometry_probe import turnaround_steps
from ec_word_family import all_distance_words


def tested_full_words(n: int):
    ms = [2, 2, 2] + [3] * (n - 3)
    out = []
    for word in enumerate_fc2_walks(n):
        if is_sweep(word, n):
            continue
        goods = valid_good_cycles(word, n, ms)
        if not goods:
            continue
        try:
            turnaround_steps(word, n)
        except ValueError:
            continue
        out.append(tuple(word))
    return sorted(out)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-from", type=int, required=True)
    parser.add_argument("--n-to", type=int, required=True)
    args = parser.parse_args()
    for n in range(args.n_from, args.n_to + 1):
        tested = set(tested_full_words(n))
        direct = set(all_distance_words(n))
        print(
            f"n={n} tested={len(tested)} direct={len(direct)} "
            f"missing={len(tested-direct)} extra={len(direct-tested)}"
        )
        for row in sorted(tested - direct)[:5]:
            print("  missing", row)
        for row in sorted(direct - tested)[:5]:
            print("  extra", row)


if __name__ == "__main__":
    main()
