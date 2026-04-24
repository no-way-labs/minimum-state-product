#!/usr/bin/env python3
"""Probe the explicit EC-or-shadow bridge predicate on one architecture class."""

from __future__ import annotations

import argparse
import os
import sys


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
if CLAUDE_DIR not in sys.path:
    sys.path.insert(0, CLAUDE_DIR)

from binscc_shadow_universality import enumerate_mover_words_smart, full_analysis  # type: ignore


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--ms", nargs="+", type=int, required=True)
    parser.add_argument("--max-len", type=int, default=None)
    args = parser.parse_args()

    n = args.n
    ms = args.ms
    max_len = args.max_len if args.max_len is not None else 3 * n + 6

    words = enumerate_mover_words_smart(ms, n, max_len)
    total_valid = 0
    overlap_ec = 0
    overlap_shadow = 0
    clean_shadow = 0
    clean_other = 0
    for w in words:
        res = full_analysis(ms, n, w)
        if res is None:
            continue
        total_valid += 1
        if res["any_overlap"]:
            if res["has_conflict"]:
                overlap_ec += 1
            elif res["has_shadow"]:
                overlap_shadow += 1
        else:
            if res["has_shadow"]:
                clean_shadow += 1
            else:
                clean_other += 1
    print(f"n={n} ms={tuple(ms)} max_len={max_len}")
    print(f"valid={total_valid}")
    print(f"overlap_and_conflict={overlap_ec}")
    print(f"overlap_and_shadow={overlap_shadow}")
    print(f"no_overlap_and_shadow={clean_shadow}")
    print(f"no_overlap_and_other={clean_other}")


if __name__ == "__main__":
    main()
