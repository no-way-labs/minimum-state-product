#!/usr/bin/env python3
"""Audit reflection reduction on the EC bridge family."""

from __future__ import annotations

import argparse
import os
import sys


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
LB_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory", "lb_obstruction")
if LB_DIR not in sys.path:
    sys.path.insert(0, LB_DIR)

from ec_bridge_geometry_probe import cyclic_distance, summarize_n, turnaround_vertex


def reflect_word(word: tuple[int, ...], n: int) -> tuple[int, ...]:
    return tuple((2 - x) % n for x in word)


def normalize_rotation(word: tuple[int, ...]) -> tuple[int, ...]:
    return min(word[i:] + word[:i] for i in range(len(word)))


def audit_range(n_from: int, n_to: int, simple_only: bool):
    for n in range(n_from, n_to + 1):
        grouped = summarize_n(n, simple_only)
        assert len(grouped) == 1
        items = list(grouped.values())[0]
        by_word = {word: (turns, minimum, goods) for word, turns, minimum, goods in items}
        failures = []
        for word, turns, minimum, goods in items:
            partner = normalize_rotation(reflect_word(word, n))
            if partner not in by_word:
                failures.append(("missing_partner", word, partner))
                continue
            p_turns, p_minimum, _ = by_word[partner]
            v = turnaround_vertex(word, turns)
            vp = turnaround_vertex(partner, p_turns)
            d = cyclic_distance(v, 1, n)
            dp = cyclic_distance(vp, 1, n)
            if abs(minimum - p_minimum) > 1e-12 or d != dp:
                failures.append(("mismatch", word, partner, minimum, p_minimum, d, dp))
        label = "simple" if simple_only else "full"
        print(f"{label} n={n} words={len(items)} failures={len(failures)}")
        for row in failures[:5]:
            print("  FAIL", row)


def compare_simple_full(n_from: int, n_to: int):
    for n in range(n_from, n_to + 1):
        simple_items = list(summarize_n(n, True).values())[0]
        full_items = list(summarize_n(n, False).values())[0]
        simple_by_d = {}
        full_by_d = {}
        for word, turns, minimum, goods in simple_items:
            d = cyclic_distance(turnaround_vertex(word, turns), 1, n)
            simple_by_d[d] = minimum
        for word, turns, minimum, goods in full_items:
            d = cyclic_distance(turnaround_vertex(word, turns), 1, n)
            full_by_d[d] = minimum
        failures = []
        for d, value in sorted(simple_by_d.items()):
            if d not in full_by_d or abs(value - full_by_d[d]) > 1e-12:
                failures.append((d, value, full_by_d.get(d)))
        print(f"compare n={n} classes={len(simple_by_d)} failures={len(failures)}")
        for row in failures[:5]:
            print("  FAIL", row)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-from", type=int, required=True)
    parser.add_argument("--n-to", type=int, required=True)
    parser.add_argument("--simple-only", action="store_true")
    parser.add_argument("--compare-simple-full", action="store_true")
    args = parser.parse_args()
    if args.compare_simple_full:
        compare_simple_full(args.n_from, args.n_to)
    else:
        audit_range(args.n_from, args.n_to, args.simple_only)


if __name__ == "__main__":
    main()
