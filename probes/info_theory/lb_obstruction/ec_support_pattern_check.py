#!/usr/bin/env python3
"""Check a proposed class-stable support pattern across all distance classes."""

from __future__ import annotations

import argparse
import itertools
import os
import sys

import numpy as np


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
LB_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory", "lb_obstruction")
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
for path in [LB_DIR, INFO_DIR, CLAUDE_DIR]:
    if path not in sys.path:
        sys.path.insert(0, path)

from cic_case3a_proof5 import enumerate_fc2_walks, is_sweep  # type: ignore
from ec_baf_conflict_state_probe import conflict_steps, valid_good_cycles
from ec_bridge_geometry_probe import turnaround_steps, turnaround_vertex, cyclic_distance
from ec_word_family import all_distance_words
from single_mask_energy import effect_energy_for_mask


def mask_from_complement(n: int, comp: tuple[int, ...]) -> int:
    mask = 0
    for i in range(n):
        if i not in comp:
            mask |= 1 << i
    return mask


def candidate_complements(d: int) -> list[tuple[int, ...]]:
    if d == 0:
        return [(1,)]
    if d == 1:
        return [(0, 2)]
    if d % 2 == 0:
        return [(1,)]
    return [(0,), (2,)]


def check_n(n: int, direct_family: bool):
    ms = [2, 2, 2] + [3] * (n - 3)
    cfgs = list(itertools.product(*[range(m) for m in ms]))
    goods_by_d: dict[int, list[tuple[tuple[int, ...], list[tuple[int, ...]]]]] = {}
    words = all_distance_words(n) if direct_family else enumerate_fc2_walks(n)
    for word in words:
        if not direct_family and is_sweep(word, n):
            continue
        good_cycles = valid_good_cycles(word, n, ms)
        if not good_cycles:
            continue
        try:
            turns = turnaround_steps(word, n)
        except ValueError:
            continue
        d = cyclic_distance(turnaround_vertex(word, turns), 1, n)
        for good in good_cycles:
            goods_by_d.setdefault(d, []).append((tuple(word), good))

    print(f"n={n}")
    for d, goods in sorted(goods_by_d.items()):
        values_by_good = []
        for word, good in goods:
            steps = set(conflict_steps(good, list(word), n))
            states = {tuple(good[t]) for t in steps}
            arr = np.array([1.0 if cfg in states else 0.0 for cfg in cfgs], dtype=np.float64)
            values_by_good.append(arr)
        print(f"  d={d} goods={len(goods)}")
        for comp in candidate_complements(d):
            mask = mask_from_complement(n, comp)
            vals = [effect_energy_for_mask(ms, arr, mask) for arr in values_by_good]
            uniq = sorted(set(round(v, 12) for v in vals))
            print(
                f"    comp={comp} min={min(vals):.12f} max={max(vals):.12f} "
                f"uniq_vals={uniq[:8]}"
            )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--direct-family", action="store_true")
    args = parser.parse_args()
    check_n(args.n, args.direct_family)


if __name__ == "__main__":
    main()
