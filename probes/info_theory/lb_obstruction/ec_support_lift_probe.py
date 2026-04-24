#!/usr/bin/env python3
"""Search for small forbidden supports with positive energy across a BAF class."""

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

from anova_interaction_spectrum import all_window_masks, allowed_mask, anova_spectrum
from cic_case3a_proof5 import enumerate_fc2_walks, is_sweep  # type: ignore
from ec_baf_conflict_state_probe import conflict_steps, valid_good_cycles
from ec_bridge_geometry_probe import turnaround_steps, turnaround_vertex, cyclic_distance
from ec_word_family import distance_class_words


def mask_from_complement(n: int, comp: tuple[int, ...]) -> int:
    mask = 0
    for i in range(n):
        if i not in comp:
            mask |= 1 << i
    return mask


def complements_upto(n: int, max_size: int):
    out = []
    for r in range(1, max_size + 1):
        out.extend(itertools.combinations(range(n), r))
    return out


def class_goods(n: int, target_d: int, direct_family: bool = False):
    ms = [2, 2, 2] + [3] * (n - 3)
    goods = []
    words = distance_class_words(n, target_d) if direct_family else enumerate_fc2_walks(n)
    for word in words:
        if not direct_family and is_sweep(word, n):
            continue
        good_cycles = valid_good_cycles(word, n, ms)
        if not good_cycles:
            continue
        if not direct_family:
            try:
                turns = turnaround_steps(word, n)
            except ValueError:
                continue
            d = cyclic_distance(turnaround_vertex(word, turns), 1, n)
            if d != target_d:
                continue
        for good in good_cycles:
            goods.append((tuple(word), good))
    return ms, goods


def class_energies(n: int, target_d: int, direct_family: bool = False):
    ms, goods = class_goods(n, target_d, direct_family)
    cfgs = list(itertools.product(*[range(m) for m in ms]))
    energy_dicts = []
    for word, good in goods:
        steps = set(conflict_steps(good, list(word), n))
        states = {tuple(good[t]) for t in steps}
        arr = np.array([1.0 if cfg in states else 0.0 for cfg in cfgs], dtype=np.float64)
        aa, af, top, energies = anova_spectrum(ms, arr, n - 2)
        energy_dicts.append(energies)
    return ms, goods, energy_dicts


def support_scan(n: int, target_d: int, max_comp_size: int, min_threshold: float = 1e-15, direct_family: bool = False):
    ms, goods, energy_dicts = class_energies(n, target_d, direct_family)
    win_masks = all_window_masks(n, n - 2)
    results = []
    for comp in complements_upto(n, max_comp_size):
        mask = mask_from_complement(n, comp)
        if allowed_mask(mask, win_masks):
            continue
        vals = [energies.get(mask, 0.0) for energies in energy_dicts]
        min_val = min(vals)
        if min_val > min_threshold:
            uniq = sorted(set(round(v, 12) for v in vals))
            results.append((len(comp), len(uniq), min_val, comp, uniq[:8]))
    results.sort(key=lambda row: (row[0], row[1], -row[2], row[3]))
    return goods, results


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--d", type=int, required=True)
    parser.add_argument("--max-comp-size", type=int, default=2)
    parser.add_argument("--limit", type=int, default=20)
    parser.add_argument("--min-threshold", type=float, default=1e-15)
    parser.add_argument("--direct-family", action="store_true")
    args = parser.parse_args()

    goods, results = support_scan(args.n, args.d, args.max_comp_size, args.min_threshold, args.direct_family)
    print(f"n={args.n} d={args.d} goods={len(goods)} positive_supports={len(results)}")
    for row in results[: args.limit]:
        size, uniq_count, min_val, comp, uniq_vals = row
        print(
            f"  comp={comp} size={size} uniq_count={uniq_count} "
            f"min={min_val:.12f} uniq_vals={uniq_vals}"
        )


if __name__ == "__main__":
    main()
