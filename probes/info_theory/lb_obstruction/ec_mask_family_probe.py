#!/usr/bin/env python3
"""Probe a small anchored forbidden-mask family on EC bridge representatives."""

from __future__ import annotations

import argparse
import os
import sys
from itertools import product as iproduct

import numpy as np


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
LB_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory", "lb_obstruction")
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
for path in [LB_DIR, INFO_DIR]:
    if path not in sys.path:
        sys.path.insert(0, path)

from anova_interaction_spectrum import anova_spectrum
from ec_bridge_geometry_probe import build_simple_good, conflict_steps_from_good
from ec_distance_class_values import representative_word


def mask_from_complement(n: int, comp: tuple[int, ...]) -> int:
    mask = 0
    for i in range(n):
        if i not in comp:
            mask |= 1 << i
    return mask


def candidate_complements(d: int) -> list[tuple[int, ...]]:
    if d == 0:
        return [(1,)]
    if d % 2 == 0:
        return [(1, d + 1)]
    if d == 1:
        return [(0, 2)]
    return [(0, d + 1), (2, d + 1)]


def representative_mask_energies(n: int):
    ms = [2, 2, 2] + [3] * (n - 3)
    cfgs = list(iproduct(*[range(m) for m in ms]))
    rows = []
    for d in range(n // 2 + 1):
        word = representative_word(n, d)
        good = build_simple_good(list(word), n)
        steps = conflict_steps_from_good(good, list(word), n)
        states = {tuple(good[t]) for t in steps}
        vals = np.array([1.0 if cfg in states else 0.0 for cfg in cfgs], dtype=np.float64)
        aa, af, _, energies = anova_spectrum(ms, vals, n - 2)
        frac = af / (aa + af) if aa + af else 0.0
        comps = candidate_complements(d)
        cand = []
        for comp in comps:
            mask = mask_from_complement(n, comp)
            cand.append((comp, energies.get(mask, 0.0)))
        rows.append((d, frac, cand))
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-from", type=int, required=True)
    parser.add_argument("--n-to", type=int, required=True)
    args = parser.parse_args()

    for n in range(args.n_from, args.n_to + 1):
        print(f"n={n}")
        for d, frac, cand in representative_mask_energies(n):
            shown = [(comp, round(en, 12)) for comp, en in cand]
            print(f"  d={d} frac={frac:.12f} candidates={shown}")


if __name__ == "__main__":
    main()
