#!/usr/bin/env python3
"""ANOVA interaction spectrum for rank extensions on the full config space.

We extend the bad-side rank to all configurations by setting:

    F(c) = 0            if c is good
         = rank(c) + 1  if c is bad

Under the uniform product measure on the full configuration space, we compute
the exact functional ANOVA / interaction decomposition:

    F = sum_{S subset [n]} F_S

and measure how much L2 energy lies on interaction subsets that are forbidden
by the width-(n-2) window model.
"""

from __future__ import annotations

import argparse
import itertools
import math
import os
import sys
from collections import defaultdict

import numpy as np


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
if CLAUDE_DIR not in sys.path:
    sys.path.insert(0, CLAUDE_DIR)

from cup2_theorem import build_system as build_cup2_system  # type: ignore
from verifier import all_configs, verify_system  # type: ignore

from cycle_info_metrics import sol3_v1_rules
from rank_info_metrics import rank_bad_configs


def build_family(name: str, n: int):
    if name == "cup2":
        ms, fs = build_cup2_system(n)
        return f"CUP-2(n={n})", ms, fs
    if name == "sol3":
        ms = [3] * n
        fs = sol3_v1_rules(ms, n)
        return f"Sol3(n={n})", ms, fs
    raise ValueError(f"unknown family {name}")


def mask_indices(mask: int, n: int) -> tuple[int, ...]:
    return tuple(i for i in range(n) if (mask >> i) & 1)


def all_window_masks(n: int, width: int) -> list[int]:
    masks = []
    for start in range(n):
        mask = 0
        for j in range(width):
            mask |= 1 << ((start + j) % n)
        masks.append(mask)
    return masks


def allowed_mask(mask: int, win_masks: list[int]) -> bool:
    return any(mask & ~w == 0 for w in win_masks)


def anova_spectrum(ms: list[int], values: np.ndarray, width: int):
    n = len(ms)
    total = int(np.prod(ms))
    configs = list(itertools.product(*(range(m) for m in ms)))
    subsets = list(range(1 << n))
    subset_idx = {mask: mask_indices(mask, n) for mask in subsets}

    means = {}
    for mask in subsets:
        idxs = subset_idx[mask]
        shape = tuple(ms[i] for i in idxs)
        arr = np.zeros(shape if shape else (), dtype=np.float64)
        for cfg, val in zip(configs, values):
            key = tuple(cfg[i] for i in idxs)
            arr[key] += val
        denom = total // int(np.prod(shape)) if shape else total
        means[mask] = arr / denom

    effects = {}
    energies = {}
    for mask in sorted(subsets, key=lambda m: (bin(m).count("1"), m)):
        idxs = subset_idx[mask]
        shape = tuple(ms[i] for i in idxs)
        eff = np.array(means[mask], copy=True)
        if mask != 0:
            eff = eff - effects[0]
        sub = (mask - 1) & mask
        while sub:
            sub_idxs = subset_idx[sub]
            sub_arr = effects[sub]
            reshape = []
            pos = {idx: j for j, idx in enumerate(idxs)}
            k = 0
            for idx in idxs:
                if idx in sub_idxs:
                    reshape.append(sub_arr.shape[k])
                    k += 1
                else:
                    reshape.append(1)
            eff = eff - sub_arr.reshape(tuple(reshape))
            sub = (sub - 1) & mask
        effects[mask] = eff
        energies[mask] = float(np.mean(eff ** 2))

    win_masks = all_window_masks(n, width)
    allowed_energy = 0.0
    forbidden_energy = 0.0
    allowed_masks = []
    forbidden_masks = []
    for mask, energy in energies.items():
        if allowed_mask(mask, win_masks):
            allowed_energy += energy
            allowed_masks.append((mask, energy))
        else:
            forbidden_energy += energy
            forbidden_masks.append((mask, energy))

    forbidden_masks.sort(key=lambda item: item[1], reverse=True)
    return allowed_energy, forbidden_energy, forbidden_masks[:15], energies


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, default=9)
    parser.add_argument("--width", type=int, required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    rng = np.random.default_rng(args.seed)
    label, ms, fs = build_family(args.family, args.n)
    result = verify_system(ms, fs)
    good = set(result["good_configs"])
    rank, _ = rank_bad_configs(ms, fs, good)
    cfgs = list(all_configs(ms))
    actual = np.array([0.0 if cfg in good else rank[cfg] + 1.0 for cfg in cfgs], dtype=np.float64)
    shuffled = rng.permutation(actual)

    aa, af, atop, _ = anova_spectrum(ms, actual, args.width)
    sa, sf, stop, _ = anova_spectrum(ms, shuffled, args.width)
    print(label, f"width={args.width}")
    print(f"  actual forbidden_energy_frac = {af / (aa + af):.6f}")
    print(f"  shuffled forbidden_energy_frac = {sf / (sa + sf):.6f}")
    print("  top actual forbidden masks:")
    for mask, energy in atop:
        print(f"  - mask={mask:b} energy={energy:.6f}")
    print("  top shuffled forbidden masks:")
    for mask, energy in stop:
        print(f"  - mask={mask:b} energy={energy:.6f}")


if __name__ == "__main__":
    main()
