#!/usr/bin/env python3
"""Compute exact ANOVA energy for a single support mask."""

from __future__ import annotations

import itertools
from typing import Iterable

import numpy as np


def mask_indices(mask: int, n: int) -> tuple[int, ...]:
    return tuple(i for i in range(n) if (mask >> i) & 1)


def submasks(mask: int) -> list[int]:
    out = [0]
    sub = mask
    while sub:
        out.append(sub)
        sub = (sub - 1) & mask
    return out


def effect_energy_for_mask(ms: list[int], values: np.ndarray, mask: int) -> float:
    n = len(ms)
    total = int(np.prod(ms))
    configs = list(itertools.product(*(range(m) for m in ms)))
    subsets = sorted(submasks(mask), key=lambda m: (bin(m).count("1"), m))
    subset_idx = {sub: mask_indices(sub, n) for sub in subsets}

    means = {}
    for sub in subsets:
        idxs = subset_idx[sub]
        shape = tuple(ms[i] for i in idxs)
        arr = np.zeros(shape if shape else (), dtype=np.float64)
        for cfg, val in zip(configs, values):
            key = tuple(cfg[i] for i in idxs)
            arr[key] += val
        denom = total // int(np.prod(shape)) if shape else total
        means[sub] = arr / denom

    effects = {}
    for sub in subsets:
        idxs = subset_idx[sub]
        eff = np.array(means[sub], copy=True)
        if sub != 0:
            eff = eff - effects[0]
        part = (sub - 1) & sub
        while part:
            part_idxs = subset_idx[part]
            part_arr = effects[part]
            reshape = []
            k = 0
            for idx in idxs:
                if idx in part_idxs:
                    reshape.append(part_arr.shape[k])
                    k += 1
                else:
                    reshape.append(1)
            eff = eff - part_arr.reshape(tuple(reshape))
            part = (part - 1) & sub
        effects[sub] = eff

    return float(np.mean(effects[mask] ** 2))
