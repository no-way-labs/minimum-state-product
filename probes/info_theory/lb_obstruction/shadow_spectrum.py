#!/usr/bin/env python3
"""Forbidden spectra for explicit shadow-cycle obstruction scalars."""

from __future__ import annotations

import argparse
import os
import sys

import numpy as np


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
DOCS_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "docs")
for path in [INFO_DIR, CLAUDE_DIR, DOCS_DIR]:
    if path not in sys.path:
        sys.path.insert(0, path)

from anova_interaction_spectrum import anova_spectrum
from verify_lower_bound import check_cycle_consistency, construct_sweep_cycle, find_shadow_cycle  # type: ignore
from verifier import all_configs  # type: ignore


def sweep_cycle(ms, nb_vals):
    cyc = construct_sweep_cycle(ms, len(ms), nb_vals)
    if cyc is None:
        raise RuntimeError("failed to construct sweep cycle")
    ok, det, msg = check_cycle_consistency(cyc, len(ms), ms)
    if not ok:
        raise RuntimeError(msg)
    shadow = find_shadow_cycle(det, set(cyc), ms, len(ms), max_len=100)
    if shadow is None:
        raise RuntimeError("no shadow cycle found")
    return cyc, det, shadow


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--ms", nargs="+", type=int, required=True)
    parser.add_argument(
        "--nb-vals",
        nargs="*",
        default=[],
        help="Assignments j=v for ternary positions, e.g. 2=1 4=2",
    )
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    ms = args.ms
    n = len(ms)
    nb_vals = {}
    for item in args.nb_vals:
        j_s, v_s = item.split("=")
        nb_vals[int(j_s)] = int(v_s)

    cycle, det, shadow = sweep_cycle(ms, nb_vals)
    cfgs = list(all_configs(ms))
    shadow_set = set(shadow)
    indicator = np.array([1.0 if cfg in shadow_set else 0.0 for cfg in cfgs], dtype=np.float64)
    rng = np.random.default_rng(args.seed)
    shuffled = rng.permutation(indicator)
    aa, af, _, _ = anova_spectrum(ms, indicator, n - 2)
    sa, sf, _, _ = anova_spectrum(ms, shuffled, n - 2)
    print(f"ms={tuple(ms)} shadow_len={len(shadow)} cycle_len={len(cycle)}")
    print(f"  actual_forbid={af/(aa+af):.6f}")
    print(f"  shuffled_forbid={sf/(sa+sf):.6f}")


if __name__ == "__main__":
    main()
