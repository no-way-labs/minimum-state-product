#!/usr/bin/env python3
"""Forbidden fractions for good-cycle indicators on explicit families and witnesses."""

from __future__ import annotations

import argparse
import os
import sys
from itertools import product as iproduct

import numpy as np


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
DOCS_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "docs")
LB_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory", "lb_obstruction")
for path in [INFO_DIR, CLAUDE_DIR, DOCS_DIR, LB_DIR]:
    if path not in sys.path:
        sys.path.insert(0, path)

from anova_interaction_spectrum import anova_spectrum
from cycle_info_metrics import sol3_v1_rules
from cup2_theorem import build_system as build_cup2_system  # type: ignore
from verifier import all_configs, verify_system  # type: ignore
from verify_lower_bound import construct_sweep_cycle
from ec_derived_spectrum import simple_baf_cycle


def valid_good_indicator(family: str, n: int):
    if family == "cup2":
        ms, fs = build_cup2_system(n)
    elif family == "sol3":
        ms = [3] * n
        fs = sol3_v1_rules(ms, n)
    else:
        raise ValueError(family)
    result = verify_system(ms, fs)
    good = set(result["good_configs"])
    cfgs = list(all_configs(ms))
    vals = np.array([1.0 if cfg in good else 0.0 for cfg in cfgs], dtype=np.float64)
    aa, af, _, _ = anova_spectrum(ms, vals, n - 2)
    return ms, len(good), af / (aa + af) if aa + af else 0.0


def shadow_good_indicator(ms, nb_vals):
    n = len(ms)
    cyc = construct_sweep_cycle(ms, n, nb_vals)
    if cyc is None:
        raise RuntimeError("failed to build sweep cycle")
    good = set(cyc)
    cfgs = list(iproduct(*[range(m) for m in ms]))
    vals = np.array([1.0 if cfg in good else 0.0 for cfg in cfgs], dtype=np.float64)
    aa, af, _, _ = anova_spectrum(ms, vals, n - 2)
    return len(good), af / (aa + af) if aa + af else 0.0


def ec_good_indicator(n: int):
    ms = [2, 2, 2] + [3] * (n - 3)
    good, _ = simple_baf_cycle(ms)
    good = set(good)
    cfgs = list(iproduct(*[range(m) for m in ms]))
    vals = np.array([1.0 if cfg in good else 0.0 for cfg in cfgs], dtype=np.float64)
    aa, af, _, _ = anova_spectrum(ms, vals, n - 2)
    return ms, len(good), af / (aa + af) if aa + af else 0.0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--mode",
        choices=["valid_cup2", "valid_sol3", "shadow_explicit", "ec_baf"],
        required=True,
    )
    parser.add_argument("--n-from", type=int, required=True)
    parser.add_argument("--n-to", type=int, required=True)
    args = parser.parse_args()

    if args.mode == "valid_cup2":
        for n in range(args.n_from, args.n_to + 1):
            ms, count, frac = valid_good_indicator("cup2", n)
            print(f"CUP-2(n={n}) good_count={count} forbid={frac:.6f}")
    elif args.mode == "valid_sol3":
        for n in range(args.n_from, args.n_to + 1):
            ms, count, frac = valid_good_indicator("sol3", n)
            print(f"Sol3(n={n}) good_count={count} forbid={frac:.6f}")
    elif args.mode == "shadow_explicit":
        for n in range(args.n_from, args.n_to + 1):
            ms = [2, 2, 2] + [3] * (n - 3)
            ternary = [i for i, m in enumerate(ms) if m == 3]
            nb_vals = {i: 1 for i in ternary}
            count, frac = shadow_good_indicator(ms, nb_vals)
            print(f"shadow_explicit(n={n}) good_count={count} forbid={frac:.6f}")
    elif args.mode == "ec_baf":
        for n in range(args.n_from, args.n_to + 1):
            ms, count, frac = ec_good_indicator(n)
            print(f"ec_baf(n={n}) good_count={count} forbid={frac:.6f}")


if __name__ == "__main__":
    main()
