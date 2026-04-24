#!/usr/bin/env python3
"""Forbidden-interaction profiles for candidate slice-code features."""

from __future__ import annotations

import argparse
import os
import sys

import numpy as np


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
if INFO_DIR not in sys.path:
    sys.path.insert(0, INFO_DIR)

from anova_interaction_spectrum import anova_spectrum
from slice_feature_search import build_family, make_feature_bank
from twolevel_spectrum import future_fc, fc as fc_fn
from verifier import all_configs, verify_system  # type: ignore


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, default=9)
    parser.add_argument(
        "--features",
        nargs="*",
        default=[
            "interior_sum",
            "even_val_sum",
            "odd_val_sum",
            "weight_pair_00",
            "weight_pair_01",
            "weight_pair_02",
            "weight_pair_10",
            "weight_pair_12",
            "weight_pair_22",
        ],
    )
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    rng = np.random.default_rng(args.seed)
    label, ms, fs = build_family(args.family, args.n)
    result = verify_system(ms, fs)
    good = set(result["good_configs"])
    cfgs = list(all_configs(ms))
    bank = make_feature_bank(cfgs)
    bad, _, _, ff = future_fc(ms, fs, good)
    ff_full = np.array([0.0 if c in good else float(ff[c]) for c in cfgs], dtype=np.float64)
    fc_full = np.array([0.0 if c in good else float(fc_fn(c)) for c in cfgs], dtype=np.float64)

    print(label, f"width={args.n - 2}")
    for name, vals in [("fc", fc_full), ("FutureFc", ff_full)] + [
        (feat, np.array(bank[feat], dtype=np.float64)) for feat in args.features
    ]:
        shuffled = rng.permutation(vals)
        aa, af, _, _ = anova_spectrum(ms, vals, args.n - 2)
        sa, sf, _, _ = anova_spectrum(ms, shuffled, args.n - 2)
        print(
            f"{name}: actual_forbid={af/(aa+af):.6f} "
            f"shuffled_forbid={sf/(sa+sf):.6f}"
        )


if __name__ == "__main__":
    main()
