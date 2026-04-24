#!/usr/bin/env python3
"""Affine-linear fits for the constant-FutureFc slice rank."""

from __future__ import annotations

import argparse
import os
import sys

import numpy as np


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
if INFO_DIR not in sys.path:
    sys.path.insert(0, INFO_DIR)

from slice_feature_search import build_family, make_feature_bank
from twolevel_spectrum import future_fc, constant_ff_rank
from verifier import verify_system  # type: ignore


def evaluate(family: str, n: int, features: list[str]):
    label, ms, fs = build_family(family, n)
    result = verify_system(ms, fs)
    good = set(result["good_configs"])
    bad, bad_set, adj, ff = future_fc(ms, fs, good)
    cfr = constant_ff_rank(bad, adj, ff)
    bank = make_feature_bank(bad)
    y = np.array([float(cfr[c]) for c in bad], dtype=np.float64)
    X = np.ones((len(bad), 1 + len(features)), dtype=np.float64)
    for j, name in enumerate(features, start=1):
        X[:, j] = np.array(bank[name], dtype=np.float64)
    coeffs, *_ = np.linalg.lstsq(X, y, rcond=None)
    pred = X @ coeffs
    resid = y - pred
    rmse = float(np.sqrt(np.mean(resid ** 2)))
    mae = float(np.mean(np.abs(resid)))
    max_abs = float(np.max(np.abs(resid)))
    exact_rounded = int(np.sum(np.rint(pred) == y))
    return label, coeffs, rmse, mae, max_abs, exact_rounded, len(bad)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n-from", type=int, required=True)
    parser.add_argument("--n-to", type=int, required=True)
    parser.add_argument("--features", nargs="+", required=True)
    args = parser.parse_args()

    print("features:", args.features)
    for n in range(args.n_from, args.n_to + 1):
        label, coeffs, rmse, mae, max_abs, exact_rounded, total = evaluate(args.family, n, args.features)
        print(f"{label}: rmse={rmse:.6f} mae={mae:.6f} max_abs={max_abs:.6f} rounded={exact_rounded}/{total}")
        print("  coeffs:", " ".join(f"{c:.6f}" for c in coeffs))


if __name__ == "__main__":
    main()
