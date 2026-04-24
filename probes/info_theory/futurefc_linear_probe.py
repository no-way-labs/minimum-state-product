#!/usr/bin/env python3
"""Affine probes for FutureFc-related targets on custom prefixes."""

from __future__ import annotations

import argparse
import os
import sys
from fractions import Fraction

import numpy as np


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
if INFO_DIR not in sys.path:
    sys.path.insert(0, INFO_DIR)

from futurefc_fiber_probe import build_dataset_custom_prefix, fc, lag_11_features
from slice_feature_search import base_invariants


TARGETS = {"FutureFc", "fc", "gap", "exp2", "int21", "exp2_weight"}


def target_value(ds, cfg, target):
    if target == "FutureFc":
        return float(ds["ff"][cfg])
    if target == "fc":
        return float(fc(cfg))
    if target == "gap":
        return float(ds["ff"][cfg] - fc(cfg))
    tp = base_invariants(cfg)
    if target == "exp2":
        return float(tp[0])
    if target == "int21":
        return float(tp[1])
    if target == "exp2_weight":
        return float(tp[2])
    raise ValueError(target)


def flatten_prefix(prefix):
    flat = []
    for part in prefix:
        if isinstance(part, tuple):
            flat.extend(float(x) for x in part)
        else:
            flat.append(float(part))
    return flat


def ensure_features(ds, feature_names):
    needed = [name for name in feature_names if name not in ds["bank"]]
    if not needed:
        return
    for name in needed:
        ds["bank"][name] = []
    for cfg in ds["bad"]:
        vals = lag_11_features(cfg)
        for name in needed:
            ds["bank"][name].append(vals[name])


def evaluate(family, n, prefix_parts, feature_names, target):
    ds = build_dataset_custom_prefix(family, n, prefix_parts)
    ensure_features(ds, feature_names)
    prefix_width = len(flatten_prefix(ds["prefix"][0])) if ds["prefix"] else 0
    X = np.ones((len(ds["bad"]), 1 + prefix_width + len(feature_names)), dtype=np.float64)
    y = np.zeros(len(ds["bad"]), dtype=np.float64)
    for i, cfg in enumerate(ds["bad"]):
        row = [1.0]
        row.extend(flatten_prefix(ds["prefix"][i]))
        row.extend(float(ds["bank"][name][i]) for name in feature_names)
        X[i, :] = np.array(row, dtype=np.float64)
        y[i] = target_value(ds, cfg, target)
    coeffs, *_ = np.linalg.lstsq(X, y, rcond=None)
    pred = X @ coeffs
    resid = y - pred
    rmse = float(np.sqrt(np.mean(resid**2)))
    max_abs = float(np.max(np.abs(resid)))
    exact = bool(np.allclose(pred, y, atol=1e-9, rtol=0.0))
    rounded = int(np.sum(np.rint(pred) == y))
    return ds["label"], coeffs, rmse, max_abs, exact, rounded, len(y)


def coeff_labels(prefix_parts, feature_names):
    labels = ["const"]
    for part in prefix_parts:
        if part == "boundary6":
            labels.extend([f"boundary6[{i}]" for i in range(6)])
        else:
            labels.append(part)
    labels.extend(feature_names)
    return labels


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--prefix-parts", nargs="*", default=["boundary6"])
    parser.add_argument("--features", nargs="+", required=True)
    parser.add_argument("--target", choices=sorted(TARGETS), required=True)
    parser.add_argument("--show-rationals", action="store_true")
    args = parser.parse_args()

    label, coeffs, rmse, max_abs, exact, rounded, total = evaluate(
        args.family, args.n, args.prefix_parts, args.features, args.target
    )
    print(label)
    print("target:", args.target)
    print("prefix_parts:", args.prefix_parts)
    print("features:", args.features)
    print(f"rmse={rmse:.12f} max_abs={max_abs:.12f} exact={exact} rounded={rounded}/{total}")
    labels = coeff_labels(args.prefix_parts, args.features)
    if args.show_rationals:
        vals = [str(Fraction(float(c)).limit_denominator()) for c in coeffs]
    else:
        vals = [f"{float(c):.12f}" for c in coeffs]
    for name, val in zip(labels, vals):
        print(f"  {name}: {val}")


if __name__ == "__main__":
    main()
