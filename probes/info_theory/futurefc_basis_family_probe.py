#!/usr/bin/env python3
"""Probe small basis families for exact FutureFc decoding across sizes."""

from __future__ import annotations

import argparse
import os
import sys


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
if INFO_DIR not in sys.path:
    sys.path.insert(0, INFO_DIR)

from futurefc_subset_search import build_dataset


def lag_11_features(cfg):
    n = len(cfg)
    starts = range(2, n - 2)
    hits2 = [j for j in starts if (cfg[j], cfg[(j + 2) % n]) == (1, 1)]
    hits3 = [j for j in starts if (cfg[j], cfg[(j + 3) % n]) == (1, 1)]
    return {
        "count_lag2_11": len(hits2),
        "weight_lag2_11": sum(hits2),
        "weight_lag3_11": sum(hits3),
    }


def exact_on_dataset(ds, features):
    for name in ["count_lag2_11", "weight_lag2_11", "weight_lag3_11"]:
        if name not in ds["bank"]:
            ds["bank"][name] = []
    for idx, cfg in enumerate(ds["bad"]):
        if idx < len(ds["bank"]["count_lag2_11"]):
            continue
        vals = lag_11_features(cfg)
        for k, v in vals.items():
            ds["bank"][k].append(v)

    mapping = {}
    exact = True
    for idx, cfg in enumerate(ds["bad"]):
        tup = (ds["prefix"][idx], tuple(ds["bank"][name][idx] for name in features))
        v = ds["ff"][cfg]
        prev = mapping.get(tup)
        if prev is None:
            mapping[tup] = v
        elif prev != v:
            exact = False
            break
    return exact, len(mapping), len(set(ds["ff"].values())), len(ds["bad"])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n-from", type=int, required=True)
    parser.add_argument("--n-to", type=int, required=True)
    parser.add_argument("--features", nargs="+", required=True)
    args = parser.parse_args()

    print("features:", args.features)
    for n in range(args.n_from, args.n_to + 1):
        ds = build_dataset(args.family, n, include_boundary=True, include_base_invariants=True)
        exact, tuples, values, bad = exact_on_dataset(ds, args.features)
        print(
            f"{ds['label']}: exact={exact} tuples={tuples} values={values} bad={bad}"
        )


if __name__ == "__main__":
    main()
