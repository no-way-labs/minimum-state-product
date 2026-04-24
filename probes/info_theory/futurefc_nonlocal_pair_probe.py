#!/usr/bin/env python3
"""Probe non-adjacent pair features for FutureFc collision resolution."""

from __future__ import annotations

import argparse
import os
import sys


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
if INFO_DIR not in sys.path:
    sys.path.insert(0, INFO_DIR)

from futurefc_subset_search import build_dataset
from slice_subset_search import DEFAULT_CANDIDATES


def lag_pair_features(cfg, lag: int):
    n = len(cfg)
    out = {}
    starts = range(2, n - 2)
    for a in range(3):
        for b in range(3):
            hits = [j for j in starts if (cfg[j], cfg[(j + lag) % n]) == (a, b)]
            key = f"{a}{b}"
            out[f"count_lag{lag}_{key}"] = len(hits)
            out[f"weight_lag{lag}_{key}"] = sum(hits)
    return out


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--lag", type=int, required=True)
    parser.add_argument("--base-features", nargs="+", required=True)
    parser.add_argument("--limit", type=int, default=30)
    args = parser.parse_args()

    ds = build_dataset(args.family, args.n, include_boundary=True, include_base_invariants=True)
    extra_bank = {}
    for prefix in [f"count_lag{args.lag}_", f"weight_lag{args.lag}_"]:
        for a in range(3):
            for b in range(3):
                extra_bank[f"{prefix}{a}{b}"] = []

    for cfg in ds["bad"]:
        vals = lag_pair_features(cfg, args.lag)
        for key, value in vals.items():
            extra_bank[key].append(value)

    print(ds["label"], f"lag={args.lag}")
    print("base features:", args.base_features)
    exacts = []
    for extra_name, arr in extra_bank.items():
        mapping = {}
        exact = True
        for idx, cfg in enumerate(ds["bad"]):
            tup = (
                ds["prefix"][idx],
                tuple(ds["bank"][name][idx] for name in args.base_features),
                arr[idx],
            )
            val = ds["ff"][cfg]
            prev = mapping.get(tup)
            if prev is None:
                mapping[tup] = val
            elif prev != val:
                exact = False
                break
        if exact:
            exacts.append((extra_name, len(mapping)))

    if exacts:
        print("exact single nonlocal pair features:", len(exacts))
        for name, tuples in exacts[: args.limit]:
            print(name, tuples)
    else:
        print("no exact single nonlocal pair feature")


if __name__ == "__main__":
    main()
