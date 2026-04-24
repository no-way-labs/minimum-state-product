#!/usr/bin/env python3
"""Evaluate fixed slice-rank feature scaffolds across n/families."""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
if INFO_DIR not in sys.path:
    sys.path.insert(0, INFO_DIR)

from slice_feature_search import (
    build_family,
    boundary6,
    mutual_information,
    entropy,
    base_invariants,
    make_feature_bank,
)
from twolevel_spectrum import future_fc, constant_ff_rank
from verifier import verify_system  # type: ignore


def evaluate(family: str, n: int, features: list[str]):
    label, ms, fs = build_family(family, n)
    result = verify_system(ms, fs)
    good = set(result["good_configs"])
    bad, bad_set, adj, ff = future_fc(ms, fs, good)
    cfr = constant_ff_rank(bad, adj, ff)
    ys = [cfr[c] for c in bad]
    H = entropy(Counter(ys))
    base = [(ff[c], boundary6(c), base_invariants(c)) for c in bad]
    bank = make_feature_bank(bad)
    keys = [(*base[i], *(bank[name][i] for name in features)) for i in range(len(bad))]
    mi = mutual_information(keys, ys)
    return label, H, mi


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n-from", type=int, required=True)
    parser.add_argument("--n-to", type=int, required=True)
    parser.add_argument("--features", nargs="+", required=True)
    args = parser.parse_args()

    print("features:", args.features)
    for n in range(args.n_from, args.n_to + 1):
        label, H, mi = evaluate(args.family, n, args.features)
        print(f"{label}: H={H:.6f} MI={mi:.6f} exact={abs(H-mi) < 1e-12}")


if __name__ == "__main__":
    main()
