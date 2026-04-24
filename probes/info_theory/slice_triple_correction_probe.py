#!/usr/bin/env python3
"""Probe whether length-3 motif statistics resolve residual slice-code collisions.

This script tests single additional triple features on top of a fixed base
scaffold. It is aimed at the first failing exact-decoder case:
`CUP-2(n=12)`.
"""

from __future__ import annotations

import argparse
import os
import sys


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
if INFO_DIR not in sys.path:
    sys.path.insert(0, INFO_DIR)

from slice_feature_search import build_family, boundary6, base_invariants, make_feature_bank
from twolevel_spectrum import future_fc, constant_ff_rank
from verifier import verify_system  # type: ignore


def triple_features(cfg):
    n = len(cfg)
    out = {}
    # Use the same left/right boundary convention as the pair features:
    # start positions 2..n-3 so that the window can touch either boundary side.
    starts = range(2, n - 2)
    for a in range(3):
        for b in range(3):
            for c in range(3):
                hits = [j for j in starts if (cfg[j], cfg[(j + 1) % n], cfg[(j + 2) % n]) == (a, b, c)]
                key = f"{a}{b}{c}"
                out[f"count_triple_{key}"] = len(hits)
                out[f"weight_triple_{key}"] = sum(hits)
    return out


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument(
        "--base-features",
        nargs="+",
        required=True,
    )
    parser.add_argument("--limit", type=int, default=30)
    args = parser.parse_args()

    label, ms, fs = build_family(args.family, args.n)
    result = verify_system(ms, fs)
    good = set(result["good_configs"])
    bad, _, adj, ff = future_fc(ms, fs, good)
    cfr = constant_ff_rank(bad, adj, ff)
    bank = make_feature_bank(bad)

    extra_bank = {}
    for key in [f"count_triple_{a}{b}{c}" for a in range(3) for b in range(3) for c in range(3)]:
        extra_bank[key] = []
    for key in [f"weight_triple_{a}{b}{c}" for a in range(3) for b in range(3) for c in range(3)]:
        extra_bank[key] = []

    for cfg in bad:
        vals = triple_features(cfg)
        for key, val in vals.items():
            extra_bank[key].append(val)

    print(label)
    print("base features:", args.base_features)
    results = []
    for extra_name, vals in extra_bank.items():
        mapping = {}
        exact = True
        for idx, cfg in enumerate(bad):
            tup = (
                (ff[cfg], boundary6(cfg), base_invariants(cfg)),
                tuple(bank[name][idx] for name in args.base_features),
                vals[idx],
            )
            rank = cfr[cfg]
            prev = mapping.get(tup)
            if prev is None:
                mapping[tup] = rank
            elif prev != rank:
                exact = False
                break
        results.append((exact, len(mapping), extra_name))

    exacts = [item for item in results if item[0]]
    if exacts:
        print(f"exact single triple features: {len(exacts)}")
        for _, tuples, name in exacts[: args.limit]:
            print(name, tuples)
    else:
        print("no exact single triple feature")
        results.sort(key=lambda item: item[1], reverse=True)
        print("best non-exact refinements:")
        for _, tuples, name in results[: args.limit]:
            print(name, tuples)


if __name__ == "__main__":
    main()
