#!/usr/bin/env python3
"""Search for exact feature subsets for FutureFc."""

from __future__ import annotations

import argparse
import itertools
import os
import sys
from collections import Counter


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
if INFO_DIR not in sys.path:
    sys.path.insert(0, INFO_DIR)

from slice_feature_search import build_family, make_feature_bank, boundary6, base_invariants
from twolevel_spectrum import future_fc
from verifier import verify_system  # type: ignore
from slice_subset_search import DEFAULT_CANDIDATES


def build_dataset(family: str, n: int, include_boundary: bool, include_base_invariants: bool):
    label, ms, fs = build_family(family, n)
    result = verify_system(ms, fs)
    good = set(result["good_configs"])
    bad, _, _, ff = future_fc(ms, fs, good)
    bank = make_feature_bank(bad)
    prefix = []
    for cfg in bad:
        parts = []
        if include_boundary:
            parts.append(boundary6(cfg))
        if include_base_invariants:
            parts.append(base_invariants(cfg))
        prefix.append(tuple(parts))
    return {
        "label": label,
        "bad": bad,
        "ff": ff,
        "bank": bank,
        "prefix": prefix,
    }


def exact_subset_stats(dataset, features: list[str]):
    mapping = {}
    for idx, cfg in enumerate(dataset["bad"]):
        tup = (dataset["prefix"][idx], tuple(dataset["bank"][name][idx] for name in features))
        val = dataset["ff"][cfg]
        prev = mapping.get(tup)
        if prev is None:
            mapping[tup] = val
        elif prev != val:
            return None
    mult = Counter(mapping.values())
    return {
        "tuples": len(mapping),
        "values": len(mult),
        "max_tuples_per_value": max(mult.values()),
        "mean_tuples_per_value": len(mapping) / len(mult),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--max-size", type=int, default=4)
    parser.add_argument("--with-boundary", action="store_true")
    parser.add_argument("--with-base-invariants", action="store_true")
    parser.add_argument("--candidates", nargs="*", default=DEFAULT_CANDIDATES)
    args = parser.parse_args()

    dataset = build_dataset(args.family, args.n, args.with_boundary, args.with_base_invariants)
    print(f"label={dataset['label']} bad={len(dataset['bad'])} values={len(set(dataset['ff'].values()))}")
    for r in range(1, args.max_size + 1):
        found = []
        for subset in itertools.combinations(args.candidates, r):
            stats = exact_subset_stats(dataset, list(subset))
            if stats is not None:
                found.append((subset, stats))
        if found:
            print(f"minimum exact subset size = {r}")
            for subset, stats in found[:30]:
                print(
                    f"subset={subset} tuples={stats['tuples']} values={stats['values']} "
                    f"max_tuples_per_value={stats['max_tuples_per_value']} "
                    f"mean_tuples_per_value={stats['mean_tuples_per_value']:.3f}"
                )
            return
    print(f"no exact subset of size <= {args.max_size}")


if __name__ == "__main__":
    main()
