#!/usr/bin/env python3
"""Search for exact feature subsets for the slice-rank code."""

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

from slice_feature_search import build_family, make_feature_bank
from twolevel_spectrum import future_fc, constant_ff_rank
from slice_feature_search import boundary6, base_invariants
from verifier import verify_system  # type: ignore


DEFAULT_CANDIDATES = [
    "interior_sum",
    "even_val_sum",
    "odd_val_sum",
    "count_val_0",
    "count_val_1",
    "count_val_2",
    "weight_pair_00",
    "weight_pair_01",
    "weight_pair_02",
    "weight_pair_10",
    "weight_pair_11",
    "weight_pair_12",
    "weight_pair_20",
    "weight_pair_21",
    "weight_pair_22",
]


def build_dataset(family: str, n: int, include_base: bool):
    label, ms, fs = build_family(family, n)
    result = verify_system(ms, fs)
    good = set(result["good_configs"])
    bad, _, adj, ff = future_fc(ms, fs, good)
    cfr = constant_ff_rank(bad, adj, ff)
    bank = make_feature_bank(bad)
    base = None
    if include_base:
        base = [(ff[c], boundary6(c), base_invariants(c)) for c in bad]
    return {
        "label": label,
        "bad": bad,
        "cfr": cfr,
        "bank": bank,
        "base": base,
    }

def exact_subset_stats(dataset, features: list[str]):
    cfr = dataset["cfr"]
    bank = dataset["bank"]
    mapping = {}
    for idx, cfg in enumerate(dataset["bad"]):
        if dataset["base"] is None:
            tup = tuple(bank[name][idx] for name in features)
        else:
            tup = (dataset["base"][idx], tuple(bank[name][idx] for name in features))
        rank = cfr[cfg]
        prev = mapping.get(tup)
        if prev is None:
            mapping[tup] = rank
        elif prev != rank:
            return {
                "label": dataset["label"],
                "exact": False,
                "tuples": len(mapping),
                "ranks": len(set(cfr.values())),
            }

    if not mapping:
        return {
            "label": dataset["label"],
            "exact": False,
            "tuples": 0,
            "ranks": len(set(cfr.values())),
        }

    rank_mult = Counter(mapping.values())
    return {
        "label": dataset["label"],
        "exact": True,
        "tuples": len(mapping),
        "ranks": len(rank_mult),
        "max_tuples_per_rank": max(rank_mult.values()),
        "mean_tuples_per_rank": len(mapping) / len(rank_mult),
    }


def search(family: str, n: int, candidates: list[str], max_size: int, include_base: bool):
    dataset = build_dataset(family, n, include_base)
    for r in range(1, max_size + 1):
        exacts = []
        for subset in itertools.combinations(candidates, r):
            stats = exact_subset_stats(dataset, list(subset))
            if stats["exact"]:
                exacts.append((subset, stats))
        if exacts:
            return r, exacts
    return None, []


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--max-size", type=int, default=4)
    parser.add_argument("--candidates", nargs="*", default=DEFAULT_CANDIDATES)
    parser.add_argument("--with-base", action="store_true")
    args = parser.parse_args()

    r, exacts = search(args.family, args.n, args.candidates, args.max_size, args.with_base)
    if r is None:
        print(f"no exact subset of size <= {args.max_size}")
        return
    print(f"minimum exact subset size = {r}")
    for subset, stats in exacts:
        print(
            f"subset={subset} tuples={stats['tuples']} ranks={stats['ranks']} "
            f"max_tuples_per_rank={stats['max_tuples_per_rank']} "
            f"mean_tuples_per_rank={stats['mean_tuples_per_rank']:.3f}"
        )


if __name__ == "__main__":
    main()
