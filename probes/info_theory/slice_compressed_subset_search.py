#!/usr/bin/env python3
"""Compressed exact-subset search for residual slice codes.

Idea:
1. Build the full candidate feature tuple once for every bad configuration.
2. Compress to unique signatures `(base, full_feature_tuple) -> rank`.
3. Test subsets only on these unique signatures.

This avoids rescanning all bad configurations for every candidate subset.
"""

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
from twolevel_spectrum import future_fc, constant_ff_rank
from verifier import verify_system  # type: ignore
from slice_subset_search import DEFAULT_CANDIDATES


def build_compressed_dataset(family: str, n: int, candidates: list[str], include_base: bool):
    label, ms, fs = build_family(family, n)
    result = verify_system(ms, fs)
    good = set(result["good_configs"])
    bad, _, adj, ff = future_fc(ms, fs, good)
    cfr = constant_ff_rank(bad, adj, ff)
    bank = make_feature_bank(bad)

    signatures = {}
    collisions = []
    for idx, cfg in enumerate(bad):
        base = None
        if include_base:
            base = (ff[cfg], boundary6(cfg), base_invariants(cfg))
        feat_tuple = tuple(bank[name][idx] for name in candidates)
        sig = (base, feat_tuple) if include_base else feat_tuple
        rank = cfr[cfg]
        prev = signatures.get(sig)
        if prev is None:
            signatures[sig] = rank
        elif prev != rank:
            collisions.append((sig, prev, rank))

    return {
        "label": label,
        "signatures": list(signatures.items()),
        "candidates": candidates,
        "full_exact": len(collisions) == 0,
        "num_collisions": len(collisions),
        "num_bad": len(bad),
        "num_signatures": len(signatures),
        "num_ranks": len(set(cfr.values())),
    }


def exact_subset_stats(dataset, subset: tuple[str, ...]):
    idxs = [dataset["candidates"].index(name) for name in subset]
    mapping = {}
    for sig, rank in dataset["signatures"]:
        if isinstance(sig, tuple) and len(sig) == 2 and isinstance(sig[1], tuple):
            base, feat_tuple = sig
            key = (base, tuple(feat_tuple[i] for i in idxs))
        else:
            feat_tuple = sig
            key = tuple(feat_tuple[i] for i in idxs)
        prev = mapping.get(key)
        if prev is None:
            mapping[key] = rank
        elif prev != rank:
            return None

    rank_mult = Counter(mapping.values())
    return {
        "tuples": len(mapping),
        "ranks": len(rank_mult),
        "max_tuples_per_rank": max(rank_mult.values()),
        "mean_tuples_per_rank": len(mapping) / len(rank_mult),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--max-size", type=int, default=6)
    parser.add_argument("--with-base", action="store_true")
    parser.add_argument("--candidates", nargs="*", default=DEFAULT_CANDIDATES)
    parser.add_argument("--stop-after-first", action="store_true")
    args = parser.parse_args()

    dataset = build_compressed_dataset(args.family, args.n, args.candidates, args.with_base)
    print(
        f"label={dataset['label']} bad={dataset['num_bad']} "
        f"full_signatures={dataset['num_signatures']} ranks={dataset['num_ranks']} "
        f"full_exact={dataset['full_exact']} collisions={dataset['num_collisions']}"
    )

    for r in range(1, args.max_size + 1):
        found = []
        for subset in itertools.combinations(args.candidates, r):
            stats = exact_subset_stats(dataset, subset)
            if stats is not None:
                found.append((subset, stats))
                if args.stop_after_first:
                    break
        if found:
            print(f"minimum exact subset size = {r}")
            for subset, stats in found[:30]:
                print(
                    f"subset={subset} tuples={stats['tuples']} ranks={stats['ranks']} "
                    f"max_tuples_per_rank={stats['max_tuples_per_rank']} "
                    f"mean_tuples_per_rank={stats['mean_tuples_per_rank']:.3f}"
                )
            return
    print(f"no exact subset of size <= {args.max_size}")


if __name__ == "__main__":
    main()
