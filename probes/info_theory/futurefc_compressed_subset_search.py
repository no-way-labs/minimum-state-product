#!/usr/bin/env python3
"""Compressed exact-subset search for FutureFc."""

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

from futurefc_subset_search import build_dataset
from slice_subset_search import DEFAULT_CANDIDATES


def build_compressed_dataset(family: str, n: int, candidates: list[str], include_boundary: bool, include_base_invariants: bool):
    ds = build_dataset(family, n, include_boundary, include_base_invariants)
    signatures = {}
    collisions = []
    for idx, cfg in enumerate(ds["bad"]):
        sig = (ds["prefix"][idx], tuple(ds["bank"][name][idx] for name in candidates))
        val = ds["ff"][cfg]
        prev = signatures.get(sig)
        if prev is None:
            signatures[sig] = val
        elif prev != val:
            collisions.append((sig, prev, val))
    return {
        "label": ds["label"],
        "signatures": list(signatures.items()),
        "candidates": candidates,
        "full_exact": len(collisions) == 0,
        "num_bad": len(ds["bad"]),
        "num_signatures": len(signatures),
        "num_values": len(set(ds["ff"].values())),
        "num_collisions": len(collisions),
    }


def exact_subset_stats(dataset, subset: tuple[str, ...]):
    idxs = [dataset["candidates"].index(name) for name in subset]
    mapping = {}
    for sig, val in dataset["signatures"]:
        prefix, feat_tuple = sig
        key = (prefix, tuple(feat_tuple[i] for i in idxs))
        prev = mapping.get(key)
        if prev is None:
            mapping[key] = val
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
    parser.add_argument("--max-size", type=int, default=6)
    parser.add_argument("--with-boundary", action="store_true")
    parser.add_argument("--with-base-invariants", action="store_true")
    parser.add_argument("--stop-after-first", action="store_true")
    parser.add_argument("--candidates", nargs="*", default=DEFAULT_CANDIDATES)
    args = parser.parse_args()

    ds = build_compressed_dataset(
        args.family,
        args.n,
        args.candidates,
        args.with_boundary,
        args.with_base_invariants,
    )
    print(
        f"label={ds['label']} bad={ds['num_bad']} full_signatures={ds['num_signatures']} "
        f"values={ds['num_values']} full_exact={ds['full_exact']} collisions={ds['num_collisions']}"
    )
    for r in range(1, args.max_size + 1):
        found = []
        for subset in itertools.combinations(args.candidates, r):
            stats = exact_subset_stats(ds, subset)
            if stats is not None:
                found.append((subset, stats))
                if args.stop_after_first:
                    break
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
