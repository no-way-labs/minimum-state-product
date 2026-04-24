#!/usr/bin/env python3
"""Probe exact decision-tree decoders for FutureFc on solved tiny bases."""

from __future__ import annotations

import argparse
import functools
import os
import sys
from collections import Counter, defaultdict


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


def build_groups(ds, features):
    needed = [name for name in features if name not in ds["bank"]]
    if needed:
        for name in needed:
            ds["bank"][name] = []
        for cfg in ds["bad"]:
            vals = lag_11_features(cfg)
            for name in needed:
                ds["bank"][name].append(vals[name])
    groups = defaultdict(dict)
    for idx, cfg in enumerate(ds["bad"]):
        prefix = ds["prefix"][idx]
        feat = tuple(ds["bank"][name][idx] for name in features)
        val = ds["ff"][cfg]
        prev = groups[prefix].get(feat)
        if prev is not None and prev != val:
            raise ValueError("feature tuple is not exact within prefix")
        groups[prefix][feat] = val
    return groups


def min_tree_depth(items):
    """Exact minimal depth of a multiway axis-aligned decision tree."""
    feats = tuple(sorted(items))
    labels = {label for _, label in feats}
    if len(labels) <= 1:
        return 0
    dim = len(feats[0][0])

    @functools.lru_cache(maxsize=None)
    def solve(state):
        labels = {label for _, label in state}
        if len(labels) <= 1:
            return 0
        best = None
        for j in range(dim):
            buckets = defaultdict(list)
            for feat, label in state:
                buckets[feat[j]].append((feat, label))
            # useless split
            if len(buckets) == 1:
                continue
            depth = 1 + max(solve(tuple(sorted(bucket))) for bucket in buckets.values())
            if best is None or depth < best:
                best = depth
        return best if best is not None else float("inf")

    return solve(feats)


def summarize(label, features, groups):
    depths = []
    sizes = Counter()
    for mp in groups.values():
        if len(mp) <= 1:
            depths.append(0)
            sizes[0] += 1
            continue
        items = tuple(sorted(mp.items()))
        d = min_tree_depth(items)
        depths.append(d)
        sizes[d] += 1
    print(label)
    print("features:", features)
    print("prefix groups:", len(groups))
    print("depth distribution:", dict(sorted(sizes.items())))
    print("max depth:", max(depths) if depths else 0)
    print("avg depth:", sum(depths) / len(depths) if depths else 0.0)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--features", nargs="+", required=True)
    args = parser.parse_args()

    ds = build_dataset(args.family, args.n, include_boundary=True, include_base_invariants=True)
    groups = build_groups(ds, args.features)
    summarize(ds["label"], args.features, groups)


if __name__ == "__main__":
    main()
