#!/usr/bin/env python3
"""Probe exact decision-tree decoders for constant-FutureFc slice rank."""

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

from slice_feature_search import build_family, boundary6, base_invariants, make_feature_bank
from twolevel_spectrum import future_fc, constant_ff_rank
from verifier import verify_system  # type: ignore


def build_groups(family, n, features):
    label, ms, fs = build_family(family, n)
    result = verify_system(ms, fs)
    good = set(result["good_configs"])
    bad, _, adj, ff = future_fc(ms, fs, good)
    cfr = constant_ff_rank(bad, adj, ff)
    bank = make_feature_bank(bad)
    groups = defaultdict(dict)
    for idx, cfg in enumerate(bad):
        prefix = (ff[cfg], boundary6(cfg), base_invariants(cfg))
        feat = tuple(bank[name][idx] for name in features)
        val = cfr[cfg]
        prev = groups[prefix].get(feat)
        if prev is not None and prev != val:
            raise ValueError("feature tuple not exact in prefix")
        groups[prefix][feat] = val
    return label, groups


def min_tree_depth(items):
    items = tuple(sorted(items))
    if len({label for _, label in items}) <= 1:
        return 0
    dim = len(items[0][0])

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
            if len(buckets) == 1:
                continue
            depth = 1 + max(solve(tuple(sorted(bucket))) for bucket in buckets.values())
            if best is None or depth < best:
                best = depth
        return best if best is not None else float("inf")

    return solve(items)


def summarize(label, features, groups):
    sizes = Counter()
    depths = []
    for mp in groups.values():
        if len(mp) <= 1:
            sizes[0] += 1
            depths.append(0)
            continue
        d = min_tree_depth(tuple(sorted(mp.items())))
        sizes[d] += 1
        depths.append(d)
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

    label, groups = build_groups(args.family, args.n, args.features)
    summarize(label, args.features, groups)


if __name__ == "__main__":
    main()
