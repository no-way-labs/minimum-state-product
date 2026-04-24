#!/usr/bin/env python3
"""Extract one exact multiway decision tree for FutureFc on a solved basis."""

from __future__ import annotations

import argparse
import functools
import os
import sys
from collections import defaultdict


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
if INFO_DIR not in sys.path:
    sys.path.insert(0, INFO_DIR)

from futurefc_subset_search import build_dataset


def build_groups(ds, features):
    groups = defaultdict(dict)
    for idx, cfg in enumerate(ds["bad"]):
        prefix = ds["prefix"][idx]
        feat = tuple(ds["bank"][name][idx] for name in features)
        val = ds["ff"][cfg]
        prev = groups[prefix].get(feat)
        if prev is not None and prev != val:
            raise ValueError("basis is not exact in prefix")
        groups[prefix][feat] = val
    return groups


def solve_tree(items):
    items = tuple(sorted(items))
    dim = len(items[0][0])

    @functools.lru_cache(maxsize=None)
    def rec(state):
        labels = {label for _, label in state}
        if len(labels) <= 1:
            return (0, ("leaf", next(iter(labels))))

        best = None
        best_tree = None
        for j in range(dim):
            buckets = defaultdict(list)
            for feat, label in state:
                buckets[feat[j]].append((feat, label))
            if len(buckets) == 1:
                continue
            child_results = {}
            child_depths = []
            for val, bucket in sorted(buckets.items()):
                d, tree = rec(tuple(sorted(bucket)))
                child_results[val] = tree
                child_depths.append(d)
            depth = 1 + max(child_depths)
            if best is None or depth < best:
                best = depth
                best_tree = ("split", j, child_results)
        if best is None:
            return (float("inf"), ("fail",))
        return (best, best_tree)

    return rec(items)


def pretty(tree, feature_names, indent=0):
    pad = "  " * indent
    tag = tree[0]
    if tag == "leaf":
        return f"{pad}return {tree[1]}"
    if tag == "split":
        _, idx, children = tree
        lines = [f"{pad}split on {feature_names[idx]}:"]
        for val, child in children.items():
            lines.append(f"{pad}  case {val}:")
            lines.append(pretty(child, feature_names, indent + 2))
        return "\n".join(lines)
    return f"{pad}{tree}"


def summarize_case(label, features, groups, limit=3):
    nontrivial = []
    for prefix, mp in groups.items():
        if len(mp) > 1:
            nontrivial.append((prefix, mp))
    print(label)
    print("features:", features)
    print("nontrivial prefix groups:", len(nontrivial))
    for idx, (prefix, mp) in enumerate(nontrivial[:limit], start=1):
        depth, tree = solve_tree(tuple(sorted(mp.items())))
        print(f"\nGroup {idx}: prefix={prefix} size={len(mp)} depth={depth}")
        print(pretty(tree, features))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--features", nargs="+", required=True)
    parser.add_argument("--limit", type=int, default=3)
    args = parser.parse_args()

    ds = build_dataset(args.family, args.n, include_boundary=True, include_base_invariants=True)
    groups = build_groups(ds, args.features)
    summarize_case(ds["label"], args.features, groups, limit=args.limit)


if __name__ == "__main__":
    main()
