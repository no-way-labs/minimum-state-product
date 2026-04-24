#!/usr/bin/env python3
"""Exact tree probes for custom FutureFc-related targets on custom prefixes."""

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

from futurefc_fiber_probe import build_dataset_custom_prefix, fc, lag_11_features
from slice_feature_search import base_invariants


TARGETS = {"FutureFc", "fc", "gap", "exp2", "int21", "exp2_weight", "count_val_2"}


def target_value(ds, cfg, target):
    if target == "FutureFc":
        return ds["ff"][cfg]
    if target == "fc":
        return fc(cfg)
    if target == "gap":
        return ds["ff"][cfg] - fc(cfg)
    tp = base_invariants(cfg)
    if target == "exp2":
        return tp[0]
    if target == "int21":
        return tp[1]
    if target == "exp2_weight":
        return tp[2]
    if target == "count_val_2":
        return sum(1 for j in range(2, len(cfg) - 2) if cfg[j] == 2)
    raise ValueError(target)


def ensure_features(ds, feature_names):
    needed = [name for name in feature_names if name not in ds["bank"]]
    if not needed:
        return
    for name in needed:
        ds["bank"][name] = []
    for cfg in ds["bad"]:
        vals = lag_11_features(cfg)
        for name in needed:
            ds["bank"][name].append(vals[name])


def build_groups(ds, features, target):
    ensure_features(ds, features)
    groups = defaultdict(dict)
    for idx, cfg in enumerate(ds["bad"]):
        prefix = ds["prefix"][idx]
        feat = tuple(ds["bank"][name][idx] for name in features)
        val = target_value(ds, cfg, target)
        prev = groups[prefix].get(feat)
        if prev is not None and prev != val:
            raise ValueError("feature tuple is not exact in prefix")
        groups[prefix][feat] = val
    return groups


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


def summarize(label, target, features, groups, show_groups, root_counts_enabled):
    sizes = Counter()
    depths = []
    nontrivial = []
    root_counts = Counter()
    for prefix, mp in groups.items():
        if len(mp) <= 1:
            sizes[0] += 1
            depths.append(0)
            continue
        items = tuple(sorted(mp.items()))
        d = min_tree_depth(items)
        sizes[d] += 1
        depths.append(d)
        if root_counts_enabled:
            _, tree = solve_tree(items)
            if tree[0] == "split":
                root_counts[features[tree[1]]] += 1
        nontrivial.append((prefix, mp, d))
    print(label)
    print("target:", target)
    print("features:", features)
    print("prefix groups:", len(groups))
    print("depth distribution:", dict(sorted(sizes.items())))
    print("max depth:", max(depths) if depths else 0)
    print("avg depth:", sum(depths) / len(depths) if depths else 0.0)
    if root_counts_enabled:
        print("root split counts:", dict(root_counts.most_common()))
    if show_groups > 0:
        for i, (prefix, mp, d) in enumerate(nontrivial[:show_groups], start=1):
            _, tree = solve_tree(tuple(sorted(mp.items())))
            print(f"\nGroup {i}: prefix={prefix} size={len(mp)} depth={d}")
            print(pretty(tree, features))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--prefix-parts", nargs="*", default=["boundary6"])
    parser.add_argument("--features", nargs="+", required=True)
    parser.add_argument("--target", choices=sorted(TARGETS), required=True)
    parser.add_argument("--show-groups", type=int, default=0)
    parser.add_argument("--root-counts", action="store_true")
    args = parser.parse_args()

    ds = build_dataset_custom_prefix(args.family, args.n, args.prefix_parts)
    groups = build_groups(ds, args.features, args.target)
    summarize(ds["label"], args.target, args.features, groups, args.show_groups, args.root_counts)


if __name__ == "__main__":
    main()
