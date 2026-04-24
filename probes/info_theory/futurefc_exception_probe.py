#!/usr/bin/env python3
"""Analyze exceptional reduced-prefix groups after a primary split feature."""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter, defaultdict


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
if INFO_DIR not in sys.path:
    sys.path.insert(0, INFO_DIR)

from futurefc_target_tree_probe import build_dataset_custom_prefix, build_groups


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--target", required=True)
    parser.add_argument("--prefix-parts", nargs="*", default=["boundary6"])
    parser.add_argument("--features", nargs="+", required=True)
    parser.add_argument("--primary", required=True)
    parser.add_argument("--secondary", nargs="*", default=None)
    parser.add_argument("--limit", type=int, default=12)
    args = parser.parse_args()

    if args.primary not in args.features:
        raise ValueError("primary feature must be among --features")
    secondary = args.secondary or [f for f in args.features if f != args.primary]
    for name in secondary:
        if name not in args.features:
            raise ValueError(f"secondary feature {name} not in features")

    ds = build_dataset_custom_prefix(args.family, args.n, args.prefix_parts)
    groups = build_groups(ds, args.features, args.target)
    idx = {name: i for i, name in enumerate(args.features)}
    pidx = idx[args.primary]

    counts = Counter()
    patterns = Counter()
    examples = defaultdict(list)
    for prefix, mp in groups.items():
        if len(mp) <= 1 or len(set(mp.values())) == 1:
            continue
        by_primary = defaultdict(list)
        for feat, label in mp.items():
            by_primary[feat[pidx]].append((feat, label))
        if all(len({label for _, label in items}) == 1 for items in by_primary.values()):
            continue

        counts["exception_groups"] += 1
        good = []
        for name in secondary:
            sidx = idx[name]
            ok = True
            for _, items in by_primary.items():
                buckets = {}
                for feat, label in items:
                    key = feat[sidx]
                    prev = buckets.get(key)
                    if prev is None:
                        buckets[key] = label
                    elif prev != label:
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                good.append(name)

        counts[tuple(good)] += 1
        norm = tuple(
            sorted(
                (val, tuple(sorted({label for _, label in items})))
                for val, items in by_primary.items()
                if len({label for _, label in items}) > 1
            )
        )
        patterns[(norm, tuple(good))] += 1
        if len(examples[(norm, tuple(good))]) < 3:
            examples[(norm, tuple(good))].append(prefix)

    print(f"{args.family}(n={args.n}) target={args.target}")
    print("primary:", args.primary)
    print("secondary:", secondary)
    print("exception_groups:", counts["exception_groups"])
    for key, value in counts.items():
        if key == "exception_groups":
            continue
        print("  resolvers", key, ":", value)
    print("pattern_count:", len(patterns))
    for i, ((norm, good), cnt) in enumerate(patterns.most_common(args.limit), start=1):
        print(f"\nPATTERN {i}: count={cnt} resolvers={good} examples={examples[(norm, good)]}")
        print(norm)


if __name__ == "__main__":
    main()
