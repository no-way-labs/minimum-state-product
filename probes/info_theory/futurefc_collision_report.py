#!/usr/bin/env python3
"""Report full-bank collisions for FutureFc."""

from __future__ import annotations

import argparse
import os
import sys
from collections import defaultdict


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
if INFO_DIR not in sys.path:
    sys.path.insert(0, INFO_DIR)

from futurefc_subset_search import build_dataset
from slice_subset_search import DEFAULT_CANDIDATES


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--limit", type=int, default=20)
    args = parser.parse_args()

    ds = build_dataset(args.family, args.n, include_boundary=True, include_base_invariants=True)
    groups = defaultdict(list)
    for idx, cfg in enumerate(ds["bad"]):
        sig = (ds["prefix"][idx], tuple(ds["bank"][name][idx] for name in DEFAULT_CANDIDATES))
        groups[sig].append((cfg, ds["ff"][cfg]))

    collisions = []
    for sig, items in groups.items():
        vals = {v for _, v in items}
        if len(vals) > 1:
            collisions.append((sig, items))

    print(ds["label"], f"collisions={len(collisions)}")
    for sig, items in collisions[: args.limit]:
        prefix, feats = sig
        print("prefix=", prefix)
        print("features=", feats)
        print("items=")
        for cfg, val in items[:10]:
            print(" ", cfg, "FutureFc", val)
        print()


if __name__ == "__main__":
    main()
