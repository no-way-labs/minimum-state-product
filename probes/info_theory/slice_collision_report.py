#!/usr/bin/env python3
"""Report full-bank collisions for the residual slice code."""

from __future__ import annotations

import argparse
import os
import sys
from collections import defaultdict


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
if INFO_DIR not in sys.path:
    sys.path.insert(0, INFO_DIR)

from slice_feature_search import build_family, boundary6, base_invariants, make_feature_bank
from twolevel_spectrum import future_fc, constant_ff_rank
from verifier import verify_system  # type: ignore
from slice_subset_search import DEFAULT_CANDIDATES


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--limit", type=int, default=20)
    args = parser.parse_args()

    label, ms, fs = build_family(args.family, args.n)
    result = verify_system(ms, fs)
    good = set(result["good_configs"])
    bad, _, adj, ff = future_fc(ms, fs, good)
    cfr = constant_ff_rank(bad, adj, ff)
    bank = make_feature_bank(bad)

    groups = defaultdict(list)
    for idx, cfg in enumerate(bad):
        base = (ff[cfg], boundary6(cfg), base_invariants(cfg))
        feat_tuple = tuple(bank[name][idx] for name in DEFAULT_CANDIDATES)
        sig = (base, feat_tuple)
        groups[sig].append((cfg, cfr[cfg]))

    collisions = []
    for sig, items in groups.items():
        ranks = {r for _, r in items}
        if len(ranks) > 1:
            collisions.append((sig, items))

    print(label, f"collisions={len(collisions)}")
    for sig, items in collisions[: args.limit]:
        base, feat_tuple = sig
        print("base=", base)
        print("features=", feat_tuple)
        print("items=")
        for cfg, rank in items[:10]:
            print(" ", cfg, "rank", rank)
        print()


if __name__ == "__main__":
    main()
