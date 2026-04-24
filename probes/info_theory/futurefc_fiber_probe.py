#!/usr/bin/env python3
"""Probe derived quantities on exact FutureFc feature fibers."""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter, defaultdict


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
if INFO_DIR not in sys.path:
    sys.path.insert(0, INFO_DIR)

from futurefc_subset_search import build_dataset
from slice_feature_search import base_invariants, boundary6, build_family, make_feature_bank
from twolevel_spectrum import future_fc
from verifier import verify_system  # type: ignore


def fc(cfg):
    n = len(cfg)
    return sum(1 for j in range(n) if cfg[j] != cfg[(j + 1) % n])


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


DERIVED_NAMES = {"FutureFc", "fc", "gap", "exp2", "int21", "exp2_weight", "count_val_2"}
PREFIX_PARTS = {"boundary6", "exp2", "int21", "exp2_weight"}


def build_dataset_custom_prefix(family: str, n: int, prefix_parts: list[str]):
    label, ms, fs = build_family(family, n)
    result = verify_system(ms, fs)
    good = set(result["good_configs"])
    bad, _, _, ff = future_fc(ms, fs, good)
    bank = make_feature_bank(bad)
    prefix = []
    for cfg in bad:
        tp = base_invariants(cfg)
        parts = []
        for name in prefix_parts:
            if name == "boundary6":
                parts.append(boundary6(cfg))
            elif name == "exp2":
                parts.append(tp[0])
            elif name == "int21":
                parts.append(tp[1])
            elif name == "exp2_weight":
                parts.append(tp[2])
            else:
                raise ValueError(name)
        prefix.append(tuple(parts))
    return {
        "label": label,
        "bad": bad,
        "ff": ff,
        "bank": bank,
        "prefix": prefix,
    }


def probe(ds, features, target_name):
    needed = [name for name in features if name not in ds["bank"]]
    if needed:
        for name in needed:
            ds["bank"][name] = []
        for cfg in ds["bad"]:
            vals = lag_11_features(cfg)
            for name in needed:
                ds["bank"][name].append(vals[name])

    mapping = {}
    collisions = 0
    for idx, cfg in enumerate(ds["bad"]):
        key = (ds["prefix"][idx], tuple(ds["bank"][name][idx] for name in features))
        if target_name == "FutureFc":
            value = ds["ff"][cfg]
        elif target_name == "fc":
            value = fc(cfg)
        elif target_name == "gap":
            value = ds["ff"][cfg] - fc(cfg)
        elif target_name == "exp2":
            value = base_invariants(cfg)[0]
        elif target_name == "int21":
            value = base_invariants(cfg)[1]
        elif target_name == "exp2_weight":
            value = base_invariants(cfg)[2]
        elif target_name == "count_val_2":
            value = sum(1 for j in range(2, len(cfg) - 2) if cfg[j] == 2)
        else:
            raise ValueError(target_name)
        prev = mapping.get(key)
        if prev is None:
            mapping[key] = value
        elif prev != value:
            collisions += 1
    values = Counter(mapping.values())
    return {
        "exact": collisions == 0,
        "collisions": collisions,
        "fiber_count": len(mapping),
        "value_count": len(values),
        "value_hist": dict(sorted(values.items())),
    }


def summarize_groups(ds, features, limit):
    groups = defaultdict(list)
    for idx, cfg in enumerate(ds["bad"]):
        key = ds["prefix"][idx]
        feat = tuple(ds["bank"][name][idx] for name in features)
        groups[key].append((cfg, feat, ds["ff"][cfg], fc(cfg)))
    nontrivial = [(prefix, rows) for prefix, rows in groups.items() if len(rows) > 1]
    print(f"nontrivial prefix groups: {len(nontrivial)}")
    for i, (prefix, rows) in enumerate(nontrivial[:limit], start=1):
        ff_values = sorted({row[2] for row in rows})
        gap_values = sorted({row[2] - row[3] for row in rows})
        print(f"group {i}: prefix={prefix} size={len(rows)} ff_values={ff_values} gap_values={gap_values}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--features", nargs="+", required=True)
    parser.add_argument("--no-boundary", action="store_true")
    parser.add_argument("--no-base-invariants", action="store_true")
    parser.add_argument(
        "--prefix-parts",
        nargs="*",
        choices=sorted(PREFIX_PARTS),
        help="override the default prefix selection with explicit components",
    )
    parser.add_argument(
        "--target",
        choices=sorted(DERIVED_NAMES),
        default="FutureFc",
        help="derived quantity to test on fibers",
    )
    parser.add_argument("--show-groups", type=int, default=0)
    args = parser.parse_args()

    if args.prefix_parts is not None:
        ds = build_dataset_custom_prefix(args.family, args.n, args.prefix_parts)
        prefix_desc = args.prefix_parts
    else:
        ds = build_dataset(
            args.family,
            args.n,
            include_boundary=not args.no_boundary,
            include_base_invariants=not args.no_base_invariants,
        )
        prefix_desc = []
        if not args.no_boundary:
            prefix_desc.append("boundary6")
        if not args.no_base_invariants:
            prefix_desc.extend(["exp2", "int21", "exp2_weight"])
    stats = probe(ds, args.features, args.target)
    print(ds["label"])
    print("features:", args.features)
    print("prefix_parts:", prefix_desc)
    print("target:", args.target)
    print("exact:", stats["exact"])
    print("collisions:", stats["collisions"])
    print("fiber_count:", stats["fiber_count"])
    print("value_count:", stats["value_count"])
    print("value_hist:", stats["value_hist"])
    if args.show_groups > 0:
        summarize_groups(ds, args.features, args.show_groups)


if __name__ == "__main__":
    main()
