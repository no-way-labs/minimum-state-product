#!/usr/bin/env python3
"""Boundary explanation probe for constant-FutureFc slice rank.

Measures how much the slice rank is determined by the boundary 6-tuple and
related coarse boundary-local summaries.
"""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter, defaultdict
from math import log2


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
if CLAUDE_DIR not in sys.path:
    sys.path.insert(0, CLAUDE_DIR)

from cup2_theorem import build_system as build_cup2_system  # type: ignore
from verifier import all_configs, verify_system  # type: ignore

from cycle_info_metrics import entropy, sol3_v1_rules
from twolevel_spectrum import constant_ff_rank, future_fc


def build_family(name: str, n: int):
    if name == "cup2":
        ms, fs = build_cup2_system(n)
        return f"CUP-2(n={n})", ms, fs
    if name == "sol3":
        ms = [3] * n
        fs = sol3_v1_rules(ms, n)
        return f"Sol3(n={n})", ms, fs
    raise ValueError(f"unknown family {name}")


def mutual_information(xs, ys):
    total = len(xs)
    cx = Counter(xs)
    cy = Counter(ys)
    by_x = defaultdict(Counter)
    for x, y in zip(xs, ys):
        by_x[x][y] += 1
    h_y = entropy(cy)
    cond = 0.0
    for x, cnt in by_x.items():
        cond += (cx[x] / total) * entropy(cnt)
    return h_y - cond


def boundary6(cfg):
    n = len(cfg)
    return (cfg[0], cfg[1], cfg[2], cfg[n - 3], cfg[n - 2], cfg[n - 1])


def interior_counts(cfg):
    n = len(cfg)
    c20 = sum(1 for j in range(2, n - 2) if cfg[j] == 2 and cfg[(j + 1) % n] == 0)
    c21 = sum(1 for j in range(2, n - 2) if cfg[j] == 2 and cfg[(j + 1) % n] == 1)
    return (c20, c21)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, default=9)
    args = parser.parse_args()

    label, ms, fs = build_family(args.family, args.n)
    result = verify_system(ms, fs)
    good = set(result["good_configs"])
    bad, bad_set, adj, ff = future_fc(ms, fs, good)
    cfr = constant_ff_rank(bad, adj, ff)

    vals = [cfr[cfg] for cfg in bad]
    b6 = [boundary6(cfg) for cfg in bad]
    b6_ff = [(ff[cfg], boundary6(cfg)) for cfg in bad]
    b6_ff_ic = [(ff[cfg], boundary6(cfg), interior_counts(cfg)) for cfg in bad]

    def support_stats(keys):
        groups = defaultdict(set)
        for k, v in zip(keys, vals):
            groups[k].add(v)
        return len(groups), sum(len(s) == 1 for s in groups.values()), max(len(s) for s in groups.values())

    print(label)
    print(f"  H(cf_rank) = {entropy(Counter(vals)):.6f} bits")
    print(f"  I(boundary6; cf_rank) = {mutual_information(b6, vals):.6f}")
    print(f"  I((FutureFc,boundary6); cf_rank) = {mutual_information(b6_ff, vals):.6f}")
    print(f"  I((FutureFc,boundary6,intCounts); cf_rank) = {mutual_information(b6_ff_ic, vals):.6f}")
    for name, keys in [
        ("boundary6", b6),
        ("(FutureFc,boundary6)", b6_ff),
        ("(FutureFc,boundary6,intCounts)", b6_ff_ic),
    ]:
        ng, single, maxsupp = support_stats(keys)
        print(f"  {name}: groups={ng}, singleton_groups={single}, max_rank_support={maxsupp}")


if __name__ == "__main__":
    main()
