#!/usr/bin/env python3
"""Information metrics for the bad-config ranking problem.

For a valid system, convergence is equivalent to the bad-config graph being acyclic.
This produces a canonical ranking `rank(c)` on bad configurations by longest
distance to the good set. The ranking is global, but the transition tables are local.

This script measures how much information about that global bad-side rank is visible
from local observables:
- one processor's local context
- privileged multiplicity |Priv(c)|
- mover-set identity tuple

The intent is to test whether convergence might be expressible as a low-bandwidth
local code, or whether the ranking is genuinely distributed.
"""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter, defaultdict, deque
from functools import reduce
from operator import mul
from typing import Iterable


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
if CLAUDE_DIR not in sys.path:
    sys.path.insert(0, CLAUDE_DIR)

from cup2_theorem import build_system as build_cup2_system  # type: ignore
from verifier import all_configs, apply_move, privileged_set, verify_system  # type: ignore

from cycle_info_metrics import entropy, sol3_v1_rules


def product(values: Iterable[int]) -> int:
    return reduce(mul, values, 1)


def build_family(name: str, n: int) -> tuple[str, list[int], list]:
    if name == "cup2":
        ms, fs = build_cup2_system(n)
        return f"CUP-2(n={n})", ms, fs
    if name == "sol3":
        ms = [3] * n
        fs = sol3_v1_rules(ms, n)
        return f"Sol3(n={n})", ms, fs
    raise ValueError(f"unknown family {name}")


def mutual_information(xs: list, ys: list) -> float:
    joint = Counter(zip(xs, ys))
    cx = Counter(xs)
    cy = Counter(ys)
    total = len(xs)
    h_y = entropy(cy)
    cond = 0.0
    by_x: dict[object, Counter] = defaultdict(Counter)
    for x, y in zip(xs, ys):
        by_x[x][y] += 1
    for x, counter in by_x.items():
        cond += (cx[x] / total) * entropy(counter)
    return h_y - cond


def rank_bad_configs(ms: list[int], fs: list, good: set[tuple[int, ...]]) -> tuple[dict[tuple[int, ...], int], dict[int, int]]:
    cfgs = list(all_configs(ms))
    bad = [cfg for cfg in cfgs if cfg not in good]
    out_bad: dict[tuple[int, ...], list[tuple[int, ...]]] = {}
    rev_bad: dict[tuple[int, ...], list[tuple[int, ...]]] = defaultdict(list)
    outdeg_bad: dict[tuple[int, ...], int] = {}

    for cfg in bad:
        succs = []
        for proc in privileged_set(cfg, fs, ms):
            nxt = apply_move(cfg, proc, fs, ms)
            if nxt not in good:
                succs.append(nxt)
                rev_bad[nxt].append(cfg)
        out_bad[cfg] = succs
        outdeg_bad[cfg] = len(succs)

    queue = deque(cfg for cfg in bad if outdeg_bad[cfg] == 0)
    rank: dict[tuple[int, ...], int] = {cfg: 0 for cfg in queue}

    while queue:
        cfg = queue.popleft()
        for pred in rev_bad[cfg]:
            candidate = rank[cfg] + 1
            prev = rank.get(pred, -1)
            if candidate > prev:
                rank[pred] = candidate
            outdeg_bad[pred] -= 1
            if outdeg_bad[pred] == 0:
                queue.append(pred)

    if len(rank) != len(bad):
        raise ValueError("bad graph is not a DAG or ranking failed")

    dist = Counter(rank.values())
    return rank, dict(sorted(dist.items()))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3", "all"], default="all")
    parser.add_argument("--n", type=int, default=9)
    args = parser.parse_args()

    families = ["cup2", "sol3"] if args.family == "all" else [args.family]
    outputs: list[str] = []

    for family in families:
        label, ms, fs = build_family(family, args.n)
        result = verify_system(ms, fs)
        if not result.get("valid"):
            raise ValueError(f"{label} is not valid")
        good = set(result["good_configs"])
        rank, dist = rank_bad_configs(ms, fs, good)
        bad_cfgs = sorted(rank)
        ranks = [rank[cfg] for cfg in bad_cfgs]
        h_rank = entropy(Counter(ranks))
        n = len(ms)

        lines: list[str] = []
        lines.append(label)
        lines.append(f"  n={n}, product={product(ms)}, bad_configs={len(bad_cfgs)}")
        lines.append(f"  good_set={len(good)}, max_rank={max(ranks, default=0)}, H(rank)={h_rank:.4f} bits")
        lines.append("")
        lines.append("  rank distribution:")
        for value, count in dist.items():
            lines.append(f"  - rank {value}: {count}")
        lines.append("")
        lines.append("  proc  m_i  I(C_i; rank)")
        lines.append("  ----  ---  ------------")
        for proc in range(n):
            contexts = [
                (cfg[(proc - 1) % n], cfg[proc], cfg[(proc + 1) % n])
                for cfg in bad_cfgs
            ]
            info = mutual_information(contexts, ranks)
            lines.append(f"  {proc:>4}  {ms[proc]:>3}      {info:>8.4f}")

        priv_mult = [len(privileged_set(cfg, fs, ms)) for cfg in bad_cfgs]
        priv_sets = [tuple(privileged_set(cfg, fs, ms)) for cfg in bad_cfgs]
        lines.append("")
        lines.append(f"  I(|Priv(c)|; rank) = {mutual_information(priv_mult, ranks):.4f} bits")
        lines.append(f"  I(Priv(c); rank) = {mutual_information(priv_sets, ranks):.4f} bits")

        outputs.append("\n".join(lines))

    print("\n\n".join(outputs))


if __name__ == "__main__":
    main()
