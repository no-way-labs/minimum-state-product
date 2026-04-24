#!/usr/bin/env python3
"""ANOVA spectra for the two-level convergence decomposition.

For a valid system, define on bad configs:

- fc(c): frontier count
- FutureFc(c): max fc reachable from c through bad steps
- cf_rank(c): DAG rank inside the constant-FutureFc slice

This script extends these scalars to the full configuration space and measures
their width-(n-2) forbidden interaction energy.
"""

from __future__ import annotations

import argparse
import os
import sys
from collections import defaultdict, deque

import numpy as np


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
if CLAUDE_DIR not in sys.path:
    sys.path.insert(0, CLAUDE_DIR)

from cup2_theorem import build_system as build_cup2_system  # type: ignore
from verifier import all_configs, apply_move, privileged_set, verify_system  # type: ignore

from anova_interaction_spectrum import anova_spectrum
from cycle_info_metrics import sol3_v1_rules
from rank_info_metrics import rank_bad_configs


def build_family(name: str, n: int):
    if name == "cup2":
        ms, fs = build_cup2_system(n)
        return f"CUP-2(n={n})", ms, fs
    if name == "sol3":
        ms = [3] * n
        fs = sol3_v1_rules(ms, n)
        return f"Sol3(n={n})", ms, fs
    raise ValueError(f"unknown family {name}")


def fc(cfg):
    n = len(cfg)
    return sum(1 for i in range(n) if cfg[i] != cfg[(i + 1) % n])


def build_bad_graph(ms, fs, good):
    bad = [cfg for cfg in all_configs(ms) if cfg not in good]
    bad_set = set(bad)
    adj = defaultdict(list)
    radj = defaultdict(list)
    for cfg in bad:
        for proc in privileged_set(cfg, fs, ms):
            nxt = apply_move(cfg, proc, fs, ms)
            if nxt in bad_set:
                adj[cfg].append(nxt)
                radj[nxt].append(cfg)
    return bad, bad_set, adj, radj


def topo_rank(adj, nodes):
    outdeg = {cfg: len(adj.get(cfg, [])) for cfg in nodes}
    sinks = [cfg for cfg in nodes if outdeg[cfg] == 0]
    rank = {cfg: 0 for cfg in sinks}
    radj = defaultdict(list)
    for cfg in nodes:
        for nxt in adj.get(cfg, []):
            radj[nxt].append(cfg)
    queue = deque(sinks)
    while queue:
        cfg = queue.popleft()
        for pred in radj[cfg]:
            cand = rank[cfg] + 1
            if cand > rank.get(pred, -1):
                rank[pred] = cand
            outdeg[pred] -= 1
            if outdeg[pred] == 0:
                queue.append(pred)
    return rank


def future_fc(ms, fs, good):
    bad, bad_set, adj, radj = build_bad_graph(ms, fs, good)
    rank = topo_rank(adj, bad)
    by_rank = defaultdict(list)
    for cfg, r in rank.items():
        by_rank[r].append(cfg)
    ff = {cfg: fc(cfg) for cfg in bad}
    for r in range(0, max(by_rank) + 1):
        for cfg in by_rank[r]:
            for nxt in adj.get(cfg, []):
                if ff[nxt] > ff[cfg]:
                    ff[cfg] = ff[nxt]
    return bad, bad_set, adj, ff


def constant_ff_rank(bad, adj, ff):
    by_ff = defaultdict(list)
    for cfg in bad:
        by_ff[ff[cfg]].append(cfg)
    cfr = {}
    for val, nodes in by_ff.items():
        node_set = set(nodes)
        sub_adj = defaultdict(list)
        for cfg in nodes:
            for nxt in adj.get(cfg, []):
                if nxt in node_set and ff[nxt] == val:
                    sub_adj[cfg].append(nxt)
        sub_rank = topo_rank(sub_adj, nodes)
        cfr.update(sub_rank)
    return cfr


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, default=9)
    parser.add_argument("--width", type=int, default=None)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    label, ms, fs = build_family(args.family, args.n)
    result = verify_system(ms, fs)
    good = set(result["good_configs"])
    width = args.width if args.width is not None else args.n - 2
    bad, bad_set, adj, ff = future_fc(ms, fs, good)
    cfr = constant_ff_rank(bad, adj, ff)

    cfgs = list(all_configs(ms))
    values = {
        "FutureFc": np.array([0.0 if cfg in good else float(ff[cfg]) for cfg in cfgs]),
        "cf_rank": np.array([0.0 if cfg in good else float(cfr[cfg] + 1) for cfg in cfgs]),
        "fc": np.array([0.0 if cfg in good else float(fc(cfg)) for cfg in cfgs]),
    }
    rng = np.random.default_rng(args.seed)
    print(label, f"width={width}")
    for name, vals in values.items():
        shuffled = rng.permutation(vals)
        aa, af, _, _ = anova_spectrum(ms, vals, width)
        sa, sf, _, _ = anova_spectrum(ms, shuffled, width)
        print(
            f"  {name}: actual_forbid={af/(aa+af):.6f}, "
            f"shuffled_forbid={sf/(sa+sf):.6f}"
        )


if __name__ == "__main__":
    main()
