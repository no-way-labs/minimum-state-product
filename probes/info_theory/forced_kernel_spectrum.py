#!/usr/bin/env python3
"""Interaction spectra for invalid sub-threshold forced-kernel scalars.

For small residual families with a candidate good cycle C, the forced mover-entry
graph F_C may have a nonempty kernel after iterative sink removal. That kernel is
the obstruction used in the finite lemmas.

This script builds two canonical scalars on the full configuration space:

- kernel_indicator(c) = 1 if c is in the forced kernel, else 0
- peel_depth(c):
    0 on good configs,
    r on nodes removed in sink-removal round r,
    R+1 on kernel nodes

Then it computes width-(n-2) forbidden interaction energy fractions and compares
against shuffled null models.
"""

from __future__ import annotations

import argparse
import os
import sys
import time
from itertools import product as iproduct

import numpy as np


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
if CLAUDE_DIR not in sys.path:
    sys.path.insert(0, CLAUDE_DIR)

from verifier import all_configs  # type: ignore

from anova_interaction_spectrum import anova_spectrum


def enumerate_good_cycles(ms, n, max_cycles=200, max_time=60.0):
    t0 = time.time()
    product_val = 1
    for m in ms:
        product_val *= m
    if product_val > 1000:
        return []

    all_cfgs = list(iproduct(*[range(m) for m in ms]))
    cycles = []
    for start_idx in range(min(len(all_cfgs), product_val)):
        if time.time() - t0 > max_time:
            break
        start = all_cfgs[start_idx]
        stack = [(start, [start], {}, [])]
        nodes = 0
        while stack and nodes < 500000:
            if time.time() - t0 > max_time:
                break
            nodes += 1
            config, path, det, movers = stack.pop()
            path_set = set(path)
            for p in range(n):
                for new_val in range(ms[p]):
                    if new_val == config[p]:
                        continue
                    if movers:
                        last = movers[-1]
                        diff = min(abs(p - last), n - abs(p - last))
                        if diff > 1:
                            continue
                    new_det = dict(det)
                    consistent = True
                    L = config[(p - 1) % n]
                    S = config[p]
                    R = config[(p + 1) % n]
                    key_m = (p, L, S, R)
                    if key_m in new_det:
                        if new_det[key_m] != new_val:
                            consistent = False
                    else:
                        new_det[key_m] = new_val
                    if consistent:
                        for i in range(n):
                            if i == p:
                                continue
                            Li = config[(i - 1) % n]
                            Si = config[i]
                            Ri = config[(i + 1) % n]
                            key_i = (i, Li, Si, Ri)
                            if key_i in new_det:
                                if new_det[key_i] != Si:
                                    consistent = False
                                    break
                            else:
                                new_det[key_i] = Si
                    if not consistent:
                        continue
                    new_config = list(config)
                    new_config[p] = new_val
                    new_config = tuple(new_config)
                    if new_config == start and len(path) >= n:
                        me_ok = True
                        for c in path:
                            priv = []
                            for i in range(n):
                                Li = c[(i - 1) % n]
                                Si = c[i]
                                Ri = c[(i + 1) % n]
                                ki = (i, Li, Si, Ri)
                                if ki in new_det and new_det[ki] != Si:
                                    priv.append(i)
                            if len(priv) != 1:
                                me_ok = False
                                break
                        if me_ok:
                            cycle_tup = tuple(path)
                            if cycle_tup not in [tuple(c) for c, _, _ in cycles]:
                                cycles.append((path, movers + [p], new_det))
                                if len(cycles) >= max_cycles:
                                    return cycles
                        continue
                    if new_config not in path_set and len(path) < 10 * n:
                        stack.append((new_config, path + [new_config], new_det, movers + [p]))
    return cycles


def build_forced_graph(ms, n, det, good_set):
    non_good = [c for c in iproduct(*[range(m) for m in ms]) if c not in good_set]
    non_good_set = set(non_good)
    adj = {}
    for c in non_good:
        out = []
        for p in range(n):
            Lp = c[(p - 1) % n]
            Sp = c[p]
            Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                nc = list(c)
                nc[p] = det[key]
                nc = tuple(nc)
                if nc in non_good_set:
                    out.append((nc, p))
        adj[c] = out
    return non_good, non_good_set, adj


def iterative_peel(non_good, adj):
    remaining = set(non_good)
    removed_round = {}
    round_num = 0
    while True:
        sinks = set()
        for cfg in remaining:
            has_out = False
            for target, _ in adj.get(cfg, []):
                if target in remaining:
                    has_out = True
                    break
            if not has_out:
                sinks.add(cfg)
        if not sinks:
            break
        round_num += 1
        for cfg in sinks:
            removed_round[cfg] = round_num
        remaining -= sinks
    kernel = remaining
    return removed_round, kernel, round_num


def analyze_cycle(ms, cycle, det, seed=0):
    n = len(ms)
    good = set(cycle)
    non_good, _, adj = build_forced_graph(ms, n, det, good)
    removed_round, kernel, rounds = iterative_peel(non_good, adj)
    cfgs = list(all_configs(ms))

    kernel_indicator = np.array(
        [1.0 if cfg in kernel else 0.0 for cfg in cfgs],
        dtype=np.float64,
    )
    peel_depth = np.array(
        [
            0.0 if cfg in good else
            float(removed_round[cfg]) if cfg in removed_round else
            float(rounds + 1)
            for cfg in cfgs
        ],
        dtype=np.float64,
    )

    rng = np.random.default_rng(seed)
    result = {}
    for name, vals in [("kernel_indicator", kernel_indicator), ("peel_depth", peel_depth)]:
        shuffled = rng.permutation(vals)
        aa, af, _, _ = anova_spectrum(ms, vals, n - 2)
        sa, sf, _, _ = anova_spectrum(ms, shuffled, n - 2)
        result[name] = {
            "actual_forbidden_frac": af / (aa + af) if aa + af else 0.0,
            "shuffled_forbidden_frac": sf / (sa + sf) if sa + sf else 0.0,
            "kernel_size": len(kernel),
            "rounds": rounds,
        }
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, choices=[5, 6], required=True)
    parser.add_argument("--max-cycles", type=int, default=10)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    if args.n == 5:
        ms = (2, 2, 2, 3, 3)
    else:
        ms = (2, 2, 2, 3, 3, 3)

    cycles = enumerate_good_cycles(ms, args.n, max_cycles=args.max_cycles, max_time=120.0)
    full = [(cycle, movers, det) for cycle, movers, det in cycles if set(movers) == set(range(args.n))]
    print(f"n={args.n}, ms={ms}, full_cycles={len(full)}")
    for idx, (cycle, movers, det) in enumerate(full[: args.max_cycles]):
        stats = analyze_cycle(ms, cycle, det, seed=args.seed + idx)
        print(f"cycle {idx}: len={len(cycle)}")
        for name, data in stats.items():
            print(
                f"  {name}: kernel={data['kernel_size']}, rounds={data['rounds']}, "
                f"actual_forbid={data['actual_forbidden_frac']:.6f}, "
                f"shuffled_forbid={data['shuffled_forbidden_frac']:.6f}"
            )


if __name__ == "__main__":
    main()
