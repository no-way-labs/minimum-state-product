#!/usr/bin/env python3
"""Feature search for the residual constant-FutureFc slice rank.

Base key:
    (FutureFc, boundary6, exp2, int21, exp2_weight)

Searches simple additional interior features and reports the mutual-information
gain with cf_rank.
"""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter, defaultdict


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
if CLAUDE_DIR not in sys.path:
    sys.path.insert(0, CLAUDE_DIR)

from cup2_theorem import build_system as build_cup2_system  # type: ignore
from verifier import verify_system  # type: ignore

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


def pair_positions(cfg):
    n = len(cfg)
    pairs = defaultdict(list)
    for j in range(2, n - 2):
        pairs[(cfg[j], cfg[(j + 1) % n])].append(j)
    return pairs


def base_invariants(cfg):
    pairs = pair_positions(cfg)
    int21 = len(pairs[(2, 1)])
    int20 = len(pairs[(2, 0)])
    exp2 = int20 + int21
    ew = sum(pairs[(2, 1)]) + sum(pairs[(2, 0)])
    return (exp2, int21, ew)


def make_feature_bank(cfgs):
    feats = {}

    def add(name, fn):
        feats[name] = [fn(cfg) for cfg in cfgs]

    # Single-value interior counts
    for v in range(3):
        add(f"count_val_{v}", lambda c, v=v: sum(1 for j in range(2, len(c) - 2) if c[j] == v))

    # Adjacent pair counts and weighted counts
    for a in range(3):
        for b in range(3):
            add(f"count_pair_{a}{b}", lambda c, a=a, b=b: len(pair_positions(c)[(a, b)]))
            add(f"weight_pair_{a}{b}", lambda c, a=a, b=b: sum(pair_positions(c)[(a, b)]))
            add(
                f"min_pair_{a}{b}",
                lambda c, a=a, b=b: min(pair_positions(c)[(a, b)]) if pair_positions(c)[(a, b)] else -1,
            )
            add(
                f"max_pair_{a}{b}",
                lambda c, a=a, b=b: max(pair_positions(c)[(a, b)]) if pair_positions(c)[(a, b)] else -1,
            )

    # Interior parity/value summaries
    add("even_val_sum", lambda c: sum(c[j] for j in range(2, len(c) - 2) if j % 2 == 0))
    add("odd_val_sum", lambda c: sum(c[j] for j in range(2, len(c) - 2) if j % 2 == 1))
    add("interior_sum", lambda c: sum(c[j] for j in range(2, len(c) - 2)))

    return feats


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["cup2", "sol3"], required=True)
    parser.add_argument("--n", type=int, default=9)
    parser.add_argument("--greedy-steps", type=int, default=0)
    args = parser.parse_args()

    label, ms, fs = build_family(args.family, args.n)
    result = verify_system(ms, fs)
    good = set(result["good_configs"])
    bad, bad_set, adj, ff = future_fc(ms, fs, good)
    cfr = constant_ff_rank(bad, adj, ff)
    ys = [cfr[c] for c in bad]

    base = [(ff[c], boundary6(c), base_invariants(c)) for c in bad]
    base_mi = mutual_information(base, ys)
    print(label)
    print(f"  base MI = {base_mi:.6f}")

    bank = make_feature_bank(bad)
    scored = []
    for name, vals in bank.items():
        keys = [(*base[i], vals[i]) for i in range(len(bad))]
        mi = mutual_information(keys, ys)
        scored.append((mi - base_mi, mi, name))
    scored.sort(reverse=True)
    for gain, mi, name in scored[:25]:
        print(f"  {name}: gain={gain:.6f}, total_MI={mi:.6f}")

    if args.greedy_steps > 0:
        print("  greedy:")
        current = list(base)
        used = set()
        for step in range(args.greedy_steps):
            best_name = None
            best_mi = None
            best_vals = None
            for name, vals in bank.items():
                if name in used:
                    continue
                keys = [(*current[i], vals[i]) for i in range(len(bad))]
                mi = mutual_information(keys, ys)
                if best_mi is None or mi > best_mi:
                    best_mi = mi
                    best_name = name
                    best_vals = vals
            used.add(best_name)
            current = [(*current[i], best_vals[i]) for i in range(len(bad))]
            print(f"  - step {step + 1}: {best_name}, total_MI={best_mi:.6f}")


if __name__ == "__main__":
    main()
