#!/usr/bin/env python3
"""Check sweep/shadow equivariance under ternary 1<->2 relabelings."""

from __future__ import annotations

import argparse
import itertools
import os
import sys


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
DOCS_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "docs")
for path in [DOCS_DIR]:
    if path not in sys.path:
        sys.path.insert(0, path)

from verify_lower_bound import (  # type: ignore
    check_cycle_consistency,
    construct_sweep_cycle,
    find_shadow_cycle,
    get_rotation_classes,
)


def relabel_map(ms, eps_src, eps_dst):
    ternary = [i for i, m in enumerate(ms) if m == 3]
    swaps = {i for i in ternary if eps_src[i] != eps_dst[i]}

    def tau(cfg):
        lst = list(cfg)
        for i in swaps:
            if lst[i] == 1:
                lst[i] = 2
            elif lst[i] == 2:
                lst[i] = 1
        return tuple(lst)

    return tau


def build_shadow(ms, eps):
    n = len(ms)
    cyc = construct_sweep_cycle(ms, n, eps)
    if cyc is None:
        raise RuntimeError("failed to construct sweep")
    ok, det, msg = check_cycle_consistency(cyc, n, ms)
    if not ok:
        raise RuntimeError(msg)
    shadow = find_shadow_cycle(det, set(cyc), ms, n, max_len=300)
    if shadow is None:
        raise RuntimeError("no shadow cycle found")
    return cyc, shadow


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-from", type=int, default=5)
    parser.add_argument("--n-to", type=int, default=7)
    args = parser.parse_args()

    total = 0
    failures = []
    for n in range(args.n_from, args.n_to + 1):
        classes = get_rotation_classes(n, 3, 3)
        for ms in classes:
            ternary = [i for i, m in enumerate(ms) if m == 3]
            assignments = []
            for vals in itertools.product([1, 2], repeat=len(ternary)):
                eps = {i: v for i, v in zip(ternary, vals)}
                cyc, shadow = build_shadow(list(ms), eps)
                assignments.append((eps, cyc, shadow))
            base_eps, base_cyc, base_shadow = assignments[0]
            for eps, cyc, shadow in assignments[1:]:
                tau = relabel_map(ms, base_eps, eps)
                total += 1
                if [tau(c) for c in base_cyc] != cyc:
                    failures.append(("cycle", n, ms, base_eps, eps))
                if [tau(c) for c in base_shadow] != shadow:
                    failures.append(("shadow", n, ms, base_eps, eps))
        print(f"n={n}: checked {len(classes)} classes")
    print(f"comparisons={total}")
    print(f"failures={len(failures)}")
    for row in failures[:20]:
        print("FAIL", row)


if __name__ == "__main__":
    main()
