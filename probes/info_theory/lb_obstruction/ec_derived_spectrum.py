#!/usr/bin/env python3
"""Forbidden spectra for nonlocal EC-derived scalars."""

from __future__ import annotations

import argparse
import os
import sys
from collections import defaultdict
from itertools import product as iproduct

import numpy as np


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
LB_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory", "lb_obstruction")
for path in [INFO_DIR, LB_DIR]:
    if path not in sys.path:
        sys.path.insert(0, path)

from anova_interaction_spectrum import anova_spectrum
from ec_witness_probe import canonical_baf_word, simple_baf_cycle


def conflict_steps(good, word, n):
    mover_triples = defaultdict(set)
    nonmover_triples = defaultdict(set)
    for t, cfg in enumerate(good):
        mover = word[t]
        for p in range(n):
            triple = (cfg[(p - 1) % n], cfg[p], cfg[(p + 1) % n])
            if p == mover:
                mover_triples[p].add(triple)
            else:
                nonmover_triples[p].add(triple)

    overlaps = {p: mover_triples[p] & nonmover_triples[p] for p in range(n)}
    bad_steps = set()
    for t, cfg in enumerate(good):
        for p in range(n):
            triple = (cfg[(p - 1) % n], cfg[p], cfg[(p + 1) % n])
            if triple in overlaps[p]:
                bad_steps.add(t)
    return overlaps, sorted(bad_steps)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    args = parser.parse_args()

    n = args.n
    ms = [2, 2, 2] + [3] * (n - 3)
    good, word = simple_baf_cycle(ms)
    overlaps, steps = conflict_steps(good, word, n)
    cfgs = list(iproduct(*[range(m) for m in ms]))
    good_set = {tuple(c) for c in good}
    ec_states = {tuple(good[t]) for t in steps}

    indicator = np.array([1.0 if cfg in ec_states else 0.0 for cfg in cfgs], dtype=np.float64)
    aa, af, _, _ = anova_spectrum(ms, indicator, n - 2)
    print(f"n={n} ms={tuple(ms)}")
    print("overlap processors:", {p: sorted(v) for p, v in overlaps.items() if v})
    print("conflict steps:", steps)
    print("conflict_state_count:", len(ec_states))
    print(f"conflict_state_indicator actual_forbid={af/(aa+af) if aa+af else 0.0:.6f}")


if __name__ == "__main__":
    main()
