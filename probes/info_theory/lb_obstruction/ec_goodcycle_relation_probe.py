#!/usr/bin/env python3
"""Compare canonical EC conflict-state indicator to the good-cycle indicator."""

from __future__ import annotations

import argparse
import os
import sys
from itertools import product as iproduct

import numpy as np


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
LB_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory", "lb_obstruction")
for path in [INFO_DIR, LB_DIR]:
    if path not in sys.path:
        sys.path.insert(0, path)

from anova_interaction_spectrum import anova_spectrum
from ec_derived_spectrum import simple_baf_cycle, conflict_steps


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-from", type=int, default=5)
    parser.add_argument("--n-to", type=int, default=8)
    args = parser.parse_args()

    for n in range(args.n_from, args.n_to + 1):
        ms = [2, 2, 2] + [3] * (n - 3)
        good, word = simple_baf_cycle(ms)
        _, steps = conflict_steps(good, word, n)
        cfgs = list(iproduct(*[range(m) for m in ms]))
        good_set = {tuple(c) for c in good}
        conf_set = {tuple(good[t]) for t in steps}
        chi_good = np.array([1.0 if c in good_set else 0.0 for c in cfgs], dtype=np.float64)
        chi_conf = np.array([1.0 if c in conf_set else 0.0 for c in cfgs], dtype=np.float64)
        exc = chi_good - chi_conf
        ga, gf, _, _ = anova_spectrum(ms, chi_good, n - 2)
        ca, cf, _, _ = anova_spectrum(ms, chi_conf, n - 2)
        ea, ef, _, _ = anova_spectrum(ms, exc, n - 2)
        print(f"n={n}")
        print(f"  good_state_count={int(np.sum(chi_good))} conf_state_count={int(np.sum(chi_conf))} exc_count={int(np.sum(exc))}")
        print(f"  chi_good forbid={gf/(ga+gf):.6f}")
        print(f"  chi_conf forbid={cf/(ca+cf):.6f}")
        print(f"  exceptional4 forbid={ef/(ea+ef):.6f}")


if __name__ == "__main__":
    main()
