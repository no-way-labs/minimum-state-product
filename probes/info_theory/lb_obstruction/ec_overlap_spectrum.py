#!/usr/bin/env python3
"""Probe forbidden spectra of local entry-conflict witness scalars."""

from __future__ import annotations

import argparse
import os
import sys
from collections import defaultdict
from itertools import product as iproduct

import numpy as np


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
if INFO_DIR not in sys.path:
    sys.path.insert(0, INFO_DIR)

from anova_interaction_spectrum import anova_spectrum


def canonical_baf_word(n: int) -> list[int]:
    return list(range(n)) + list(range(n - 2, 0, -1)) + [0, n - 1]


def simple_baf_cycle(ms):
    """Build the simple [0,1,0] state-sequence cycle used in EC analysis."""
    n = len(ms)
    word = canonical_baf_word(n)
    fire_counts = [0] * n
    for p in word:
        fire_counts[p] += 1
    seqs = {p: [0, 1, 0] for p in range(n)}
    fcc = [0] * n
    configs = [tuple(seqs[p][0] for p in range(n))]
    for mover in word:
        fcc[mover] += 1
        configs.append(tuple(seqs[p][fcc[p]] for p in range(n)))
    if configs[-1] != configs[0]:
        raise RuntimeError("not cyclic")
    good = configs[:-1]
    if len(set(good)) != len(good):
        raise RuntimeError("not simple")
    return good, word


def overlap_sets(good, word, n):
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
    return {p: mover_triples[p] & nonmover_triples[p] for p in range(n)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--ms", nargs="+", type=int, required=True)
    args = parser.parse_args()

    ms = args.ms
    n = len(ms)
    good, word = simple_baf_cycle(ms)
    overlaps = overlap_sets(good, word, n)
    cfgs = list(iproduct(*[range(m) for m in ms]))

    total_overlap = np.array(
        [
            float(
                sum(
                    1
                    for p in range(n)
                    if (cfg[(p - 1) % n], cfg[p], cfg[(p + 1) % n]) in overlaps[p]
                )
            )
            for cfg in cfgs
        ],
        dtype=np.float64,
    )
    aa, af, _, _ = anova_spectrum(list(ms), total_overlap, n - 2)
    print(f"ms={tuple(ms)}")
    print("word:", word)
    print("overlap processors:", {p: sorted(v) for p, v in overlaps.items() if v})
    print(f"total_overlap actual_forbid={af/(aa+af) if aa+af else 0.0:.6f}")


if __name__ == "__main__":
    main()
