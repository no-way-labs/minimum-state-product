#!/usr/bin/env python3
"""Probe conflict-state forbidden mass across non-sweep fc=2 BAF words."""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter, defaultdict
from itertools import product as iproduct

import numpy as np


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
for path in [CLAUDE_DIR, INFO_DIR]:
    if path not in sys.path:
        sys.path.insert(0, path)

from anova_interaction_spectrum import anova_spectrum
from cic_case3a_proof5 import enumerate_fc2_walks, enumerate_state_sequences, is_sweep  # type: ignore


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
    steps = set()
    for t, cfg in enumerate(good):
        for p in range(n):
            triple = (cfg[(p - 1) % n], cfg[p], cfg[(p + 1) % n])
            if triple in overlaps[p]:
                steps.add(t)
    return sorted(steps)


def valid_good_cycles(word, n, ms):
    L = len(word)
    fc = [0] * n
    for p in word:
        fc[p] += 1
    proc_seqs = {p: enumerate_state_sequences(ms[p], fc[p]) for p in range(n)}
    goods = []
    for combo in iproduct(*[proc_seqs[p] for p in range(n)]):
        ss = {p: combo[p] for p in range(n)}
        fcc = [0] * n
        configs = [tuple(ss[p][0] for p in range(n))]
        for t in range(L):
            fcc[word[t]] += 1
            configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
        if configs[-1] != configs[0]:
            continue
        good = configs[:-1]
        if len(set(good)) != L:
            continue
        goods.append(good)
    return goods


def conflict_state_forbid(good, word, ms):
    n = len(ms)
    steps = conflict_steps(good, word, n)
    states = {tuple(good[t]) for t in steps}
    cfgs = list(iproduct(*[range(m) for m in ms]))
    vals = np.array([1.0 if c in states else 0.0 for c in cfgs], dtype=np.float64)
    aa, af, _, _ = anova_spectrum(ms, vals, n - 2)
    return af / (aa + af) if aa + af else 0.0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-from", type=int, default=5)
    parser.add_argument("--n-to", type=int, default=8)
    args = parser.parse_args()

    for n in range(args.n_from, args.n_to + 1):
        ms = [2, 2, 2] + [3] * (n - 3)
        words = [w for w in enumerate_fc2_walks(n) if not is_sweep(w, n)]
        mins = Counter()
        samples = []
        for w in words:
            goods = valid_good_cycles(w, n, ms)
            vals = [conflict_state_forbid(g, w, ms) for g in goods]
            if not vals:
                continue
            m = min(vals)
            mins[m] += 1
            if len(samples) < 8:
                samples.append((w, m, len(goods)))
        print(f"n={n} words={len(words)}")
        print("  minima:", dict(mins))
        for w, m, count in samples:
            print("  sample", m, "goods", count, "word", w)


if __name__ == "__main__":
    main()
