#!/usr/bin/env python3
"""Probe the EC witness across all non-sweep fc=2 BAF words."""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter, defaultdict
from itertools import product as iproduct


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
if CLAUDE_DIR not in sys.path:
    sys.path.insert(0, CLAUDE_DIR)

from cic_case3a_proof5 import enumerate_fc2_walks, enumerate_state_sequences, is_sweep  # type: ignore


def ec_total_stats(word, n, ms):
    L = len(word)
    fc = [0] * n
    for p in word:
        fc[p] += 1
    proc_seqs = {p: enumerate_state_sequences(ms[p], fc[p]) for p in range(n)}
    totals = Counter()
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
        mover_triples = defaultdict(set)
        nonmover_triples = defaultdict(set)
        for t, c in enumerate(good):
            mover = word[t]
            for p in range(n):
                triple = (c[(p - 1) % n], c[p], c[(p + 1) % n])
                if p == mover:
                    mover_triples[p].add(triple)
                else:
                    nonmover_triples[p].add(triple)
        total = sum(len(mover_triples[p] & nonmover_triples[p]) for p in range(n))
        totals[total] += 1
    return totals


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-from", type=int, default=5)
    parser.add_argument("--n-to", type=int, default=9)
    args = parser.parse_args()

    for n in range(args.n_from, args.n_to + 1):
        ms = [2, 2, 2] + [3] * (n - 3)
        words = [w for w in enumerate_fc2_walks(n) if not is_sweep(w, n)]
        minima = Counter()
        print(f"n={n} non_sweep_words={len(words)}")
        for w in words:
            totals = ec_total_stats(w, n, ms)
            if not totals:
                continue
            m = min(totals)
            minima[m] += 1
        print("  minima:", dict(minima))


if __name__ == "__main__":
    main()
