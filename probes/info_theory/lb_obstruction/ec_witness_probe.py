#!/usr/bin/env python3
"""Probe canonical EC witnesses on BAF-style cycles."""

from __future__ import annotations

import argparse
import os
import sys
from collections import defaultdict


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
if CLAUDE_DIR not in sys.path:
    sys.path.insert(0, CLAUDE_DIR)


def canonical_baf_word(n: int) -> list[int]:
    return list(range(n)) + list(range(n - 2, 0, -1)) + [0, n - 1]


def simple_baf_cycle(ms):
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
    good = configs[:-1]
    return good, word


def overlap_profile(good, word, n):
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
    counts = {p: len(v) for p, v in overlaps.items()}
    return overlaps, counts


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-from", type=int, default=5)
    parser.add_argument("--n-to", type=int, default=12)
    args = parser.parse_args()

    for n in range(args.n_from, args.n_to + 1):
        ms = [2, 2, 2] + [3] * (n - 3)
        good, word = simple_baf_cycle(ms)
        overlaps, counts = overlap_profile(good, word, n)
        conflict_procs = [p for p, c in counts.items() if c > 0]
        total = sum(counts.values())
        print(f"n={n} word_len={len(word)}")
        print(f"  conflict_procs={conflict_procs}")
        print(f"  overlap_counts={counts}")
        print(f"  total_overlap={total}")


if __name__ == "__main__":
    main()
