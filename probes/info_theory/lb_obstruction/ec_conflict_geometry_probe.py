#!/usr/bin/env python3
"""Probe the conflict-state support formula on non-sweep fc=2 BAF words."""

from __future__ import annotations

import argparse
import os
import sys
from collections import Counter


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
LB_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory", "lb_obstruction")
for path in [CLAUDE_DIR, LB_DIR]:
    if path not in sys.path:
        sys.path.insert(0, path)

from cic_case3a_proof5 import enumerate_fc2_walks, is_sweep  # type: ignore
from ec_derived_spectrum import conflict_steps


def build_good_from_word(word, n):
    seqs = {p: [0, 1, 0] for p in range(n)}
    fcc = [0] * n
    configs = [tuple(seqs[p][0] for p in range(n))]
    for mover in word:
        fcc[mover] += 1
        configs.append(tuple(seqs[p][fcc[p]] for p in range(n)))
    if configs[-1] != configs[0] or len(set(configs[:-1])) != len(configs) - 1:
        return None
    return configs[:-1]


def turn_steps(word, n):
    L = len(word)
    dirs = [(word[(i + 1) % L] - word[i]) % n for i in range(L)]
    turns = []
    for i in range(L):
        if dirs[i] != dirs[i - 1]:
            turns.append(i)
    return turns


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-from", type=int, default=5)
    parser.add_argument("--n-to", type=int, default=8)
    args = parser.parse_args()

    for n in range(args.n_from, args.n_to + 1):
        words = [w for w in enumerate_fc2_walks(n) if not is_sweep(w, n)]
        failures = []
        for w in words:
            good = build_good_from_word(w, n)
            if good is None:
                continue
            overlaps, steps = conflict_steps(good, w, n)
            turns = turn_steps(w, n)
            predicted = sorted(set(range(len(w))) - {turns[0], (turns[0] + 1) % len(w), turns[1], (turns[1] + 1) % len(w)})
            if steps != predicted:
                failures.append((w, turns, steps, predicted))
        print(f"n={n} non_sweep_words={len(words)} failures={len(failures)}")
        for row in failures[:5]:
            print("  FAIL", row)


if __name__ == "__main__":
    main()
