#!/usr/bin/env python3
"""Probe EC bridge values by turnaround geometry on the BAF family."""

from __future__ import annotations

import argparse
import os
import sys
from collections import defaultdict
from itertools import product as iproduct


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
INFO_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory")
LB_DIR = os.path.join(INFO_DIR, "lb_obstruction")
for path in [CLAUDE_DIR, INFO_DIR, LB_DIR]:
    if path not in sys.path:
        sys.path.insert(0, path)

from cic_case3a_proof5 import enumerate_fc2_walks, is_sweep  # type: ignore
from anova_interaction_spectrum import anova_spectrum
from ec_baf_conflict_state_probe import conflict_state_forbid, valid_good_cycles


def build_simple_good(word: list[int], n: int):
    seqs = {p: [0, 1, 0] for p in range(n)}
    fcc = [0] * n
    configs = [tuple(seqs[p][0] for p in range(n))]
    for mover in word:
        fcc[mover] += 1
        configs.append(tuple(seqs[p][fcc[p]] for p in range(n)))
    if configs[-1] != configs[0] or len(set(configs[:-1])) != len(configs) - 1:
        return None
    return configs[:-1]


def conflict_steps_from_good(good, word, n):
    mover_triples: dict[int, set[tuple[int, int, int]]] = defaultdict(set)
    nonmover_triples: dict[int, set[tuple[int, int, int]]] = defaultdict(set)
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


def simple_conflict_state_forbid(word, ms):
    n = len(ms)
    good = build_simple_good(word, n)
    if good is None:
        return None
    steps = conflict_steps_from_good(good, word, n)
    states = {tuple(good[t]) for t in steps}
    cfgs = list(iproduct(*[range(m) for m in ms]))
    vals = [1.0 if cfg in states else 0.0 for cfg in cfgs]
    aa, af, _, _ = anova_spectrum(ms, vals, n - 2)
    return af / (aa + af) if aa + af else 0.0


def turnaround_steps(word: list[int], n: int) -> tuple[int, int]:
    """Return the two step indices at which the walk changes direction."""
    L = len(word)
    turns: list[int] = []
    for t in range(L):
        prev_dir = (word[t] - word[t - 1]) % n
        next_dir = (word[(t + 1) % L] - word[t]) % n
        if prev_dir != next_dir:
            turns.append(t)
    if len(turns) != 2:
        raise ValueError(f"expected 2 turnaround steps, got {len(turns)} for {word}")
    return tuple(turns)


def normalized_step_gap(turns: tuple[int, int], cycle_len: int) -> tuple[int, int]:
    a, b = turns
    return tuple(sorted(((b - a) % cycle_len, (a - b) % cycle_len)))


def turnaround_vertex(word: tuple[int, ...] | list[int], turns: tuple[int, int]) -> int:
    return word[turns[0]]


def cyclic_distance(a: int, b: int, n: int) -> int:
    d = (a - b) % n
    return min(d, n - d)


def summarize_n(n: int, simple_only: bool):
    ms = [2, 2, 2] + [3] * (n - 3)
    by_gap: dict[tuple[int, int], list[tuple[tuple[int, ...], tuple[int, int], float, int]]] = defaultdict(list)
    for word in enumerate_fc2_walks(n):
        if is_sweep(word, n):
            continue
        if simple_only:
            minimum = simple_conflict_state_forbid(word, ms)
            if minimum is None:
                continue
            goods_count = 1
        else:
            goods = valid_good_cycles(word, n, ms)
            if not goods:
                continue
            minimum = min(conflict_state_forbid(good, word, ms) for good in goods)
            goods_count = len(goods)
        turns = turnaround_steps(word, n)
        gap = normalized_step_gap(turns, 2 * n)
        by_gap[gap].append((tuple(word), turns, minimum, goods_count))
    return by_gap


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-from", type=int, default=5)
    parser.add_argument("--n-to", type=int, default=8)
    parser.add_argument("--simple-only", action="store_true")
    args = parser.parse_args()

    for n in range(args.n_from, args.n_to + 1):
        by_gap = summarize_n(n, args.simple_only)
        print(f"n={n}")
        for gap, items in sorted(by_gap.items()):
            values = sorted({round(item[2], 12) for item in items})
            print(f"  gap={gap} words={len(items)} unique_minima={values}")
            for word, turns, minimum, goods in items[:4]:
                turn_v = turnaround_vertex(word, turns)
                dist1 = cyclic_distance(turn_v, 1, n)
                print(
                    "    "
                    f"turns={turns} turn_v={turn_v} dist_to_1={dist1} "
                    f"min={minimum:.12f} goods={goods} word={word}"
                )


if __name__ == "__main__":
    main()
