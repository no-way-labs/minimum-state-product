#!/usr/bin/env python3
"""Probe explicit product-basis inner products on EC bridge representatives."""

from __future__ import annotations

import argparse
from fractions import Fraction
import math
import os
import sys
from itertools import product as iproduct


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
LB_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory", "lb_obstruction")
if LB_DIR not in sys.path:
    sys.path.insert(0, LB_DIR)

from ec_bridge_geometry_probe import build_simple_good, conflict_steps_from_good
from ec_distance_class_values import representative_word


def candidate_complement(d: int) -> tuple[int, ...]:
    if d == 0:
        return (1,)
    if d % 2 == 0:
        return (1, d + 1)
    if d == 1:
        return (0, 2)
    return (0, d + 1)


def phi(x: int, m: int) -> float:
    return (1.0 if x == 0 else 0.0) - 1.0 / m


def phi_exact(x: int, m: int) -> Fraction:
    return Fraction(1 if x == 0 else 0, 1) - Fraction(1, m)


def representative_inner(n: int, d: int) -> float:
    ms = [2, 2, 2] + [3] * (n - 3)
    word = representative_word(n, d)
    good = build_simple_good(list(word), n)
    steps = set(conflict_steps_from_good(good, list(word), n))
    states = {tuple(good[t]) for t in steps}
    comp = candidate_complement(d)
    keep = [i for i in range(n) if i not in comp]
    total = 0.0
    denom = math.prod(ms)
    for cfg in iproduct(*[range(m) for m in ms]):
        if cfg in states:
            prod = 1.0
            for i in keep:
                prod *= phi(cfg[i], ms[i])
            total += prod
    return total / denom


def representative_inner_exact(n: int, d: int) -> Fraction:
    ms = [2, 2, 2] + [3] * (n - 3)
    word = representative_word(n, d)
    good = build_simple_good(list(word), n)
    steps = set(conflict_steps_from_good(good, list(word), n))
    states = {tuple(good[t]) for t in steps}
    comp = candidate_complement(d)
    keep = [i for i in range(n) if i not in comp]
    total = Fraction(0, 1)
    denom = math.prod(ms)
    for cfg in iproduct(*[range(m) for m in ms]):
        if cfg in states:
            prod = Fraction(1, 1)
            for i in keep:
                prod *= phi_exact(cfg[i], ms[i])
            total += prod
    return total / denom


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-from", type=int, required=True)
    parser.add_argument("--n-to", type=int, required=True)
    args = parser.parse_args()

    for n in range(args.n_from, args.n_to + 1):
        print(f"n={n}")
        for d in range(n // 2 + 1):
            inner = representative_inner(n, d)
            print(f"  d={d} inner={inner:.18g}")


if __name__ == "__main__":
    main()
