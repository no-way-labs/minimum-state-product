#!/usr/bin/env python3
"""Verify the exact basis-coefficient formulas on the representative family."""

from __future__ import annotations

import argparse
from fractions import Fraction
import os
import sys


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
LB_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "info_theory", "lb_obstruction")
if LB_DIR not in sys.path:
    sys.path.insert(0, LB_DIR)

from ec_basis_inner_probe import representative_inner_exact


R = Fraction(-1, 2)


def two_pow(exp: int) -> Fraction:
    if exp >= 0:
        return Fraction(2**exp, 1)
    return Fraction(1, 2 ** (-exp))


def formula_value(n: int, d: int) -> Fraction:
    if d == 0:
        a = two_pow(n - 7) / Fraction(3 ** (2 * n - 6), 1)
        return a * (1 - R ** (n - 2)) / (1 - R)
    if d == 1:
        a = two_pow(n - 6) / Fraction(3 ** (2 * n - 6), 1)
        return a * (2 - R - (R ** (n - 3))) / (1 - R)
    a = two_pow(n - 8) / Fraction(3 ** (2 * n - 7), 1)
    if d % 2 == 1:
        return a * (2 - R ** (d - 2) - R ** (n - d - 2)) / (1 - R)
    return -a * (1 + R ** (d - 2) + R ** (n - d - 2)) / (1 - R)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-from", type=int, required=True)
    parser.add_argument("--n-to", type=int, required=True)
    args = parser.parse_args()

    for n in range(args.n_from, args.n_to + 1):
        failures = []
        for d in range(n // 2 + 1):
            actual = representative_inner_exact(n, d)
            expected = formula_value(n, d)
            if actual != expected:
                failures.append((d, actual, expected))
        print(f"n={n} failures={len(failures)}")
        for row in failures[:5]:
            print("  FAIL", row)


if __name__ == "__main__":
    main()
