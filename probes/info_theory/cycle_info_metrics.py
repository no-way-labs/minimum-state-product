#!/usr/bin/env python3
"""Information-theoretic metrics for valid good cycles.

This script treats a good cycle as a distributed zero-error coding object:

- Step index K is the hidden source.
- Each processor i observes a local context C_i(K) = (L,S,R).
- The mover bit R_i(K) = 1[moverAt(K) = i] must be zero-error decodable from C_i.

For known valid witnesses we measure:
- local context support sizes
- mover/non-mover support sizes
- empirical entropies H(C_i) and H(R_i)
- a Shearer-style support/entropy bound

The goal is not to prove the threshold directly, but to identify what
information quantities are actually active on working systems.
"""

from __future__ import annotations

import argparse
import math
import os
import sys
from collections import Counter
from dataclasses import dataclass
from functools import reduce
from operator import mul
from typing import Callable, Iterable


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
CLAUDE_DIR = os.path.join(REPO_ROOT, "paper2_dev_010", "claude")
if CLAUDE_DIR not in sys.path:
    sys.path.insert(0, CLAUDE_DIR)

from cup2_theorem import build_system as build_cup2_system  # type: ignore
from verifier import verify_system  # type: ignore


TransitionFn = Callable[[int, int, int], int]


def product(values: Iterable[int]) -> int:
    return reduce(mul, values, 1)


def log2_or_zero(x: float) -> float:
    return 0.0 if x <= 0.0 else math.log2(x)


def entropy(counter: Counter) -> float:
    total = sum(counter.values())
    if total == 0:
        return 0.0
    ans = 0.0
    for count in counter.values():
        p = count / total
        ans -= p * math.log2(p)
    return ans


def binary_entropy(p: float) -> float:
    if p <= 0.0 or p >= 1.0:
        return 0.0
    return -p * math.log2(p) - (1.0 - p) * math.log2(1.0 - p)


def sol3_v1_rules(ms: list[int], n: int) -> list[TransitionFn]:
    """Dijkstra Solution 3 style rules used in local exploratory scripts."""

    def make_bottom(m0: int) -> TransitionFn:
        def f(left: int, self_: int, right: int) -> int:
            if (self_ + 1) % m0 == right % m0:
                return (self_ - 1) % m0
            return self_

        return f

    def make_top(m_top: int) -> TransitionFn:
        def f(left: int, self_: int, right: int) -> int:
            if left % m_top == right % m_top and not (left % m_top == (self_ - 1) % m_top):
                return (left % m_top + 1) % m_top
            return self_

        return f

    def make_middle(m_i: int) -> TransitionFn:
        def f(left: int, self_: int, right: int) -> int:
            if (self_ + 1) % m_i == left % m_i:
                return left % m_i
            if (self_ + 1) % m_i == right % m_i:
                return right % m_i
            return self_

        return f

    fs: list[TransitionFn] = [make_bottom(ms[0])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i]))
    fs.append(make_top(ms[n - 1]))
    return fs


@dataclass(frozen=True)
class FamilySpec:
    name: str
    ms: list[int]
    fs: list[TransitionFn]


def build_family(name: str, n: int) -> FamilySpec:
    if name == "cup2":
        ms, fs = build_cup2_system(n)
        return FamilySpec(name=f"CUP-2(n={n})", ms=ms, fs=fs)
    if name == "sol3":
        ms = [3] * n
        fs = sol3_v1_rules(ms, n)
        return FamilySpec(name=f"Sol3(n={n})", ms=ms, fs=fs)
    raise ValueError(f"unknown family: {name}")


def cycle_movers(cycle: list[tuple[int, ...]]) -> list[int]:
    n = len(cycle[0])
    movers = []
    for idx, cfg in enumerate(cycle):
        nxt = cycle[(idx + 1) % len(cycle)]
        diffs = [j for j in range(n) if cfg[j] != nxt[j]]
        if len(diffs) != 1:
            raise ValueError(f"step {idx} has {len(diffs)} movers")
        movers.append(diffs[0])
    return movers


def shearer_support_bound(support_sizes: list[int]) -> float:
    total = sum(log2_or_zero(size) for size in support_sizes) / 3.0
    return 2.0 ** total


def analyze_family(spec: FamilySpec) -> str:
    result = verify_system(spec.ms, spec.fs)
    if not result.get("valid"):
        raise ValueError(f"{spec.name} is not valid according to verifier")

    cycle = result["cycle"]
    n = len(spec.ms)
    movers = cycle_movers(cycle)
    cycle_len = len(cycle)
    prod = product(spec.ms)
    support_sizes: list[int] = []
    entropy_sizes: list[float] = []
    lines: list[str] = []

    lines.append(f"{spec.name}")
    lines.append(f"  n={n}, product={prod}, cycle_len={cycle_len}")
    lines.append(f"  log2(product)={log2_or_zero(prod):.4f}, log2(cycle_len)={log2_or_zero(cycle_len):.4f}")
    lines.append("")
    lines.append(
        "  proc  m_i  cap  supp  |M|  |N|  overlap  fireCt   H(C_i)   H(R_i)   I(C_i;R_i)"
    )
    lines.append(
        "  ----  ---  ---  ----  ---  ---  -------  ------   ------   ------   ---------"
    )

    for proc in range(n):
        contexts = []
        roles = []
        for idx, cfg in enumerate(cycle):
            context = (cfg[(proc - 1) % n], cfg[proc], cfg[(proc + 1) % n])
            contexts.append(context)
            roles.append(1 if movers[idx] == proc else 0)

        ctx_counter = Counter(contexts)
        mover_counter = Counter(ctx for idx, ctx in enumerate(contexts) if roles[idx] == 1)
        nonmover_counter = Counter(ctx for idx, ctx in enumerate(contexts) if roles[idx] == 0)

        support = len(ctx_counter)
        support_sizes.append(support)

        h_ctx = entropy(ctx_counter)
        entropy_sizes.append(h_ctx)

        fire_count = sum(roles)
        p_role = fire_count / cycle_len
        h_role = binary_entropy(p_role)

        overlap = len(set(mover_counter) & set(nonmover_counter))
        if overlap != 0:
            raise ValueError(f"{spec.name} has overlap at proc {proc}")

        cap = spec.ms[(proc - 1) % n] * spec.ms[proc] * spec.ms[(proc + 1) % n]
        lines.append(
            f"  {proc:>4}  {spec.ms[proc]:>3}  {cap:>3}  {support:>4}  "
            f"{len(mover_counter):>3}  {len(nonmover_counter):>3}  {overlap:>7}  "
            f"{fire_count:>6}   {h_ctx:>6.3f}   {h_role:>6.3f}   {h_role:>9.3f}"
        )

    lines.append("")
    lines.append("  global summaries")
    lines.append(
        f"  - avg local support = {sum(support_sizes) / n:.4f}"
    )
    lines.append(
        f"  - max local support = {max(support_sizes)}"
    )
    lines.append(
        f"  - avg H(C_i) = {sum(entropy_sizes) / n:.4f} bits"
    )
    lines.append(
        f"  - Shearer support bound: cycle_len <= {shearer_support_bound(support_sizes):.4f}"
    )
    lines.append(
        f"  - Geometric mean support^(1/3 sum): {(product(support_sizes)) ** (1.0 / 3.0):.4f}"
    )

    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--family",
        choices=["cup2", "sol3", "all"],
        default="all",
        help="which witness family to analyze",
    )
    parser.add_argument(
        "--n",
        type=int,
        default=9,
        help="ring size",
    )
    args = parser.parse_args()

    families = ["cup2", "sol3"] if args.family == "all" else [args.family]
    outputs = []
    for family in families:
        spec = build_family(family, args.n)
        outputs.append(analyze_family(spec))
    print("\n\n".join(outputs))


if __name__ == "__main__":
    main()
