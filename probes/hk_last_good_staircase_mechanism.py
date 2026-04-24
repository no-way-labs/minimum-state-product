#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import sys
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(__file__))
GPT_SCRIPTS = os.path.join(ROOT, "gpt", "scripts")
sys.path.insert(0, GPT_SCRIPTS)

from p2_good_cycle_search import enumerate_good_cycles  # type: ignore


def local_five(t: int, n: int) -> set[int]:
    return {(t - 2) % n, (t - 1) % n, t, (t + 1) % n, (t + 2) % n}


def pivots(ms: tuple[int, ...]) -> list[int]:
    n = len(ms)
    return [i for i in range(n) if ms[(i - 1) % n] == 2 and ms[(i + 1) % n] == 2]


def hk_last_instances(movers: tuple[int, ...], n: int, pivs: list[int]) -> list[tuple[int, int]]:
    hits = []
    for t in pivs:
        outside = [idx for idx, mover in enumerate(movers) if mover not in local_five(t, n)]
        if outside and outside[-1] + 1 == len(movers):
            hits.append((t, outside[-1]))
    return hits


def staircase4(bits: tuple[int, int, int, int]) -> bool:
    a, b, c, d = bits
    return (a <= b <= c <= d) or (a >= b >= c >= d)


def is_forward_sweep(movers: tuple[int, ...], n: int) -> bool:
    return all(movers[k] == (k % n) for k in range(len(movers)))


def is_reverse_sweep(movers: tuple[int, ...], n: int) -> bool:
    return all(movers[k] == ((-k) % n) for k in range(len(movers)))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=9)
    parser.add_argument("--max-cycles", type=int, default=100)
    parser.add_argument("--time-limit", type=float, default=8.0)
    args = parser.parse_args()

    n = args.n
    ms = tuple(2 for _ in range(n))
    coords = (0, n - 4, n - 3, n - 2)
    pivs = pivots(ms)

    hk_cycles = 0
    sweep_kinds = Counter()
    proj_counter = Counter()
    sample = []

    for cycle, movers in enumerate_good_cycles(ms, max_cycles=args.max_cycles, time_limit=args.time_limit):
        hits = hk_last_instances(movers, n, pivs)
        if not hits:
            continue
        hk_cycles += 1
        if is_forward_sweep(movers, n):
            sweep_kinds["forward"] += 1
        elif is_reverse_sweep(movers, n):
            sweep_kinds["reverse"] += 1
        else:
            sweep_kinds["other"] += 1
        good_proj = tuple(tuple(cfg[i] for i in coords) for cfg in cycle)
        all_stair = all(staircase4(bits) for bits in good_proj)
        proj_counter[all_stair] += 1
        if len(sample) < 3:
            sample.append((movers, hits, good_proj[:10], all_stair))

    print(f"n={n} state_counts={ms} coords={coords}")
    print(f"hk_last_cycles={hk_cycles}")
    print(f"sweep_kinds={dict(sweep_kinds)}")
    print(f"all_projections_staircase={dict(proj_counter)}")
    for idx, (movers, hits, proj, all_stair) in enumerate(sample, 1):
        print(f"\nSample {idx}")
        print(f"movers={movers}")
        print(f"hk_last_hits={hits}")
        print(f"first_projections={proj}")
        print(f"all_stair={all_stair}")


if __name__ == "__main__":
    main()
