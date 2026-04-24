#!/usr/bin/env python3
from __future__ import annotations

import os
import sys

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


def main() -> None:
    n = 7
    ms = (2,) * n
    count = 0
    any_match = 0
    for cycle, movers in enumerate_good_cycles(ms, max_cycles=80, time_limit=8.0):
        hits = hk_last_instances(movers, n, pivots(ms))
        if not hits:
            continue
        i0 = movers[0]
        c0 = cycle[0]
        count += 1
        matched_here = []
        for t, k_out in hits:
            for j, cfg in enumerate(cycle):
                diff = {i for i, (a, b) in enumerate(zip(cfg, c0)) if a != b}
                if diff == {i0, t}:
                    matched_here.append((t, j))
        if matched_here:
            any_match += 1
            print(f"MATCH movers={movers} i0={i0} matches={matched_here}")
        elif count <= 5:
            print(f"NO-MATCH movers={movers} i0={i0}")
    print(f"\nhk_last cycles checked={count} cycles_with_match={any_match}")


if __name__ == "__main__":
    main()
