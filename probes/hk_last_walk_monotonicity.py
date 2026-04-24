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


def direction(a: int, b: int, n: int) -> str:
    if b == (a + 1) % n:
        return "R"
    if b == (a - 1) % n:
        return "L"
    if b == a:
        return "S"
    return "?"


def shorter_dir(i0: int, t: int, n: int) -> str:
    dr = (t - i0) % n
    dl = (i0 - t) % n
    return "R" if dr <= dl else "L"


def main() -> None:
    n = 7
    ms = (2,) * n
    checked = 0
    backtracks = 0
    for cycle, movers in enumerate_good_cycles(ms, max_cycles=80, time_limit=8.0):
        hits = hk_last_instances(movers, n, pivots(ms))
        if not hits:
            continue
        i0 = movers[0]
        for t, k_out in hits:
            want = shorter_dir(i0, t, n)
            k_t = None
            for k, mv in enumerate(movers):
                if mv == t and k > 0:
                    k_t = k
                    break
            if k_t is None:
                continue
            dirs = [direction(movers[k], movers[k + 1], n) for k in range(k_t)]
            bad = [d for d in dirs if d not in (want, "S")]
            checked += 1
            if bad:
                backtracks += 1
                print(f"BACKTRACK i0={i0} t={t} want={want} k_t={k_t} movers_prefix={movers[:k_t+1]} dirs={dirs}")
            elif checked <= 12:
                print(f"MONO i0={i0} t={t} want={want} k_t={k_t} movers_prefix={movers[:k_t+1]} dirs={dirs}")
    print(f"\nchecked={checked} backtrack_profiles={backtracks}")


if __name__ == "__main__":
    main()
