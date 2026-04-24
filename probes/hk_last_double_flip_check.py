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


def flip2(cfg: tuple[int, ...], i: int, j: int, ms: tuple[int, ...]) -> tuple[int, ...]:
    out = list(cfg)
    out[i] = (out[i] + 1) % ms[i]
    out[j] = (out[j] + 1) % ms[j]
    return tuple(out)


def main() -> None:
    n = 7
    ms = (2,) * n
    count = 0
    off = 0
    on = 0
    for cycle, movers in enumerate_good_cycles(ms, max_cycles=80, time_limit=8.0):
        if not hk_last_instances(movers, n, pivots(ms)):
            continue
        count += 1
        c0 = cycle[0]
        cflip = flip2(c0, 0, 1, ms)
        if cflip in cycle:
            on += 1
            print(f"ON  movers={movers} flip2(gc[0],0,1)={cflip}")
        else:
            off += 1
            if off <= 5:
                print(f"OFF movers={movers} flip2(gc[0],0,1)={cflip}")
    print(f"\nhk_last cycles checked={count} off={off} on={on}")


if __name__ == "__main__":
    main()
