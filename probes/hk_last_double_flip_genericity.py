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


def check_family(ms: tuple[int, ...], max_cycles: int = 40):
    n = len(ms)
    total_hits = 0
    off_hits = 0
    counterexamples = []
    for cycle, movers in enumerate_good_cycles(ms, max_cycles=max_cycles, time_limit=8.0):
        hits = hk_last_instances(movers, n, pivots(ms))
        if not hits:
            continue
        i0 = movers[0]
        c0 = cycle[0]
        for t, k_out in hits:
            total_hits += 1
            cflip = flip2(c0, i0, t, ms)
            if cflip not in cycle:
                off_hits += 1
            elif len(counterexamples) < 8:
                counterexamples.append((movers, t, k_out, i0, cflip))
    return total_hits, off_hits, counterexamples


def main() -> None:
    families = [
        (2, 2, 2, 2, 2, 10),
        (2, 2, 2, 2, 2, 2, 14),
        (2, 2, 2, 2, 2, 2, 2, 22),
        (2,) * 9,
    ]
    for ms in families:
        total_hits, off_hits, counterexamples = check_family(ms)
        print(f"\nstate_counts={ms}")
        print(f"hk_last_hits={total_hits} off_hits={off_hits}")
        if counterexamples:
            print("counterexamples:")
            for movers, t, k_out, i0, cflip in counterexamples:
                print(f"  i0={i0} t={t} k_out={k_out} cflip={cflip} movers={movers}")


if __name__ == "__main__":
    main()
