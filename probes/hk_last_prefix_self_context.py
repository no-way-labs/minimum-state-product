#!/usr/bin/env python3
from __future__ import annotations

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


def main() -> None:
    families = [
        (2,) * 7,
        (2, 2, 2, 2, 2, 10),
        (2, 2, 2, 2, 2, 2, 14),
    ]
    for ms in families:
        n = len(ms)
        prof = Counter()
        examples = []
        checked = 0
        for cycle, movers in enumerate_good_cycles(ms, max_cycles=20, time_limit=6.0):
            hits = hk_last_instances(movers, n, pivots(ms))
            if not hits:
                continue
            for t, _ in hits[:1]:
                k_t = None
                for k, mv in enumerate(movers):
                    if mv == t and k > 0:
                        k_t = k
                        break
                if k_t is None:
                    continue
                for k in range(k_t):
                    p = movers[k]
                    l = (p - 1) % n
                    r = (p + 1) % n
                    pre = (cycle[k][l], cycle[k][p], cycle[k][r])
                    post = (cycle[(k + 1) % len(cycle)][l], cycle[(k + 1) % len(cycle)][p], cycle[(k + 1) % len(cycle)][r])
                    nxt = movers[k + 1]
                    prof[(pre, post, nxt)] += 1
                    if len(examples) < 12:
                        examples.append((ms, t, k, p, pre, post, nxt))
                checked += 1
                if checked >= 12:
                    break
            if checked >= 12:
                break
        print(f"\nfamily={ms}")
        print("top local transition profiles:")
        for key, count in prof.most_common(12):
            print(f"  {key}: {count}")
        print("examples:")
        for ex in examples[:8]:
            print(" ", ex)


if __name__ == "__main__":
    main()
