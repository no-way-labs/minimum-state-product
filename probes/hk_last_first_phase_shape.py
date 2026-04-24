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
        (2, 2, 2, 2, 2, 2, 2, 22),
        (2,) * 9,
    ]
    for ms in families:
        n = len(ms)
        seen = 0
        print(f"\nfamily={ms}")
        for cycle, movers in enumerate_good_cycles(ms, max_cycles=20, time_limit=6.0):
            hits = hk_last_instances(movers, n, pivots(ms))
            if not hits:
                continue
            i0 = movers[0]
            for t, _ in hits[:2]:
                t_positions = [idx for idx, mv in enumerate(movers) if mv == t]
                if not t_positions:
                    continue
                k_next = min(idx for idx in t_positions if idx > 0)
                k_prev = max(t_positions)
                phase = movers[:k_next + 1]
                tail = phase[max(0, len(phase) - 4):]
                print(f"  i0={i0} t={t} prev_t={k_prev} next_t={k_next} phase={phase} tail={tail}")
                seen += 1
                if seen >= 8:
                    break
            if seen >= 8:
                break


if __name__ == "__main__":
    main()
