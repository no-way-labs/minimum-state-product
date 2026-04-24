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


def nonadjacent(pair, n):
    a, b = pair
    return b not in {(a - 1) % n, a, (a + 1) % n}


def main() -> None:
    families = [
        (2,) * 7,
        (2, 2, 2, 2, 2, 10),
        (2, 2, 2, 2, 2, 2, 14),
        (2,) * 9,
    ]
    for ms in families:
        n = len(ms)
        checked = 0
        seen_exact = 0
        dist2_pairs = Counter()
        for cycle, movers in enumerate_good_cycles(ms, max_cycles=30, time_limit=8.0):
            hits = hk_last_instances(movers, n, pivots(ms))
            if not hits:
                continue
            i0 = movers[0]
            c0 = cycle[0]
            for t, _ in hits:
                target = tuple(sorted((i0, t)))
                checked += 1
                for j, cfg in enumerate(cycle):
                    diff = tuple(i for i, (a, b) in enumerate(zip(cfg, c0)) if a != b)
                    if len(diff) == 2:
                        dist2_pairs[diff] += 1
                        if tuple(sorted(diff)) == target:
                            seen_exact += 1
                if checked >= 30:
                    break
            if checked >= 30:
                break
        print(f"\nfamily={ms}")
        print(f"profiles_checked={checked}")
        print(f"exact_cFlip2_support_hits={seen_exact}")
        print("top distance-2 supports:")
        for pair, count in dist2_pairs.most_common(12):
            tag = " nonadj" if nonadjacent(pair, n) else ""
            print(f"  {pair}: {count}{tag}")


if __name__ == "__main__":
    main()
