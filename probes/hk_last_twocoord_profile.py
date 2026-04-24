#!/usr/bin/env python3
from __future__ import annotations

import os
import sys
from collections import Counter, defaultdict

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
    both_changed = 0
    mover_profiles = Counter()
    sample = []
    for cycle, movers in enumerate_good_cycles(ms, max_cycles=80, time_limit=8.0):
        hits = hk_last_instances(movers, n, pivots(ms))
        if not hits:
            continue
        i0 = movers[0]
        c0 = cycle[0]
        for t, k_out in hits:
            count += 1
            local_counter = Counter()
            for j, cfg in enumerate(cycle):
                di0 = cfg[i0] != c0[i0]
                dt = cfg[t] != c0[t]
                local_counter[(di0, dt)] += 1
                if di0 and dt:
                    both_changed += 1
                    if len(sample) < 10:
                        sample.append((movers, t, j, cfg))
                mover_profiles[(movers[j], di0, dt)] += 1
            print(f"cycle#{count} i0={i0} t={t} profile={dict(local_counter)}")
            if count >= 10:
                break
        if count >= 10:
            break
    print(f"\nprofiles_checked={count} both_changed_hits={both_changed}")
    print("top mover profiles:")
    for item, c in mover_profiles.most_common(20):
        print(f"  {item}: {c}")
    if sample:
        print("samples with both changed:")
        for s in sample:
            print(" ", s)


if __name__ == "__main__":
    main()
