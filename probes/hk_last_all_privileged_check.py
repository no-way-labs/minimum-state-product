#!/usr/bin/env python3
from __future__ import annotations

import os
import sys

ROOT = os.path.dirname(os.path.dirname(__file__))
GPT_SCRIPTS = os.path.join(ROOT, "gpt", "scripts")
sys.path.insert(0, GPT_SCRIPTS)

from p2_good_cycle_search import enumerate_good_cycles  # type: ignore
from p2_cycle_screen import forced_rule_map  # type: ignore
from p2_completion_search import screening_data  # type: ignore


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


def is_forward_sweep(movers: tuple[int, ...], n: int) -> bool:
    return all(movers[k] == (k % n) for k in range(len(movers)))


def is_reverse_sweep(movers: tuple[int, ...], n: int) -> bool:
    return all(movers[k] == ((-k) % n) for k in range(len(movers)))


def main() -> None:
    n = 7
    ms = (2,) * n
    data = screening_data(ms)
    seen = 0
    for cycle, movers in enumerate_good_cycles(ms, max_cycles=80, time_limit=8.0):
        hits = hk_last_instances(movers, n, pivots(ms))
        if not hits:
            continue
        if is_forward_sweep(movers, n) or is_reverse_sweep(movers, n):
            continue
        seen += 1
        fm = forced_rule_map(cycle, movers)
        cycle_set = frozenset(cycle)
        all_forced = 0
        max_forced = -1
        argmax = None
        for idx, cfg in enumerate(data.configs):
            if cfg in cycle_set:
                continue
            forced_priv = 0
            for proc, key in enumerate(data.config_keys[idx]):
                out = fm.get(key)
                if out is not None and out != cfg[proc]:
                    forced_priv += 1
            if forced_priv == n:
                all_forced += 1
            if forced_priv > max_forced:
                max_forced = forced_priv
                argmax = cfg
        print(f"\n=== non-sweep witness {seen} ===")
        print(f"movers={movers}")
        print(f"hits={hits}")
        print(f"num_all_forced={all_forced}")
        print(f"max_forced={max_forced} at cfg={argmax}")
        if seen >= 5:
            break


if __name__ == "__main__":
    main()
