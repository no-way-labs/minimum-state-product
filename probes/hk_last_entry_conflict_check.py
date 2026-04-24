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


def has_entry_conflict(cycle, movers):
    n = len(cycle[0])
    for s, cfg_s in enumerate(cycle):
        p = movers[s]
        ls = cfg_s[(p - 1) % n]
        ss = cfg_s[p]
        rs = cfg_s[(p + 1) % n]
        for j, cfg_j in enumerate(cycle):
            if movers[j] == p:
                continue
            if cfg_j[(p - 1) % n] == ls and cfg_j[p] == ss and cfg_j[(p + 1) % n] == rs:
                return True, (s, j, p, (ls, ss, rs))
    return False, None


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
        checked = 0
        ec_hits = 0
        sample = None
        for cycle, movers in enumerate_good_cycles(ms, max_cycles=30, time_limit=8.0):
            if not hk_last_instances(movers, n, pivots(ms)):
                continue
            checked += 1
            has_ec, witness = has_entry_conflict(cycle, movers)
            if has_ec:
                ec_hits += 1
                if sample is None:
                    sample = (movers, witness)
        print(f"\nfamily={ms}")
        print(f"hk_last_cycles_checked={checked} entry_conflict_hits={ec_hits}")
        if sample:
            print(f"sample={sample}")


if __name__ == "__main__":
    main()
