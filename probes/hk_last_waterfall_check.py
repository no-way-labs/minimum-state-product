#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import sys
from math import prod

ROOT = os.path.dirname(os.path.dirname(__file__))
GPT_SCRIPTS = os.path.join(ROOT, "gpt", "scripts")
sys.path.insert(0, GPT_SCRIPTS)

from p2_good_cycle_search import enumerate_good_cycles  # type: ignore


def local_five(t: int, n: int) -> set[int]:
    return {(t - 2) % n, (t - 1) % n, t, (t + 1) % n, (t + 2) % n}


def pivots(ms: tuple[int, ...]) -> list[int]:
    n = len(ms)
    return [i for i in range(n) if ms[(i - 1) % n] == 2 and ms[(i + 1) % n] == 2]


def hk_last_instances(movers: tuple[int, ...], ms: tuple[int, ...]) -> list[tuple[int, int]]:
    n = len(ms)
    hits = []
    for t in pivots(ms):
        outside = [idx for idx, mover in enumerate(movers) if mover not in local_five(t, n)]
        if outside and outside[-1] + 1 == len(movers):
            hits.append((t, outside[-1]))
    return hits


def subthreshold_multisets(n: int) -> list[tuple[int, ...]]:
    limit = 4 * (3 ** (n - 2))
    out: list[tuple[int, ...]] = []

    def rec(pos: int, last: int, cur_prod: int, cur: list[int]) -> None:
        if pos == n:
            if cur_prod < limit:
                out.append(tuple(cur))
            return
        maxv = limit // cur_prod
        for v in range(last, maxv + 1):
            if cur_prod * v >= limit:
                break
            cur.append(v)
            rec(pos + 1, v, cur_prod * v, cur)
            cur.pop()

    rec(0, 2, 1, [])
    return out


def pick_target(n: int) -> tuple[int, ...]:
    best = None
    best_hits = -1
    for ms in subthreshold_multisets(n):
        hits = 0
        for cycle, movers in enumerate_good_cycles(ms, max_cycles=50, time_limit=2.0):
            hits += len(hk_last_instances(movers, ms))
        if hits > best_hits:
            best_hits = hits
            best = ms
    assert best is not None
    print(f"picked target multiset={best} product={prod(best)} hk_last_hits={best_hits}")
    return best


def active(n: int, j: int, i: int) -> bool:
    d = (j + 2 * n - i) % (2 * n)
    return 1 <= d <= n


def waterfall_high_vals(cycle: tuple[tuple[int, ...], ...]) -> tuple[bool, tuple[int, ...] | None]:
    n = len(cycle[0])
    L = len(cycle)
    if L != 2 * n:
        return False, None
    vals = []
    for i in range(n):
        active_vals = {cycle[j][i] for j in range(L) if active(n, j, i)}
        inactive_vals = {cycle[j][i] for j in range(L) if not active(n, j, i)}
        if len(active_vals) != 1:
            return False, None
        if inactive_vals != {0}:
            return False, None
        (hv,) = tuple(active_vals)
        if hv == 0:
            return False, None
        vals.append(hv)
    return True, tuple(vals)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    args = parser.parse_args()

    ms = pick_target(args.n)
    chosen = None
    for cycle, movers in enumerate_good_cycles(ms, max_cycles=50, time_limit=5.0):
        hits = hk_last_instances(movers, ms)
        if hits:
            chosen = (cycle, movers, hits[0])
            break
    if chosen is None:
        print("no hk_last witness in budget")
        return
    cycle, movers, (t, k_out) = chosen
    ok, high_vals = waterfall_high_vals(cycle)
    print(f"chosen hk_last witness: pivot={t} k_out={k_out} len={len(cycle)}")
    print(f"movers={movers}")
    print(f"waterfall={ok}")
    if high_vals is not None:
        print(f"highVal={high_vals}")


if __name__ == "__main__":
    main()
