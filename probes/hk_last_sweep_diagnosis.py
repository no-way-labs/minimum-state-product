#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import sys
from collections import Counter
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
            best = ms
            best_hits = hits
    assert best is not None
    print(f"picked target multiset={best} product={prod(best)} hk_last_hits={best_hits}")
    return best


def is_double_sweep(movers: tuple[int, ...], n: int) -> bool:
    if len(movers) != 2 * n:
        return False
    base = list(range(n))
    rots = [tuple(base[r:] + base[:r] + base[r:] + base[:r]) for r in range(n)]
    return movers in rots


def fire_count_vector(movers: tuple[int, ...], n: int) -> tuple[int, ...]:
    counts = [0] * n
    for m in movers:
        counts[m] += 1
    return tuple(counts)


def only_zero_one(cycle: tuple[tuple[int, ...], ...]) -> bool:
    return all(v in (0, 1) for cfg in cycle for v in cfg)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, nargs="+", default=[6, 7, 8])
    args = parser.parse_args()

    for n in args.n:
        ms = pick_target(n)
        hits = 0
        sweep_hits = 0
        binary_hits = 0
        firecount_counter: Counter[tuple[int, ...]] = Counter()
        first_half_counter: Counter[tuple[int, ...]] = Counter()

        for cycle, movers in enumerate_good_cycles(ms, max_cycles=50, time_limit=5.0):
            hk_hits = hk_last_instances(movers, ms)
            if not hk_hits:
                continue
            for _t, _k_out in hk_hits:
                hits += 1
                if is_double_sweep(movers, n):
                    sweep_hits += 1
                if only_zero_one(cycle):
                    binary_hits += 1
                firecount_counter[fire_count_vector(movers, n)] += 1
                first_half_counter[movers[:n]] += 1

        print(f"\n=== n={n} ===")
        print(f"target state_counts={ms}")
        print(f"hk_last_instances={hits}")
        print(f"double_sweep_hits={sweep_hits}")
        print(f"zero_one_only_hits={binary_hits}")
        print("fireCount vectors:")
        for vec, count in firecount_counter.most_common():
            print(f"  {vec}: {count}")
        print("first-half mover words:")
        for word, count in first_half_counter.most_common(5):
            print(f"  {word}: {count}")


if __name__ == "__main__":
    main()
