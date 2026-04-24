#!/usr/bin/env python3
from __future__ import annotations

import os
import sys
import time
from collections import Counter
from math import prod

ROOT = os.path.dirname(os.path.dirname(__file__))
GPT_SCRIPTS = os.path.join(ROOT, "gpt", "scripts")
sys.path.insert(0, GPT_SCRIPTS)

from p2_good_cycle_search import enumerate_good_cycles  # type: ignore


def pivots_with_binary_neighbors(state_counts: tuple[int, ...]) -> list[int]:
    n = len(state_counts)
    return [
        i for i in range(n)
        if state_counts[(i - 1) % n] == 2 and state_counts[(i + 1) % n] == 2
    ]


def local_five(t: int, n: int) -> set[int]:
    return {(t - 2) % n, (t - 1) % n, t % n, (t + 1) % n, (t + 2) % n}


def classify_hk_last(movers: tuple[int, ...], t: int, n: int) -> tuple[bool, int | None]:
    local = local_five(t, n)
    outside = [idx for idx, mover in enumerate(movers) if mover not in local]
    if not outside:
        return False, None
    k_out = outside[-1]
    return k_out + 1 == len(movers), k_out


def scan_candidate(state_counts: tuple[int, ...], max_cycles: int, time_limit: float) -> None:
    n = len(state_counts)
    pivots = pivots_with_binary_neighbors(state_counts)
    print(f"\nstate_counts={state_counts} pivots={pivots}")
    if not pivots:
      print("  no pivots with binary neighbors")
      return

    total_cycles = 0
    hk_last_hits = 0
    pair_counter: Counter[tuple[int, int, int]] = Counter()
    started = time.time()

    for cycle, movers in enumerate_good_cycles(state_counts, max_cycles=max_cycles, time_limit=time_limit):
        total_cycles += 1
        for t in pivots:
            has_hk_last, k_out = classify_hk_last(movers, t, n)
            if not has_hk_last:
                continue
            hk_last_hits += 1
            assert k_out is not None
            pair_counter[(t, movers[k_out], movers[0])] += 1

    print(f"  screened_cycles={total_cycles} elapsed={time.time() - started:.2f}s")
    print(f"  hk_last_hits={hk_last_hits}")
    if pair_counter:
        print("  (pivot, mover[k_out], mover[0]) frequencies:")
        for key, count in pair_counter.most_common():
            print(f"    {key}: {count}")


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


def scan_all_multisets(n: int, max_cycles: int, time_limit: float) -> None:
    multisets = subthreshold_multisets(n)
    print(f"\n=== n={n} sub-threshold multisets: {len(multisets)} ===")
    total_screened = 0
    total_hits = 0
    any_pairs: Counter[tuple[int, int, int]] = Counter()

    for idx, state_counts in enumerate(multisets, start=1):
        pivots = pivots_with_binary_neighbors(state_counts)
        if not pivots:
            continue
        print(f"[{idx}/{len(multisets)}] state_counts={state_counts} product={prod(state_counts)} pivots={pivots}")
        started = time.time()
        screened = 0
        hits = 0
        pairs: Counter[tuple[int, int, int]] = Counter()
        for cycle, movers in enumerate_good_cycles(state_counts, max_cycles=max_cycles, time_limit=time_limit):
            screened += 1
            for t in pivots:
                has_hk_last, k_out = classify_hk_last(movers, t, len(state_counts))
                if not has_hk_last:
                    continue
                hits += 1
                assert k_out is not None
                pairs[(t, movers[k_out], movers[0])] += 1
                any_pairs[(t, movers[k_out], movers[0])] += 1
        total_screened += screened
        total_hits += hits
        print(f"  screened_cycles={screened} elapsed={time.time() - started:.2f}s hk_last_hits={hits}")
        if pairs:
            for key, count in pairs.most_common():
                print(f"    {key}: {count}")

    print(f"\nSUMMARY n={n}: screened_cycles={total_screened} hk_last_hits={total_hits}")
    if any_pairs:
        print("aggregate (pivot, mover[k_out], mover[0]) frequencies:")
        for key, count in any_pairs.most_common():
            print(f"  {key}: {count}")


def main() -> None:
    print("hk_last scan over all sub-threshold multisets")
    for n in [5, 6, 7, 8, 9]:
        scan_all_multisets(n, max_cycles=50, time_limit=2.0)


if __name__ == "__main__":
    main()
