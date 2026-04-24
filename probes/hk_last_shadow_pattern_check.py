#!/usr/bin/env python3
from __future__ import annotations

import argparse


def shadow_shift(n: int, i: int) -> int:
    if i <= n - 5:
        return n - 2 - i
    if i == n - 4:
        return 0
    if i == n - 3:
        return n + 1
    if i == n - 2:
        return 2
    return 2 * n - 1


def shadow_perm(n: int, k: int) -> int:
    if k == 0:
        return n - 4
    if k == 1:
        return n - 1
    if k == 2:
        return 0
    if k <= n - 3:
        return k - 2
    if k == n - 2:
        return n - 2
    return n - 3


def shadow_active(n: int, j: int, d: int) -> bool:
    idx = (j + d) % (2 * n)
    return 1 <= idx <= n


def shadow_cfg(n: int, k: int, shadow_off: int) -> tuple[int, ...]:
    return tuple(
        1 if shadow_active(n, (k + shadow_off) % (2 * n), shadow_shift(n, i)) else 0
        for i in range(n)
    )


def staircase_patterns() -> set[tuple[int, int, int, int]]:
    return {
        (0, 0, 0, 0),
        (0, 0, 0, 1),
        (0, 0, 1, 1),
        (0, 1, 1, 1),
        (1, 0, 0, 0),
        (1, 1, 0, 0),
        (1, 1, 1, 0),
        (1, 1, 1, 1),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=9)
    parser.add_argument("--i0", type=int, default=0)
    args = parser.parse_args()

    n = args.n
    i0 = args.i0 % n

    shadow_off_candidates = [k for k in range(n) if shadow_perm(n, k) == i0]
    if not shadow_off_candidates:
        raise SystemExit(f"no shadowOff found for n={n}, i0={i0}")
    shadow_off = shadow_off_candidates[0]

    coords = (i0, (i0 + n - 4) % n, (i0 + n - 3) % n, (i0 + n - 2) % n)
    patterns = {
        tuple(shadow_cfg(n, k, shadow_off)[i] for i in coords)
        for k in range(2 * n)
    }
    stair = staircase_patterns()
    print(f"n={n} i0={i0} shadowOff={shadow_off} coords={coords}")
    print(f"shadow_patterns={sorted(patterns)}")
    print(f"count={len(patterns)}")
    print(f"all_non_staircase={patterns.isdisjoint(stair)}")
    print(f"intersection_with_staircase={sorted(patterns & stair)}")


if __name__ == "__main__":
    main()
