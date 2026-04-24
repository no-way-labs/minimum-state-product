#!/usr/bin/env python3
"""Probe the full exact P1:(0,1,2) source/destination family.

For a given n >= 9, define:

- source starts: c0=0, c1=1, c2=2, c[n-3]=1, c[n-2]=0, c[n-1]=1
- destination starts: same, but c1=0
- every other site is free in {0,1,2}

This script computes the actual TP-preserving bad-step closure from those starts,
builds the actual reachable TP graph, and reports whether the source/destination
start-rank gap is uniform.
"""

from __future__ import annotations

from collections import Counter, deque
from itertools import product
import argparse


def t_bot(l: int, s: int, r: int) -> int:
    return {
        (0, 0, 0): 1,
        (0, 0, 1): 1,
        (0, 0, 2): 0,
        (0, 1, 0): 1,
        (0, 1, 1): 1,
        (0, 1, 2): 1,
        (1, 0, 0): 0,
        (1, 0, 1): 1,
        (1, 0, 2): 0,
        (1, 1, 0): 0,
        (1, 1, 1): 1,
        (1, 1, 2): 0,
    }.get((l, s, r), 0)


def t_low(l: int, s: int, r: int) -> int:
    return {
        (0, 0, 0): 0,
        (0, 0, 1): 0,
        (0, 0, 2): 0,
        (0, 1, 0): 0,
        (0, 1, 1): 1,
        (0, 1, 2): 0,
        (0, 2, 0): 0,
        (0, 2, 1): 2,
        (0, 2, 2): 0,
        (1, 0, 0): 1,
        (1, 0, 1): 1,
        (1, 0, 2): 1,
        (1, 1, 0): 1,
        (1, 1, 1): 1,
        (1, 1, 2): 2,
        (1, 2, 0): 0,
        (1, 2, 1): 1,
        (1, 2, 2): 2,
    }.get((l, s, r), 0)


def t_mid(l: int, s: int, r: int) -> int:
    return {
        (0, 0, 0): 0,
        (0, 0, 1): 0,
        (0, 0, 2): 0,
        (0, 1, 0): 0,
        (0, 1, 1): 1,
        (0, 1, 2): 0,
        (0, 2, 0): 0,
        (0, 2, 1): 2,
        (0, 2, 2): 0,
        (1, 0, 0): 1,
        (1, 0, 1): 1,
        (1, 0, 2): 1,
        (1, 1, 0): 1,
        (1, 1, 1): 1,
        (1, 1, 2): 2,
        (1, 2, 0): 0,
        (1, 2, 1): 1,
        (1, 2, 2): 2,
        (2, 0, 0): 0,
        (2, 0, 1): 0,
        (2, 0, 2): 2,
        (2, 1, 0): 1,
        (2, 1, 1): 0,
        (2, 1, 2): 2,
        (2, 2, 0): 0,
        (2, 2, 1): 2,
        (2, 2, 2): 2,
    }.get((l, s, r), 0)


def t_high(l: int, s: int, r: int) -> int:
    return {
        (0, 0, 0): 0,
        (0, 0, 1): 0,
        (0, 1, 0): 0,
        (0, 1, 1): 0,
        (0, 2, 0): 0,
        (0, 2, 1): 0,
        (1, 0, 0): 1,
        (1, 0, 1): 1,
        (1, 1, 0): 1,
        (1, 1, 1): 2,
        (1, 2, 0): 0,
        (1, 2, 1): 2,
        (2, 0, 0): 0,
        (2, 0, 1): 2,
        (2, 1, 0): 0,
        (2, 1, 1): 2,
        (2, 2, 0): 2,
        (2, 2, 1): 2,
    }.get((l, s, r), 0)


def t_top(l: int, s: int, r: int) -> int:
    return {
        (0, 0, 0): 0,
        (0, 0, 1): 0,
        (0, 1, 0): 0,
        (0, 1, 1): 0,
        (1, 0, 0): 0,
        (1, 0, 1): 1,
        (1, 1, 0): 1,
        (1, 1, 1): 1,
        (2, 0, 0): 1,
        (2, 0, 1): 1,
        (2, 1, 0): 1,
        (2, 1, 1): 1,
    }.get((l, s, r), 0)


def transition(c: tuple[int, ...], i: int) -> int:
    n = len(c)
    l, s, r = c[(i - 1) % n], c[i], c[(i + 1) % n]
    if i == 0:
        return t_bot(l, s, r)
    if i == 1:
        return t_low(l, s, r)
    if i == n - 2:
        return t_high(l, s, r)
    if i == n - 1:
        return t_top(l, s, r)
    return t_mid(l, s, r)


def privileged(c: tuple[int, ...], i: int) -> bool:
    return transition(c, i) != c[i]


def move(c: tuple[int, ...], i: int) -> tuple[int, ...]:
    out = list(c)
    out[i] = transition(c, i)
    return tuple(out)


def exp2_bit(n: int, j: int, a: int, b: int) -> int:
    return 1 if 2 <= j and j + 2 < n and a == 2 and b != 2 else 0


def int21_bit(n: int, j: int, a: int, b: int) -> int:
    return 1 if 2 <= j and j + 2 < n and a == 2 and b == 1 else 0


def tp_inv(c: tuple[int, ...]) -> tuple[int, int, int]:
    n = len(c)
    exp = [exp2_bit(n, j, c[j], c[(j + 1) % n]) for j in range(n)]
    int21 = [int21_bit(n, j, c[j], c[(j + 1) % n]) for j in range(n)]
    return (sum(exp), sum(int21), sum(j * exp[j] for j in range(n)))


def good_cycle(n: int) -> list[tuple[int, ...]]:
    c = tuple([0] * n)
    seen: list[tuple[int, ...]] = []
    while c not in seen:
        seen.append(c)
        movers = [i for i in range(n) if privileged(c, i)]
        if len(movers) != 1:
            raise RuntimeError(f"non-unique privileged config {c}: {movers}")
        c = move(c, movers[0])
    return seen


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True, help="Ring size n >= 9.")
    args = parser.parse_args()

    n = args.n
    if n < 9:
        raise SystemExit("n must be at least 9")

    good = set(good_cycle(n))
    free_positions = list(range(3, n - 3))

    starts: list[tuple[int, ...]] = []
    for vals in product(range(3), repeat=len(free_positions)):
        src = [0] * n
        dst = [0] * n
        src[0:3] = [0, 1, 2]
        dst[0:3] = [0, 0, 2]
        src[n - 3:n] = [1, 0, 1]
        dst[n - 3:n] = [1, 0, 1]
        for pos, val in zip(free_positions, vals):
            src[pos] = val
            dst[pos] = val
        starts.append(tuple(src))
        starts.append(tuple(dst))
    starts = [c for c in starts if c not in good]

    reach = set(starts)
    q = deque(starts)
    while q:
        c = q.popleft()
        inv = tp_inv(c)
        for i in range(n):
            if not privileged(c, i):
                continue
            d = move(c, i)
            if d in good:
                continue
            if tp_inv(d) != inv:
                continue
            if d not in reach:
                reach.add(d)
                q.append(d)

    adj = {c: [] for c in reach}
    for c in reach:
        inv = tp_inv(c)
        for i in range(n):
            if not privileged(c, i):
                continue
            d = move(c, i)
            if d in reach and tp_inv(d) == inv:
                adj[c].append(d)

    white, gray, black = 0, 1, 2
    color = {c: white for c in reach}
    rank: dict[tuple[int, ...], int] = {}
    cycle = False

    def dfs(c: tuple[int, ...]) -> int:
        nonlocal cycle
        color[c] = gray
        best = 0
        for d in adj[c]:
            if color[d] == gray:
                cycle = True
                continue
            if color[d] == white:
                dfs(d)
            best = max(best, rank.get(d, 0) + 1)
        color[c] = black
        rank[c] = best
        return best

    for c in list(reach):
        if color[c] == white:
            dfs(c)

    gaps = Counter()
    ladder_step0 = Counter()
    ladder_step1 = Counter()
    ladder_step2 = Counter()
    ladder_step3 = Counter()
    ladder_drop0 = Counter()
    ladder_drop1 = Counter()
    ladder_drop2 = Counter()
    ladder_drop3 = Counter()
    for vals in product(range(3), repeat=len(free_positions)):
        src = [0] * n
        dst = [0] * n
        src[0:3] = [0, 1, 2]
        dst[0:3] = [0, 0, 2]
        src[n - 3:n] = [1, 0, 1]
        dst[n - 3:n] = [1, 0, 1]
        for pos, val in zip(free_positions, vals):
            src[pos] = val
            dst[pos] = val
        src_t = tuple(src)
        dst_t = tuple(dst)
        gaps[rank[src_t] - rank[dst_t]] += 1

        def tp_bad_step(a: tuple[int, ...], i: int, inv) -> tuple[bool, tuple[int, ...]]:
            b = move(a, i)
            ok = privileged(a, i) and (b not in good) and (tp_inv(b) == inv)
            return ok, b

        inv_src = tp_inv(src_t)
        ok0, s0 = tp_bad_step(src_t, 0, inv_src)
        ladder_step0[ok0] += 1
        if ok0:
            ladder_drop0[rank[src_t] - rank[s0]] += 1

        ok1, s1 = tp_bad_step(s0, 1, inv_src) if ok0 else (False, src_t)
        ladder_step1[ok1] += 1
        if ok1:
            ladder_drop1[rank[s0] - rank[s1]] += 1

        ok2, s2 = tp_bad_step(s1, 0, inv_src) if ok1 else (False, src_t)
        ladder_step2[ok2] += 1
        if ok2:
            ladder_drop2[rank[s1] - rank[s2]] += 1

        ok3, s3 = tp_bad_step(s2, 1, inv_src) if ok2 else (False, src_t)
        ladder_step3[ok3] += 1
        if ok3:
            ladder_drop3[rank[s2] - rank[s3]] += 1

    print(f"n: {n}")
    print(f"free positions: {len(free_positions)}")
    print(f"reachable actual states: {len(reach)}")
    print(f"acyclic: {not cycle}")
    print(f"max rank: {max(rank.values()) if rank else 0}")
    print(f"gap counts: {gaps}")
    print(f"ladder step0 ok counts: {ladder_step0}, rank drops: {ladder_drop0}")
    print(f"ladder step1 ok counts: {ladder_step1}, rank drops: {ladder_drop1}")
    print(f"ladder step2 ok counts: {ladder_step2}, rank drops: {ladder_drop2}")
    print(f"ladder step3 ok counts: {ladder_step3}, rank drops: {ladder_drop3}")


if __name__ == "__main__":
    main()
