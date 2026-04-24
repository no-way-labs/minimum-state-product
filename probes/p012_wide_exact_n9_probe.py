#!/usr/bin/env python3
"""Probe the broadened exact P1:(0,1,2) source/destination family.

This keeps the exact 9-coordinate signature

  (c0, c1, c2, c3, c4, cN4, cN3, cN2, cN1)

and frees cN4, unlike the current P012ExactScratch source theorem.

It computes the actual TP-preserving bad-step closure from the broadened exact
source/destination starts, projects to the exact signature, and reports:

- projected state count
- whether the projected graph is acyclic
- max projected rank
- start-rank distributions
"""

from __future__ import annotations

from collections import Counter, defaultdict, deque
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


def exact_sig(c: tuple[int, ...]) -> tuple[int, ...]:
    n = len(c)
    return (c[0], c[1], c[2], c[3], c[4], c[n - 4], c[n - 3], c[n - 2], c[n - 1])


def exact_sig_idx(s: tuple[int, ...]) -> int:
    c0, c1, c2, c3, c4, cN4, cN3, cN2, cN1 = s
    return ((((((((c0 * 3 + c1) * 3 + c2) * 3 + c3) * 3 + c4) * 3 + cN4) * 3 + cN3) * 3 + cN2) * 2 + cN1)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=9,
                        help="Ring size n (default: 9).")
    parser.add_argument("--emit-ranks", action="store_true",
                        help="Print rank buckets as exact signature indices.")
    args = parser.parse_args()

    n = args.n
    if n < 9:
        raise SystemExit("n must be at least 9")

    moduli = [3] * n
    moduli[0] = 2
    moduli[-1] = 2
    all_states = list(product(*[range(m) for m in moduli]))
    good = set(good_cycle(n))

    starts: list[tuple[int, ...]] = []
    for c3, c4, cN4 in product(range(3), repeat=3):
        src = [0] * n
        src[0], src[1], src[2] = 0, 1, 2
        src[3], src[4] = c3, c4
        src[n - 4], src[n - 3], src[n - 2], src[n - 1] = cN4, 1, 0, 1
        starts.append(tuple(src))

        dst = [0] * n
        dst[0], dst[1], dst[2] = 0, 0, 2
        dst[3], dst[4] = c3, c4
        dst[n - 4], dst[n - 3], dst[n - 2], dst[n - 1] = cN4, 1, 0, 1
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

    sigs = sorted({exact_sig(c) for c in reach})
    edges: dict[tuple[int, ...], set[tuple[int, ...]]] = defaultdict(set)
    for c in reach:
        inv = tp_inv(c)
        s = exact_sig(c)
        for i in range(n):
            if not privileged(c, i):
                continue
            d = move(c, i)
            if d in good:
                continue
            if tp_inv(d) == inv:
                edges[s].add(exact_sig(d))

    white, gray, black = 0, 1, 2
    color = {s: white for s in sigs}
    rank: dict[tuple[int, ...], int] = {}
    cycle = False

    def dfs(s: tuple[int, ...]) -> int:
        nonlocal cycle
        color[s] = gray
        best = 0
        for t in edges[s]:
            if t == s:
                continue
            if color[t] == gray:
                cycle = True
                continue
            if color[t] == white:
                dfs(t)
            best = max(best, rank.get(t, 0) + 1)
        color[s] = black
        rank[s] = best
        return best

    for s in sigs:
        if color[s] == white:
            dfs(s)

    print(f"projected states: {len(sigs)}")
    print(f"acyclic: {not cycle}")
    print(f"max rank: {max(rank.values()) if rank else 0}")
    print("rank counts:", sorted(Counter(rank.values()).items()))

    src_counter = Counter()
    dst_counter = Counter()
    for c3, c4, cN4 in product(range(3), repeat=3):
        src = [0] * n
        src[0], src[1], src[2] = 0, 1, 2
        src[3], src[4] = c3, c4
        src[n - 4], src[n - 3], src[n - 2], src[n - 1] = cN4, 1, 0, 1
        src = tuple(src)

        dst = [0] * n
        dst[0], dst[1], dst[2] = 0, 0, 2
        dst[3], dst[4] = c3, c4
        dst[n - 4], dst[n - 3], dst[n - 2], dst[n - 1] = cN4, 1, 0, 1
        dst = tuple(dst)
        if src in rank:
            src_counter[(cN4, rank[src])] += 1
        if dst in rank:
            dst_counter[(cN4, rank[dst])] += 1
    print("source start ranks by (cN4, rank):", src_counter)
    print("dest start ranks by (cN4, rank):", dst_counter)
    gaps = Counter()
    for c3, c4, cN4 in product(range(3), repeat=3):
        src = (0, 1, 2, c3, c4, cN4, 1, 0, 1)
        dst = (0, 0, 2, c3, c4, cN4, 1, 0, 1)
        gaps[rank[src] - rank[dst]] += 1
    print("source-dest rank gaps:", gaps)

    if args.emit_ranks:
        buckets: dict[int, list[int]] = defaultdict(list)
        for s, r in rank.items():
            buckets[r].append(exact_sig_idx(s))
        for r in sorted(buckets):
            vals = sorted(buckets[r])
            print(f"rank {r}: {vals}")


if __name__ == "__main__":
    main()
