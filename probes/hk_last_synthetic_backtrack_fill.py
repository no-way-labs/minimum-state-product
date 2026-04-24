#!/usr/bin/env python3
from __future__ import annotations

from collections import deque


def neighbors(p: int, n: int) -> list[int]:
    return [(p - 1) % n, p, (p + 1) % n]


def shorter_path(i0: int, t: int, n: int) -> tuple[int, ...]:
    dr = (t - i0) % n
    dl = (i0 - t) % n
    if dr <= dl:
        return tuple((i0 + k) % n for k in range(dr + 1))
    return tuple((i0 - k) % n for k in range(dl + 1))


def main() -> None:
    n = 7
    i0 = 0
    t = 2
    path = shorter_path(i0, t, n)
    failures = []

    # walk words up to length 8, first hit t at the end
    q = deque([(i0, [i0])])
    while q:
        pos, walk = q.popleft()
        if len(walk) > 8:
            continue
        if len(walk) > 1 and pos == t:
            toggled = {p for p in range(n) if sum(1 for x in walk[:-1] if x == p) % 2 == 1}
            if not set(path).issubset(toggled):
                failures.append((tuple(walk), tuple(sorted(toggled))))
                if len(failures) >= 10:
                    break
            continue
        for nxt in neighbors(pos, n):
            # first hit t only at the end
            if nxt == t and len(walk) == 1:
                q.append((nxt, walk + [nxt]))
            elif nxt != t:
                q.append((nxt, walk + [nxt]))

    print(f"n={n} i0={i0} t={t} shorter_path={path}")
    print(f"failures_found={len(failures)}")
    for walk, toggled in failures[:10]:
        print(f"  walk={walk} toggled={toggled}")


if __name__ == "__main__":
    main()
