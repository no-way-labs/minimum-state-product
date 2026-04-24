#!/usr/bin/env python3
"""Probe the exceptional destination family `002…22101`.

This script reuses the TP-bad-step model from `p012_full_exact_gap_probe.py`
and focuses on the actual TP-bad closure from the exceptional destination start

  0,0,2,2,...,2,1,0,1

for a given `n >= 9`.

It reports:
- closure size
- Lean `cup2Fc` distribution
- reachable middle-strip count
- whether the middle strips are exactly the language `1^a 0^b 2^c` with `c >= 1`
- the projected `(a,b,c)` move automaton
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict, deque
import importlib.util
from pathlib import Path


def load_p012_probe():
    path = Path(__file__).with_name("p012_full_exact_gap_probe.py")
    spec = importlib.util.spec_from_file_location("p012probe", path)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


mod = load_p012_probe()


def closure_from(start: tuple[int, ...]) -> set[tuple[int, ...]]:
    n = len(start)
    good = set(mod.good_cycle(n))
    reach = {start}
    q: deque[tuple[int, ...]] = deque([start])
    while q:
        c = q.popleft()
        inv = mod.tp_inv(c)
        for i in range(n):
            if not mod.privileged(c, i):
                continue
            d = mod.move(c, i)
            if d in good:
                continue
            if mod.tp_inv(d) != inv:
                continue
            if d not in reach:
                reach.add(d)
                q.append(d)
    return reach


def lean_fc(c: tuple[int, ...]) -> int:
    n = len(c)
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def abc(mid: tuple[int, ...]) -> tuple[int, int, int]:
    a = 0
    while a < len(mid) and mid[a] == 1:
        a += 1
    b = 0
    while a + b < len(mid) and mid[a + b] == 0:
        b += 1
    c = len(mid) - a - b
    return (a, b, c)


def is_102_language(mid: tuple[int, ...]) -> bool:
    seen_zero = False
    seen_two = False
    for x in mid:
        if not seen_zero and not seen_two:
            if x == 1:
                continue
            if x == 0:
                seen_zero = True
                continue
            if x == 2:
                seen_two = True
                continue
            return False
        if seen_zero and not seen_two:
            if x == 0:
                continue
            if x == 2:
                seen_two = True
                continue
            return False
        if x != 2:
            return False
    return seen_two


def start_state(n: int) -> tuple[int, ...]:
    if n < 9:
        raise ValueError("n must be at least 9")
    return tuple([0, 0, 2] + [2] * (n - 6) + [1, 0, 1])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True, help="Ring size n >= 9.")
    args = parser.parse_args()

    n = args.n
    start = start_state(n)
    reach = closure_from(start)

    fcs = Counter(lean_fc(c) for c in reach)
    mids = {c[3 : n - 3] for c in reach}
    bad_mids = sorted(m for m in mids if not is_102_language(m))

    abc_transitions: dict[tuple[int, int, int], set[tuple[int, tuple[int, int, int]]]] = defaultdict(set)
    for c in reach:
        inv = mod.tp_inv(c)
        key = abc(c[3 : n - 3])
        for i in range(n):
            if not mod.privileged(c, i):
                continue
            d = mod.move(c, i)
            if d in reach and mod.tp_inv(d) == inv:
                abc_transitions[key].add((i, abc(d[3 : n - 3])))

    print("start:", start)
    print("closure size:", len(reach))
    print("lean_fc distribution:", dict(sorted(fcs.items())))
    print("middle-strip count:", len(mids))
    print("middle language exact:", len(bad_mids) == 0)
    if bad_mids:
        print("bad middle strips:")
        for mid in bad_mids:
            print(" ", mid)
    else:
        print("middle-strip counts match 1^a 0^b 2^c")

    print("abc automaton:")
    for key in sorted(abc_transitions):
        print(f"  {key}: {sorted(abc_transitions[key])}")


if __name__ == "__main__":
    main()
