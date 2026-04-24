#!/usr/bin/env python3
"""Summarize adjacent ring words by 0-anchored sweep blocks and local wiggles."""

from __future__ import annotations

import argparse


def parse_int_tuple(text: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in text.split(",") if part.strip())


def split_blocks(movers: tuple[int, ...]) -> list[tuple[int, ...]]:
    blocks: list[tuple[int, ...]] = []
    current = [movers[0]]
    for mover in movers[1:]:
        current.append(mover)
        if mover == 0:
            blocks.append(tuple(current))
            current = [0]
    if len(current) > 1:
        blocks.append(tuple(current))
    return blocks


def step_kind(left: int, right: int, n: int) -> str:
    if (right - left) % n == 1:
        return "F"
    if (left - right) % n == 1:
        return "B"
    return "?"


def block_signature(block: tuple[int, ...], n: int) -> str:
    steps = [step_kind(block[i], block[i + 1], n) for i in range(len(block) - 1)]
    forward = steps.count("F")
    backward = steps.count("B")
    orientation = "F" if forward >= backward else "R"
    wiggles: list[str] = []
    i = 1
    while i < len(block) - 1:
        a = block[i - 1]
        b = block[i]
        c = block[i + 1]
        if a == c and a != b:
            low = min(a, b)
            high = max(a, b)
            wiggles.append(f"{low}{high}{low}")
            i += 2
            continue
        i += 1
    return f"{orientation}[{','.join(wiggles)}]"


def word_signature(movers: tuple[int, ...], n: int) -> str:
    return " | ".join(block_signature(block, n) for block in split_blocks(movers))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--movers", required=True)
    parser.add_argument("--n", type=int, default=9)
    args = parser.parse_args()

    movers = parse_int_tuple(args.movers)
    print(f"blocks={split_blocks(movers)}")
    print(f"signature={word_signature(movers, args.n)}")


if __name__ == "__main__":
    main()
