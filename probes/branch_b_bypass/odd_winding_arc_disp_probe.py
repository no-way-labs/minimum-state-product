#!/usr/bin/env python3
"""
odd_winding_arc_disp_probe.py

Probe odd-winding EC-free residual cycles for the displacement between two
consecutive fires of a binary processor.

Default family:

    ms = (2,3,3,2,3,3,2,3,3).

The residual filter matches the current odd-winding research packet:

1. valid good cycle at cycle length sum(ms),
2. odd winding,
3. no provider interval, and
4. no entry conflict anywhere.

For each residual cycle, the script picks the first binary processor in index
order with at least two firings, lets `a1 < a2` be its first consecutive firing
pair, and computes both:

    intervalDisplacement(a1, a2)     -- corrected return interval [a1, a2)
    intervalDisplacement(a1 + 1, a2) -- old open interval (diagnostic only)

The corrected return interval is the primary statistic: it is the interval used
by the Lean `ArcConfinement` layer and by the current M4 sub-case 3a/3b split.
"""

from __future__ import annotations

import argparse
from collections import Counter
from math import prod


DEFAULT_MS = (2, 3, 3, 2, 3, 3, 2, 3, 3)


def left(p: int, n: int) -> int:
    return (p - 1) % n


def right(p: int, n: int) -> int:
    return (p + 1) % n


def signed_step(curr: int, nxt: int, n: int) -> int:
    diff = (nxt - curr) % n
    if diff == 0:
        return 0
    if diff == 1:
        return 1
    if diff == n - 1:
        return -1
    raise ValueError(f"non-local step {curr}->{nxt}")


def total_displacement(word: tuple[int, ...], n: int) -> int:
    return sum(signed_step(word[k], word[(k + 1) % len(word)], n) for k in range(len(word)))


def winding_class(word: tuple[int, ...], n: int) -> str:
    cw = 0
    ccw = 0
    for k in range(len(word)):
        step = signed_step(word[k], word[(k + 1) % len(word)], n)
        if step == 1:
            cw += 1
        elif step == -1:
            ccw += 1
    if ccw == 0 and cw > 0:
        return "sweep-cw"
    if cw == 0 and ccw > 0:
        return "sweep-ccw"
    if cw == ccw:
        return "zw-cw0" if cw == 0 else "zw-cwpos"
    return "odd-winding"


def build_configs(word: tuple[int, ...], ms: tuple[int, ...]) -> list[tuple[int, ...]]:
    n = len(ms)
    cfg = [0] * n
    configs = [tuple(cfg)]
    for mover in word:
        cfg[mover] = (cfg[mover] + 1) % ms[mover]
        configs.append(tuple(cfg))
    return configs[:-1]


def canonicalize(word: tuple[int, ...]) -> tuple[int, ...]:
    best = word
    for i in range(len(word)):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


def fire_steps(word: tuple[int, ...], p: int) -> list[int]:
    return [k for k, mover in enumerate(word) if mover == p]


def has_provider_interval(word: tuple[int, ...], ms: tuple[int, ...]) -> bool:
    n = len(ms)
    cl = len(word)
    fc = [0] * n
    for mover in word:
        fc[mover] += 1
    for i in range(n):
        if fc[i] < 2:
            continue
        li = left(i, n)
        ri = right(i, n)
        if ms[li] != 2 and ms[ri] != 2:
            continue
        fires = fire_steps(word, i)
        for idx in range(len(fires)):
            a1 = fires[idx]
            a2 = fires[(idx + 1) % len(fires)]
            if a2 <= a1:
                a2 += cl
            if a2 - a1 < 2:
                continue
            lc = 0
            rc = 0
            for k_raw in range(a2 - 1, a1, -1):
                k = k_raw % cl
                mover = word[k]
                if mover == i:
                    continue
                if mover == li:
                    lc += 1
                if mover == ri:
                    rc += 1
                left_ok = (lc == 0) or (ms[li] == 2 and lc % 2 == 0 and lc >= 2)
                right_ok = (rc == 0) or (ms[ri] == 2 and rc % 2 == 0 and rc >= 2)
                if left_ok and right_ok and (lc > 0 or rc > 0):
                    return True
    return False


def has_any_ec(word: tuple[int, ...], configs: list[tuple[int, ...]], ms: tuple[int, ...]) -> bool:
    n = len(ms)
    for p in range(n):
        mover_ctx = set()
        nonmover_ctx = set()
        lp = left(p, n)
        rp = right(p, n)
        for k, mover in enumerate(word):
            ctx = (configs[k][lp], configs[k][p], configs[k][rp])
            if mover == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        if mover_ctx & nonmover_ctx:
            return True
    return False


def enumerate_cycles(ms: tuple[int, ...], cap: int = 500000) -> tuple[list[tuple[int, ...]], bool]:
    n = len(ms)
    cl = sum(ms)
    target_fc = list(ms)
    start_config = tuple([0] * n)
    out: list[tuple[int, ...]] = []

    def dfs(word: list[int], fc: list[int], config: tuple[int, ...]) -> None:
        if len(out) >= cap:
            return
        if len(word) == cl:
            last = word[-1]
            first = word[0]
            if first not in (left(last, n), last, right(last, n)):
                return
            if config != start_config or fc != target_fc:
                return
            cfg = [0] * n
            seen = {tuple(cfg)}
            for mover in word:
                cfg[mover] = (cfg[mover] + 1) % ms[mover]
                t = tuple(cfg)
                if t in seen and t != start_config:
                    return
                seen.add(t)
            out.append(tuple(word))
            return

        remaining = cl - len(word)
        needed = sum(max(0, target_fc[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return

        last = word[-1]
        for nxt in (left(last, n), last, right(last, n)):
            if fc[nxt] + 1 > target_fc[nxt]:
                continue
            new_config = list(config)
            new_config[nxt] = (new_config[nxt] + 1) % ms[nxt]
            word.append(nxt)
            fc[nxt] += 1
            dfs(word, fc, tuple(new_config))
            word.pop()
            fc[nxt] -= 1

    for start in range(n):
        fc = [0] * n
        fc[start] = 1
        cfg = [0] * n
        cfg[start] = (cfg[start] + 1) % ms[start]
        dfs([start], fc, tuple(cfg))

    return out, len(out) >= cap


def first_binary_arc_record(word: tuple[int, ...], ms: tuple[int, ...]) -> dict[str, object]:
    n = len(ms)
    cl = len(word)
    binary_procs = tuple(i for i, m in enumerate(ms) if m == 2)
    for b in binary_procs:
        fires = fire_steps(word, b)
        if len(fires) < 2:
            continue
        a1, a2 = fires[0], fires[1]
        open_arc_disp = sum(
            signed_step(word[k], word[(k + 1) % cl], n)
            for k in range(a1 + 1, a2)
        )
        return_disp = sum(
            signed_step(word[k], word[(k + 1) % cl], n)
            for k in range(a1, a2)
        )
        rec = {
            "b": b,
            "a1": a1,
            "a2": a2,
            "fire_count_b": len(fires),
            "open_arc_disp": open_arc_disp,
            "return_disp": return_disp,
            "word": list(word),
        }
        rec["open_k"] = open_arc_disp // n if open_arc_disp % n == 0 else None
        rec["return_k"] = return_disp // n if return_disp % n == 0 else None
        return rec
    raise ValueError("no binary with at least two firings found")


def filter_residual(cycles: list[tuple[int, ...]], ms: tuple[int, ...]) -> list[tuple[int, ...]]:
    n = len(ms)
    out = []
    for word in cycles:
        if winding_class(word, n) != "odd-winding":
            continue
        if has_provider_interval(word, ms):
            continue
        configs = build_configs(word, ms)
        if has_any_ec(word, configs, ms):
            continue
        out.append(word)
    return out


def analyze(
    cycles: list[tuple[int, ...]], ms: tuple[int, ...]
) -> tuple[Counter, list[dict[str, object]], Counter, list[dict[str, object]]]:
    open_hist: Counter = Counter()
    open_non_divisible: list[dict[str, object]] = []
    return_hist: Counter = Counter()
    return_k_zero_witnesses: list[dict[str, object]] = []
    for word in cycles:
        rec = first_binary_arc_record(word, ms)
        if rec["open_k"] is None:
            open_non_divisible.append(rec)
        else:
            open_hist[rec["open_k"]] += 1
        if rec["return_k"] is None:
            raise ValueError(f"return interval not divisible by n for {rec}")
        return_hist[rec["return_k"]] += 1
        if rec["return_k"] == 0 and len(return_k_zero_witnesses) < 5:
            return_k_zero_witnesses.append(rec)
    return open_hist, open_non_divisible, return_hist, return_k_zero_witnesses


def parse_ms(text: str) -> tuple[int, ...]:
    cleaned = text.strip()
    if cleaned.startswith("(") and cleaned.endswith(")"):
        cleaned = cleaned[1:-1]
    parts = [part.strip() for part in cleaned.split(",") if part.strip()]
    if not parts:
        raise argparse.ArgumentTypeError(f"empty multiset: {text!r}")
    try:
        ms = tuple(int(part) for part in parts)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"bad multiset {text!r}") from exc
    if any(m < 2 for m in ms):
        raise argparse.ArgumentTypeError(f"all entries must be >= 2: {text!r}")
    if len(ms) < 4:
        raise argparse.ArgumentTypeError(f"need at least 4 processors: {text!r}")
    return ms


def has_three_consecutive_binary(ms: tuple[int, ...]) -> bool:
    n = len(ms)
    return any(ms[i] == 2 and ms[(i + 1) % n] == 2 and ms[(i + 2) % n] == 2 for i in range(n))


def threshold(n: int) -> int:
    return 4 * (3 ** (n - 2))


def print_case_header(ms: tuple[int, ...], cap: int) -> None:
    n = len(ms)
    cl = sum(ms)
    prod_ms = prod(ms)
    thr = threshold(n)
    print("=" * 72)
    print("Odd-winding arc-displacement probe")
    print("=" * 72)
    print(f"family: n={n}, ms={ms}, CL={cl}")
    print(f"product={prod_ms}, threshold={thr}, sub-threshold={prod_ms < thr}")
    print(
        f"binary-count={sum(1 for m in ms if m == 2)}, "
        f"has-3CB={has_three_consecutive_binary(ms)}"
    )
    print("residual filter: odd-winding + no-provider-interval + EC-free")
    print("primary statistic: corrected return interval [a1,a2)")
    print(f"enumeration cap: {cap} valid cycles")
    print()


def run_case(ms: tuple[int, ...], cap: int) -> None:
    print_case_header(ms, cap)
    raw_cycles, raw_hit_cap = enumerate_cycles(ms, cap=cap)
    canon_map: dict[tuple[int, ...], tuple[int, ...]] = {}
    for word in raw_cycles:
        canon_map.setdefault(canonicalize(word), word)
    unique_cycles = list(canon_map.values())

    raw_residual = filter_residual(raw_cycles, ms)
    unique_residual = filter_residual(unique_cycles, ms)

    print(f"raw valid cycles: {len(raw_cycles)}")
    print(f"rotation-canonical valid cycles: {len(unique_cycles)}")
    print(f"raw residual cycles: {len(raw_residual)}")
    print(f"rotation-canonical residual cycles: {len(unique_residual)}")
    if raw_hit_cap:
        print("WARNING: valid-cycle enumeration hit the cap; results are a sample, not exhaustive.")
    print()

    raw_open_hist, raw_open_nondiv, raw_return_hist, raw_return_k0 = analyze(raw_residual, ms)
    uniq_open_hist, uniq_open_nondiv, uniq_return_hist, uniq_return_k0 = analyze(unique_residual, ms)

    print("Raw residual distribution on corrected return interval [a1,a2)")
    print(f"  divisible-by-n cases: {sum(raw_return_hist.values())}")
    print("  non-divisible cases:  0")
    print(f"  k histogram:          {dict(sorted(raw_return_hist.items()))}")
    print()

    print("Rotation-canonical residual distribution on corrected return interval [a1,a2)")
    print(f"  divisible-by-n cases: {sum(uniq_return_hist.values())}")
    print("  non-divisible cases:  0")
    print(f"  k histogram:          {dict(sorted(uniq_return_hist.items()))}")
    print()

    print("Raw open-interval diagnostic on (a1,a2)")
    print(f"  divisible-by-n cases: {sum(raw_open_hist.values())}")
    print(f"  non-divisible cases:  {len(raw_open_nondiv)}")
    print(f"  k histogram:          {dict(sorted(raw_open_hist.items()))}")
    print()

    print("Rotation-canonical open-interval diagnostic on (a1,a2)")
    print(f"  divisible-by-n cases: {sum(uniq_open_hist.values())}")
    print(f"  non-divisible cases:  {len(uniq_open_nondiv)}")
    print(f"  k histogram:          {dict(sorted(uniq_open_hist.items()))}")
    print()

    if raw_open_nondiv:
        print("First non-divisible raw open-interval examples")
        for rec in raw_open_nondiv[:5]:
            print(
                f"  b={rec['b']}, fc[b]={rec['fire_count_b']}, fires=({rec['a1']}, {rec['a2']}), "
                f"open_arc_disp={rec['open_arc_disp']}, "
                f"return_disp={rec['return_disp']}, word={rec['word']}"
            )
        print()

    if uniq_return_k0:
        print("Rotation-canonical corrected-return k = 0 witnesses")
        for rec in uniq_return_k0[:5]:
            print(
                f"  b={rec['b']}, fc[b]={rec['fire_count_b']}, fires=({rec['a1']}, {rec['a2']}), "
                f"return_disp={rec['return_disp']}, word={rec['word']}"
            )
    else:
        print("Rotation-canonical corrected-return k = 0 witnesses: none")
    print()

    if raw_return_k0 and not uniq_return_k0:
        print("raw corrected-return k = 0 exists only as rotation multiplicity")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "families",
        nargs="*",
        type=parse_ms,
        help="comma-separated family, e.g. 2,3,3,2,3,3,2,3,3",
    )
    parser.add_argument(
        "--cap",
        type=int,
        default=500000,
        help="maximum number of valid cycles to enumerate per family",
    )
    args = parser.parse_args()

    families = args.families or [DEFAULT_MS]
    for idx, ms in enumerate(families):
        if idx:
            print()
        run_case(ms, args.cap)


if __name__ == "__main__":
    main()
