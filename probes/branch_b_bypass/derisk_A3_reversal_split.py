#!/usr/bin/env python3
"""A3 derisk check: reversalCount split on small ZW good cycles.

This follows the branch-B bypass plan entry for candidate A3:
  - use the CycleTypes `reversalCount` definition exactly,
  - test small n=5,7,9 families,
  - split cycles into `reversalCount <= 2` vs `>= 4`,
  - check the low-reversal side for a two-sweep pattern,
  - check the high-reversal side for at least one oscillatory gap subrun.

The cycle enumeration matches the earlier ZW provider probes in this repo:
minimum-length abstract good cycles (distinct configurations, return to start,
local L/stay/R mover steps, fire counts equal to the local modulus vector).
"""

from __future__ import annotations

import argparse
import time
from collections import Counter
from dataclasses import dataclass
from typing import Iterable


def left(p: int, n: int) -> int:
    return (p - 1) % n


def right(p: int, n: int) -> int:
    return (p + 1) % n


@dataclass(frozen=True)
class Family:
    n: int
    label: str
    ms: tuple[int, ...]


def enumerate_min_length_cycles(ms: tuple[int, ...], n: int) -> list[tuple[int, ...]]:
    """Enumerate the min-CL abstract good cycles used by the earlier ZW probes."""
    cycle_len = sum(ms)
    start_cfg = tuple(0 for _ in range(n))
    out: list[tuple[int, ...]] = []

    def dfs(
        word: list[int],
        fire_counts: list[int],
        config: tuple[int, ...],
        visited: set[tuple[int, ...]],
    ) -> None:
        depth = len(word)
        if depth == cycle_len:
            first = word[0]
            last = word[-1]
            if first not in (left(last, n), last, right(last, n)):
                return
            if config != start_cfg:
                return
            if any(fire_counts[p] != ms[p] for p in range(n)):
                return
            out.append(tuple(word))
            return

        remaining = cycle_len - depth
        needed = sum(ms[p] - fire_counts[p] for p in range(n) if fire_counts[p] < ms[p])
        if needed > remaining:
            return

        curr = word[-1]
        for nxt in (right(curr, n), left(curr, n), curr):
            if fire_counts[nxt] >= ms[nxt]:
                continue
            next_cfg = list(config)
            next_cfg[nxt] = (next_cfg[nxt] + 1) % ms[nxt]
            next_cfg_t = tuple(next_cfg)
            if next_cfg_t in visited:
                if not (next_cfg_t == start_cfg and depth == cycle_len - 1):
                    continue
            next_fire_counts = list(fire_counts)
            next_fire_counts[nxt] += 1
            word.append(nxt)
            added = False
            if next_cfg_t != start_cfg:
                visited.add(next_cfg_t)
                added = True
            dfs(word, next_fire_counts, next_cfg_t, visited)
            if added:
                visited.discard(next_cfg_t)
            word.pop()

    start_proc = 0
    fire_counts0 = [0] * n
    fire_counts0[start_proc] = 1
    config0 = [0] * n
    config0[start_proc] = 1 % ms[start_proc]
    visited0 = {tuple(config0)}
    dfs([start_proc], fire_counts0, tuple(config0), visited0)
    return out


def canonical_rotation(word: tuple[int, ...]) -> tuple[int, ...]:
    return min(word[i:] + word[:i] for i in range(len(word)))


def is_zero_winding_cw_pos(word: tuple[int, ...], n: int) -> bool:
    cw = 0
    ccw = 0
    for k, curr in enumerate(word):
        nxt = word[(k + 1) % len(word)]
        if nxt == right(curr, n):
            cw += 1
        elif nxt == left(curr, n):
            ccw += 1
    return cw == ccw and cw > 0


def step_dirs(word: tuple[int, ...], n: int) -> list[str]:
    dirs: list[str] = []
    for k, curr in enumerate(word):
        nxt = word[(k + 1) % len(word)]
        if nxt == right(curr, n):
            dirs.append("cw")
        elif nxt == curr:
            dirs.append("stay")
        else:
            dirs.append("ccw")
    return dirs


def reversal_steps(word: tuple[int, ...], n: int) -> list[int]:
    dirs = step_dirs(word, n)
    revs: list[int] = []
    for k, d1 in enumerate(dirs):
        d2 = dirs[(k + 1) % len(dirs)]
        if (d1, d2) in (("cw", "ccw"), ("ccw", "cw")):
            revs.append(k)
    return revs


def reversal_count(word: tuple[int, ...], n: int) -> int:
    return len(reversal_steps(word, n))


def two_sweep_proxy(word: tuple[int, ...], n: int) -> bool:
    """Mover-word proxy for the A3 low-reversal branch.

    The 2026-04-13 Branch-B note identifies the key structure as a single cw
    block followed by a single ccw block, up to cyclic rotation. We check that
    on the non-stay direction word, since exact `reversalCount` ignores flips
    separated by stay steps.
    """
    nonstay = [d for d in step_dirs(word, n) if d != "stay"]
    if "cw" not in nonstay or "ccw" not in nonstay:
        return False
    sign_changes = sum(1 for i, d in enumerate(nonstay) if d != nonstay[(i + 1) % len(nonstay)])
    return sign_changes == 2


def gap_interior_cw(b: int, c: int, n: int) -> tuple[int, ...]:
    out: list[int] = []
    k = right(b, n)
    while k != c:
        out.append(k)
        k = right(k, n)
    return tuple(out)


def consecutive_binary_gaps(ms: tuple[int, ...], n: int) -> list[tuple[int, int, frozenset[int]]]:
    binaries = [p for p, m in enumerate(ms) if m == 2]
    gaps: list[tuple[int, int, frozenset[int]]] = []
    for idx, b in enumerate(binaries):
        c = binaries[(idx + 1) % len(binaries)]
        interior = frozenset(gap_interior_cw(b, c, n))
        if interior:
            gaps.append((b, c, interior))
    return gaps


def find_gap_runs(
    word: tuple[int, ...],
    start_boundary: int,
    end_boundary: int,
    interior: frozenset[int],
) -> list[tuple[int, int]]:
    """Boundary-to-boundary runs through one fixed binary gap."""
    run_len = len(word)
    runs: list[tuple[int, int]] = []
    for s, mover in enumerate(word):
        if mover != start_boundary:
            continue
        k = (s + 1) % run_len
        if word[k] not in interior:
            continue
        steps = 0
        while word[k] in interior:
            k = (k + 1) % run_len
            steps += 1
            if steps > run_len:
                break
        if word[k] == end_boundary:
            runs.append((s, k))
    return runs


def is_oscillatory(word: tuple[int, ...], s: int, e: int, n: int) -> bool:
    has_cw = False
    has_ccw = False
    k = s
    steps = 0
    while k != e and steps <= len(word):
        nxt = (k + 1) % len(word)
        if word[nxt] == right(word[k], n):
            has_cw = True
        elif word[nxt] == left(word[k], n):
            has_ccw = True
        if has_cw and has_ccw:
            return True
        k = nxt
        steps += 1
    return has_cw and has_ccw


def oscillatory_gap_runs(word: tuple[int, ...], ms: tuple[int, ...], n: int) -> list[tuple[int, int, int, int]]:
    runs: list[tuple[int, int, int, int]] = []
    for b, c, interior in consecutive_binary_gaps(ms, n):
        for start_boundary, end_boundary in ((b, c), (c, b)):
            for s, e in find_gap_runs(word, start_boundary, end_boundary, interior):
                if is_oscillatory(word, s, e, n):
                    runs.append((start_boundary, end_boundary, s, e))
    return runs


def default_families() -> list[Family]:
    return [
        Family(5, "n5 gaps(2,0,0) [3-consec-binary]", (2, 2, 2, 3, 3)),
        Family(5, "n5 gaps(1,1,0) [alternating-3bin]", (2, 3, 2, 3, 2)),
        Family(7, "n7 gaps(4,0,0)", (2, 2, 2, 3, 3, 3, 3)),
        Family(7, "n7 gaps(3,1,0)", (2, 2, 2, 3, 2, 3, 3)),
        Family(7, "n7 gaps(2,2,0)", (2, 2, 3, 3, 2, 3, 3)),
        Family(7, "n7 gaps(2,1,1)", (2, 3, 2, 3, 2, 3, 3)),
        Family(9, "n9 gaps(6,0,0) [3-consec-binary]", (2, 2, 2, 3, 3, 3, 3, 3, 3)),
        Family(9, "n9 gaps(4,2,0) [pivot alt]", (2, 3, 2, 3, 2, 3, 3, 3, 3)),
        Family(9, "n9 gaps(3,3,0) [3-all-spaced]", (2, 3, 3, 3, 2, 3, 3, 3, 2)),
        Family(9, "n9 gaps(2,2,2) [all-odd-gap]", (2, 3, 3, 2, 3, 3, 2, 3, 3)),
    ]


def all_three_binary_families() -> list[Family]:
    out: list[Family] = []
    for n in (5, 7, 9):
        ternaries = n - 3
        seen: set[tuple[int, int, int]] = set()
        for g0 in range(ternaries + 1):
            for g1 in range(ternaries - g0 + 1):
                g2 = ternaries - g0 - g1
                gap_tuple = (g0, g1, g2)
                rots = tuple(gap_tuple[i:] + gap_tuple[:i] for i in range(3))
                canon = min(rots)
                if canon in seen:
                    continue
                seen.add(canon)
                ms: list[int] = []
                for gap in canon:
                    ms.append(2)
                    ms.extend([3] * gap)
                out.append(Family(n, f"n{n} gaps{canon}", tuple(ms)))
    out.sort(key=lambda fam: (fam.n, fam.label))
    return out


def iter_families(mode: str) -> Iterable[Family]:
    if mode == "all3bin":
        return all_three_binary_families()
    return default_families()


def run_family(family: Family) -> dict[str, object]:
    n = family.n
    ms = family.ms
    t0 = time.time()
    raw = enumerate_min_length_cycles(ms, n)
    uniq = {canonical_rotation(word) for word in raw}
    zw = [word for word in uniq if is_zero_winding_cw_pos(word, n)]
    elapsed = time.time() - t0

    bucket_counts = Counter()
    low_two_sweep_failures: list[tuple[int, ...]] = []
    high_no_osc_failures: list[tuple[int, ...]] = []
    middle_bucket_examples: list[tuple[tuple[int, ...], int]] = []

    for word in zw:
        rc = reversal_count(word, n)
        bucket_counts[rc] += 1
        if rc <= 2:
            if not two_sweep_proxy(word, n):
                low_two_sweep_failures.append(word)
        elif rc >= 4:
            if not oscillatory_gap_runs(word, ms, n):
                high_no_osc_failures.append(word)
        else:
            middle_bucket_examples.append((word, rc))

    return {
        "family": family,
        "raw": len(raw),
        "unique": len(uniq),
        "zw": len(zw),
        "elapsed": elapsed,
        "bucket_counts": bucket_counts,
        "low_two_sweep_failures": low_two_sweep_failures,
        "high_no_osc_failures": high_no_osc_failures,
        "middle_bucket_examples": middle_bucket_examples,
    }


def format_word(word: tuple[int, ...]) -> str:
    return "[" + ",".join(str(x) for x in word) + "]"


def verdict_for_results(
    low_failures: int,
    high_failures: int,
    unexpected_middle: int,
    used_two_sweep_proxy: bool,
) -> str:
    if high_failures > 0:
        return "fail"
    if low_failures > 0:
        return "fail"
    if unexpected_middle > 0:
        return "partial"
    if used_two_sweep_proxy:
        return "partial"
    return "pass"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--family-set",
        choices=("default", "all3bin"),
        default="default",
        help="family set to test",
    )
    args = parser.parse_args()

    family_results = [run_family(family) for family in iter_families(args.family_set)]

    tested_families = [result["family"].label for result in family_results]  # type: ignore[index]
    low_total = 0
    high_total = 0
    low_failures = 0
    high_failures = 0
    unexpected_middle = 0

    print("Per-family summary")
    for result in family_results:
        family = result["family"]  # type: ignore[index]
        bucket_counts = result["bucket_counts"]  # type: ignore[index]
        low_count = sum(count for rc, count in bucket_counts.items() if rc <= 2)
        high_count = sum(count for rc, count in bucket_counts.items() if rc >= 4)
        middle_count = sum(count for rc, count in bucket_counts.items() if 2 < rc < 4)
        low_bad = len(result["low_two_sweep_failures"])  # type: ignore[index]
        high_bad = len(result["high_no_osc_failures"])  # type: ignore[index]
        print(
            f"  {family.label}: raw={result['raw']} unique={result['unique']} "
            f"zw={result['zw']} rev-buckets={dict(sorted(bucket_counts.items()))} "
            f"low<=2={low_count} high>=4={high_count} mid={middle_count} "
            f"low_fail={low_bad} high_fail={high_bad} "
            f"({result['elapsed']:.1f}s)"
        )
        low_total += low_count
        high_total += high_count
        low_failures += low_bad
        high_failures += high_bad
        unexpected_middle += middle_count

    print("\nDiagnostics")
    for result in family_results:
        family = result["family"]  # type: ignore[index]
        low_bad = result["low_two_sweep_failures"]  # type: ignore[index]
        high_bad = result["high_no_osc_failures"]  # type: ignore[index]
        middle = result["middle_bucket_examples"]  # type: ignore[index]
        if low_bad:
            example = low_bad[0]
            print(
                f"  low-reversal non-two-sweep: {family.label} "
                f"word={format_word(example)} dirs={step_dirs(example, family.n)}"
            )
        if high_bad:
            example = high_bad[0]
            print(
                f"  high-reversal no-oscillatory-subrun: {family.label} "
                f"word={format_word(example)} dirs={step_dirs(example, family.n)}"
            )
        if middle:
            example, rc = middle[0]
            print(
                f"  unexpected middle bucket rc={rc}: {family.label} "
                f"word={format_word(example)} dirs={step_dirs(example, family.n)}"
            )

    rate = "n/a" if high_total == 0 else f"{(high_total - high_failures) / high_total:.3f}"
    verdict = verdict_for_results(
        low_failures=low_failures,
        high_failures=high_failures,
        unexpected_middle=unexpected_middle,
        used_two_sweep_proxy=True,
    )

    print("\nA3 record")
    print(f"A3 tested families: {tested_families}")
    print(
        "A3 cycles with reversalCount ≤ 2: "
        f"{low_total}, all two-sweep?: {'yes' if low_failures == 0 else 'no'}"
    )
    print(f"A3 cycles with reversalCount ≥ 4: {high_total}")
    print(f"A3 % of ≥ 4 cycles with oscillatory subrun: {rate}")
    print(f"A3 verdict: {verdict}")

    if unexpected_middle:
        print(f"A3 note: found {unexpected_middle} cycles with reversalCount = 3.")
    print(
        "A3 note: the ≤ 2 branch uses a mover-word two-block proxy "
        "(non-stay directions form one cw block and one ccw block)."
    )


if __name__ == "__main__":
    main()
