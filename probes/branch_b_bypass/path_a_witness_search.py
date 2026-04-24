#!/usr/bin/env python3
"""
Path A witness existence probe — A1 residual (2026-04-13).

Search guidance for `path_a_witness_existence_spec_2026-04-13.md`.

For every cycle in the 348 + 2028 A1 residual, enumerate all interior
ternary sites `i` and all non-wrap consecutive-fire pairs (a1, a2) of
`i`, checking whether any `(i, a1, a2, k2)` admits the Lean provider
shape from `ZeroWinding.lean:47-84`:

  hlt:      a1 < a2 (linearly, strict)
  ha2:      moverAt a2 = i
  hno_i:    no fire of i on open interval (a1, a2)
  k2 in (a1, a2) open
  provider: Option 1 — left(i) silent on [k2, a2) AND right(i) binary
            AND intervalFireCount(right(i), k2, a2) is even
         OR Option 2 — left(i) binary AND intervalFireCount(left(i), k2, a2) even
            AND right(i) silent on [k2, a2)

Report Q1 (coverage), Q2 (site distribution), Q3 (failures).
"""

from __future__ import annotations

import importlib.util
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


RESID = load_module(
    "charac_A1_nonosc_residual",
    ROOT / "probes/branch_b_bypass/charac_A1_nonosc_residual.py",
)


@dataclass(frozen=True)
class Family:
    n: int
    label: str
    ms: tuple[int, ...]
    expected_residual: int


FAMILIES = [
    Family(9, "n9 pivot alt", (2, 3, 2, 3, 2, 3, 3, 3, 3), 348),
    Family(11, "n11 pivot 3bin", (2, 3, 2, 3, 2, 3, 3, 3, 3, 3, 3), 2028),
]


def left_ring(i: int, n: int) -> int:
    return (i - 1) % n


def right_ring(i: int, n: int) -> int:
    return (i + 1) % n


def is_binary(ms: tuple[int, ...], i: int) -> bool:
    return ms[i] == 2


def fire_steps(word, i: int):
    return [k for k, p in enumerate(word) if p == i]


def interval_fire_count(word, q: int, lo: int, hi: int) -> int:
    """Count k in [lo, hi) with word[k] == q. Linear interval, lo <= hi."""
    return sum(1 for k in range(lo, hi) if word[k] == q)


def has_any_fire(word, q: int, lo: int, hi: int) -> bool:
    return any(word[k] == q for k in range(lo, hi))


def check_witness(word, ms, n, i: int, a1: int, a2: int, k2: int) -> str | None:
    """Return 'Option1', 'Option2', or None if no witness at (i, a1, a2, k2)."""
    # hlt: a1 < a2
    if not (a1 < a2):
        return None
    # ha2
    if word[a2] != i:
        return None
    # hno_i: no fire of i in open (a1, a2)
    for k in range(a1 + 1, a2):
        if word[k] == i:
            return None
    # k2 in (a1, a2) open
    if not (a1 < k2 < a2):
        return None
    li = left_ring(i, n)
    ri = right_ring(i, n)
    # Option 1: left(i) silent on [k2, a2), right(i) binary, right(i) fires even
    opt1_left_silent = not has_any_fire(word, li, k2, a2)
    opt1_right_binary = is_binary(ms, ri)
    opt1_right_even = (interval_fire_count(word, ri, k2, a2) % 2 == 0)
    if opt1_left_silent and opt1_right_binary and opt1_right_even:
        return "Option1"
    # Option 2: left(i) binary, left(i) fires even, right(i) silent on [k2, a2)
    opt2_left_binary = is_binary(ms, li)
    opt2_left_even = (interval_fire_count(word, li, k2, a2) % 2 == 0)
    opt2_right_silent = not has_any_fire(word, ri, k2, a2)
    if opt2_left_binary and opt2_left_even and opt2_right_silent:
        return "Option2"
    return None


def check_wrap_witness(word, ms, n, i: int, a: int, s_max: int) -> str | None:
    """Wrap-aware analogue of `check_witness`, matching the shape of
    `general_wrapping_step_pair_ec` (CyclicContext.lean:195).

    Hypotheses:
      - a < s_max (linear, strict)
      - word[a] == i and word[s_max] == i
      - no fire of i at k < a (hno_i_before)
      - no fire of i at k > s_max (hno_i_after)
      - wrap_nonempty: (s_max + 1) % L != a  (so the wrap interval is non-trivial)

    Provider (Option 1): left(i) silent on BOTH [s_max+1, L) and [0, a),
      right(i) binary, SUMMED fire count of right(i) on those two intervals even.
    Provider (Option 2): left(i) binary, SUMMED fire count even, right(i) silent.

    Returns 'WrapOption1', 'WrapOption2', or None.
    """
    L = len(word)
    if not (a < s_max):
        return None
    if word[a] != i or word[s_max] != i:
        return None
    # no fire of i before a
    for k in range(0, a):
        if word[k] == i:
            return None
    # no fire of i after s_max
    for k in range(s_max + 1, L):
        if word[k] == i:
            return None
    # wrap non-empty
    if (s_max + 1) % L == a:
        return None
    li = left_ring(i, n)
    ri = right_ring(i, n)

    def silent_on_wrap(q):
        return (not has_any_fire(word, q, s_max + 1, L)) and (not has_any_fire(word, q, 0, a))

    def fire_count_wrap(q):
        return interval_fire_count(word, q, s_max + 1, L) + interval_fire_count(word, q, 0, a)

    # Option 1: left silent, right binary, right even-count
    if silent_on_wrap(li) and is_binary(ms, ri) and (fire_count_wrap(ri) % 2 == 0):
        return "WrapOption1"
    # Option 2: left binary, left even-count, right silent
    if is_binary(ms, li) and (fire_count_wrap(li) % 2 == 0) and silent_on_wrap(ri):
        return "WrapOption2"
    return None


def search_cycle(word, ms, n, include_binary_sites: bool = True):
    """Search all sites (default: including binary) and all consec-fire pairs,
    including wrap-around pairs.

    Linear pairs are checked via `check_witness` against `general_step_pair_ec`;
    wrap pairs via `check_wrap_witness` against `general_wrapping_step_pair_ec`.

    Returns list of (i, a1_or_a, a2_or_smax, k2_or_None, option) tuples for
    every matching witness.
    """
    hits = []
    for i in range(n):
        if ms[i] == 2 and not include_binary_sites:
            continue
        fires = fire_steps(word, i)
        if len(fires) < 2:
            continue
        # linear consec-fire pairs
        for idx in range(len(fires) - 1):
            a1 = fires[idx]
            a2 = fires[idx + 1]
            for k2 in range(a1 + 1, a2):
                option = check_witness(word, ms, n, i, a1, a2, k2)
                if option is not None:
                    hits.append((i, a1, a2, k2, option))
                    break
        # wrap-around pair: a = first fire, s_max = last fire
        a = fires[0]
        s_max = fires[-1]
        option = check_wrap_witness(word, ms, n, i, a, s_max)
        if option is not None:
            hits.append((i, a, s_max, None, option))
    return hits


def main():
    drift = []
    per_family = {}
    for fam in FAMILIES:
        residual_words = RESID.residual_population(fam)
        if len(residual_words) != fam.expected_residual:
            drift.append(
                f"{fam.label}: expected {fam.expected_residual}, got {len(residual_words)}"
            )
        per_family[fam.label] = (fam, residual_words)

    if drift:
        print("DRIFT DETECTED: " + "; ".join(drift))
        return

    print("=" * 70)
    print("Path A — witness existence on A1 residual")
    print("=" * 70)
    print()

    grand_witnessed = 0
    grand_total = 0
    failures_all = []

    for fam in FAMILIES:
        _fam, words = per_family[fam.label]
        witnessed = 0
        site_counter = Counter()
        option_counter = Counter()
        family_failures = []
        for word in words:
            hits = search_cycle(word, fam.ms, fam.n)
            if hits:
                witnessed += 1
                for i, a1, a2, k2, option in hits:
                    site_counter[i] += 1
                    option_counter[option] += 1
            else:
                family_failures.append(word)
        grand_witnessed += witnessed
        grand_total += len(words)
        print(f"### {fam.label}")
        print(f"  Q1 coverage: {witnessed} / {len(words)}")
        top_sites = ", ".join(f"i={i}:{c}" for i, c in site_counter.most_common(10))
        print(f"  Q2 site distribution (hit counts, top 10): {top_sites}")
        print(f"  Q2 option distribution: {dict(option_counter)}")
        if family_failures:
            print(f"  Q3 failures: {len(family_failures)}")
            for w in family_failures[:5]:
                print(f"    word={list(w)}")
            if len(family_failures) > 5:
                print(f"    ... and {len(family_failures) - 5} more")
        else:
            print("  Q3 failures: 0")
        failures_all.extend((fam, w) for w in family_failures)
        print()

    print("=" * 70)
    print(f"Grand total: {grand_witnessed} / {grand_total} witnessed")
    if grand_witnessed == grand_total:
        print("VERDICT: Path A witness existence EMPIRICALLY CONFIRMED on full residual.")
    else:
        print(
            f"VERDICT: {grand_total - grand_witnessed} cycles unwitnessed — "
            "conjecture needs refinement."
        )
    print("=" * 70)


if __name__ == "__main__":
    main()
