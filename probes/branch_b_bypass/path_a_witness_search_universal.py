#!/usr/bin/env python3
"""
Path A universal probe — test witness existence on ZW cwPos min-CL cycles
with no oscillatory B2B run anywhere, across all 7 families tested by A1.

The A1 residual (as previously defined) was specific to stretched-SSR
failure + no-osc-B2B. The real scope for Path A in Sorry #1 is the broader
class: ZW cwPos cycles where Branch A's theorem doesn't apply (i.e., no
oscillatory B2B run anywhere). This probe verifies Path A's witness
existence on that broader class across all tested families.

Re-uses the witness search logic from `path_a_witness_search.py`.
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


A1 = load_module(
    "a1_probe", ROOT / "probes/branch_b_bypass/derisk_A1_stretched_ssr_tail.py"
)
Budget = load_module(
    "budget_probe", ROOT / "probes/zw_mechanism_budget_probe.py"
)
WITNESS = load_module(
    "path_a_witness_search",
    ROOT / "probes/branch_b_bypass/path_a_witness_search.py",
)


@dataclass(frozen=True)
class Family:
    n: int
    label: str
    ms: tuple[int, ...]


# All 7 families from the A1 bypass plan.
FAMILIES = [
    Family(9, "n9 all-odd-gap", (2, 3, 3, 2, 3, 3, 2, 3, 3)),
    Family(9, "n9 3-consec-binary", (2, 2, 2, 3, 3, 3, 3, 3, 3)),
    Family(9, "n9 pivot alt", (2, 3, 2, 3, 2, 3, 3, 3, 3)),
    Family(9, "n9 3-all-spaced", (2, 3, 3, 3, 2, 3, 3, 3, 2)),
    Family(11, "n11 all-odd-gap", (2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 3)),
    Family(11, "n11 3-consec-binary", (2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3)),
    Family(11, "n11 pivot 3bin", (2, 3, 2, 3, 2, 3, 3, 3, 3, 3, 3)),
]


def binary_pairs(ms, n):
    return Budget.binary_pairs(list(ms), n)


def any_oscillatory_b2b(word, ms, n):
    for b, c, interior in binary_pairs(ms, n):
        for s, e in Budget.find_gap_runs(word, b, c, interior):
            if Budget.is_oscillatory(word, s, e, n):
                return True
    return False


def path_a_population(fam: Family):
    """All ZW cwPos min-CL cycles with no oscillatory B2B run anywhere."""
    raw = A1.enumerate_min_length_cycles(list(fam.ms), fam.n)
    uniq = sorted(set(A1.canonical_rotation(w) for w in raw))
    zw = [w for w in uniq if A1.is_zw_cwpos(w, fam.n)]
    return [w for w in zw if not any_oscillatory_b2b(w, fam.ms, fam.n)]


def main():
    print("=" * 70)
    print("Path A universal — witness existence on ZW cwPos min-CL")
    print("+ no oscillatory B2B run, across 7 A1-tested families")
    print("=" * 70)
    print()

    grand_witnessed = 0
    grand_total = 0

    for fam in FAMILIES:
        words = path_a_population(fam)
        witnessed = 0
        site_counter = Counter()
        option_counter = Counter()
        failures = []
        for word in words:
            hits = WITNESS.search_cycle(word, fam.ms, fam.n)
            if hits:
                witnessed += 1
                for i, a1, a2, k2, option in hits:
                    site_counter[i] += 1
                    option_counter[option] += 1
            else:
                failures.append(word)

        grand_witnessed += witnessed
        grand_total += len(words)

        print(f"### {fam.label}")
        print(f"  non-osc population: {len(words)}")
        if len(words) == 0:
            print("  (no cycles in Path A scope — every cycle has an oscillatory B2B run)")
            print()
            continue
        print(f"  witnessed: {witnessed} / {len(words)}")
        top = ", ".join(f"i={i}:{c}" for i, c in site_counter.most_common(10))
        print(f"  site distribution (top 10): {top}")
        print(f"  option distribution: {dict(option_counter)}")
        if failures:
            print(f"  failures: {len(failures)}")
            for w in failures[:5]:
                print(f"    word={list(w)}")
            if len(failures) > 5:
                print(f"    ... and {len(failures) - 5} more")
        else:
            print("  failures: 0")
        print()

    print("=" * 70)
    print(f"Grand total: {grand_witnessed} / {grand_total} witnessed")
    if grand_witnessed == grand_total and grand_total > 0:
        print("VERDICT: Path A EMPIRICALLY CONFIRMED ON ALL 7 FAMILIES.")
    elif grand_total == 0:
        print("VERDICT: No cycles in Path A scope across any family.")
    else:
        print(f"VERDICT: {grand_total - grand_witnessed} unwitnessed cycles.")
    print("=" * 70)


if __name__ == "__main__":
    main()
