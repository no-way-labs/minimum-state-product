#!/usr/bin/env python3
"""
Path A L4d wrap-vs-linear stay probe.

For each Path A pivot cycle, for each sandwich-T `i`, classify the
stay step as:
  - linear: fires at (k, k+1) with k+1 < L
  - wrap:   fires at (L-1, 0)

L4d cases (a)/(b) (linear stay) close analytically by collapsing
one of A_0 or A_1. Case (c) (wrap stay) needs an independent
argument. If case (c) is empirically empty, L4d closes analytically
modulo "case (c) does not occur".
"""

from __future__ import annotations

import importlib.util
import sys
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


UNIV = load_module(
    "path_a_universal",
    ROOT / "probes/branch_b_bypass/path_a_witness_search_universal.py",
)


def sandwiched_indices(ms):
    n = len(ms)
    out = []
    for i in range(n):
        if ms[i] == 3 and ms[(i - 1) % n] == 2 and ms[(i + 1) % n] == 2:
            out.append(i)
    return out


def stay_kind_at(word, i):
    """Return 'linear', 'wrap', 'both', or 'none'."""
    L = len(word)
    has_linear = False
    has_wrap = False
    for k in range(L - 1):
        if word[k] == i and word[k + 1] == i:
            has_linear = True
            break
    if word[L - 1] == i and word[0] == i:
        has_wrap = True
    if has_linear and has_wrap:
        return "both"
    if has_linear:
        return "linear"
    if has_wrap:
        return "wrap"
    return "none"


def main():
    print("=" * 70)
    print("Path A L4d wrap-vs-linear stay probe")
    print("=" * 70)
    print()

    grand_kinds = Counter()

    for fam in UNIV.FAMILIES:
        sandwiches = sandwiched_indices(fam.ms)
        if not sandwiches:
            continue
        words = UNIV.path_a_population(fam)
        kinds = Counter()
        for word in words:
            for i in sandwiches:
                kinds[stay_kind_at(word, i)] += 1
        for k, v in kinds.items():
            grand_kinds[k] += v
        print(f"### {fam.label}")
        print(f"  population: {len(words)}, sandwich-Ts: {sandwiches}")
        print(f"  per-(cycle × sandwich-T) stay kind: {dict(kinds)}")
        total_per_sandwich = sum(kinds.values())
        print(f"  total per-sandwich entries: {total_per_sandwich}")
        print()

    print("=" * 70)
    print(f"Grand stay-kind counter: {dict(grand_kinds)}")
    print("=" * 70)
    if grand_kinds.get("wrap", 0) == 0 and grand_kinds.get("both", 0) == 0:
        print("VERDICT: every sandwich-T stay is LINEAR.")
        print("L4d closes analytically: linear stay → empty A_0 or A_1 → not (1,1,0).")
    elif grand_kinds.get("none", 0) > 0:
        print(f"VERDICT: {grand_kinds.get('none', 0)} sandwich-Ts have NO stay.")
        print("Need additional analytical work for the no-stay sub-case.")
    else:
        wrap_count = grand_kinds.get("wrap", 0) + grand_kinds.get("both", 0)
        print(f"VERDICT: {wrap_count} sandwich-Ts have wrap or both stays.")
        print("Linear-stay sub-case is closable; wrap/both sub-cases remain open.")
    print("=" * 70)


if __name__ == "__main__":
    main()
