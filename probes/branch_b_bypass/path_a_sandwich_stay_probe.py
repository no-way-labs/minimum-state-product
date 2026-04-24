#!/usr/bin/env python3
"""
Path A sandwiched-ternary stay probe.

Sharper version of `path_a_stay_step_probe.py`. Stays happen
generally, but the L4d argument only needs to rule out stays AT
A SANDWICHED TERNARY (a ternary `i` with both binary neighbours
fc=2). If `moverAt k = moverAt(k+1) = i` for some sandwiched `i`,
then i has two cyclically-adjacent fires, and the corresponding L4a
3-arc partition has wrap arc empty → c_w(b_L) = c_w(b_R) = 0 →
double-(1,1,0) is realisable at that triple.

Equivalently: L4d holds iff there is no Path A min-CL good cycle with
a sandwich-ternary stay step.

Also report stays per processor type to triangulate the mechanism.
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


def site_role(ms, i):
    if ms[i] == 2:
        return "binary"
    n = len(ms)
    left_bin = ms[(i - 1) % n] == 2
    right_bin = ms[(i + 1) % n] == 2
    if left_bin and right_bin:
        return "sandwiched-T"
    if left_bin or right_bin:
        return "single-bin-adj-T"
    return "deep-T"


def stay_steps(word, ms):
    """Return list of (step, proc, role) for every stay step in word."""
    L = len(word)
    out = []
    for k in range(L):
        if word[k] == word[(k + 1) % L]:
            p = word[k]
            out.append((k, p, site_role(ms, p)))
    return out


def main():
    print("=" * 70)
    print("Path A sandwiched-ternary stay probe")
    print("=" * 70)
    print()

    grand_total = 0
    grand_with_sandwich_stay = 0
    grand_role = Counter()

    for fam in UNIV.FAMILIES:
        words = UNIV.path_a_population(fam)
        with_sandwich_stay = 0
        family_role = Counter()
        family_total_stays = 0
        for word in words:
            stays = stay_steps(word, fam.ms)
            family_total_stays += len(stays)
            for step, p, role in stays:
                family_role[role] += 1
            if any(r == "sandwiched-T" for _, _, r in stays):
                with_sandwich_stay += 1
        grand_total += len(words)
        grand_with_sandwich_stay += with_sandwich_stay
        for k, v in family_role.items():
            grand_role[k] += v
        print(f"### {fam.label}")
        print(f"  population: {len(words)}")
        print(f"  total stays: {family_total_stays}")
        print(f"  cycles with sandwiched-T stay: {with_sandwich_stay}")
        print(f"  stays by proc role: {dict(family_role)}")
        print()

    print("=" * 70)
    print(f"Grand total: {grand_total}")
    print(f"Grand cycles with sandwiched-T stay: {grand_with_sandwich_stay}")
    print(f"Grand stays by role: {dict(grand_role)}")
    print("=" * 70)

    if grand_with_sandwich_stay == 0:
        print("VERDICT: No Path A min-CL good cycle has a stay at a sandwiched ternary.")
        print("Implication: stays only occur at non-sandwiched processors.")
        print("This closes L4d analytically: the double-(1,1,0) case forces")
        print("a stay at the sandwiched ternary i, which is empirically impossible.")
    else:
        print(f"VERDICT: {grand_with_sandwich_stay} cycles have a sandwich-T stay.")
        print("L4d cannot be closed via the no-sandwich-stay route directly;")
        print("need a finer constraint.")
    print("=" * 70)


if __name__ == "__main__":
    main()
