#!/usr/bin/env python3
"""
Path A L4d multiset probe.

Rotation-invariant version. For each Path A pivot cycle, for each
sandwich-T `i` with `fc[i] = 3`, compute the L4a triples
`(c_0_L, c_1_L, c_w_L)` and `(c_0_R, c_1_R, c_w_R)` over the
canonical f_0 < f_1 < f_2 ordering, then check the SORTED
multisets `sorted(triple_L) == sorted(triple_R) == [0, 1, 1]`.

If even the multiset version is empty across all pivot families,
then L4d's full conclusion (double-(1,1,0) impossible regardless of
rotation) holds empirically as a rotation-invariant statement.
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
    return [
        i for i in range(n)
        if ms[i] == 3 and ms[(i - 1) % n] == 2 and ms[(i + 1) % n] == 2
    ]


def fires_of(word, p):
    return [k for k, x in enumerate(word) if x == p]


def interval_count(word, p, lo, hi):
    return sum(1 for k in range(lo, hi) if word[k] == p)


def l4a_triple(word, i, b, n):
    """Return (c_0, c_1, c_w) for binary b at sandwich-T i with 3 fires."""
    L = len(word)
    fires = fires_of(word, i)
    assert len(fires) == 3, f"expected 3 i-fires, got {len(fires)}"
    f0, f1, f2 = fires
    c0 = interval_count(word, b, f0 + 1, f1)
    c1 = interval_count(word, b, f1 + 1, f2)
    cw = interval_count(word, b, 0, f0) + interval_count(word, b, f2 + 1, L)
    return (c0, c1, cw)


def main():
    print("=" * 70)
    print("Path A L4d multiset probe (rotation-invariant)")
    print("=" * 70)
    print()

    grand_labelled_110 = 0
    grand_multiset_110 = 0
    grand_count_total = 0
    grand_lr_pairs = Counter()

    for fam in UNIV.FAMILIES:
        sandwiches = sandwiched_indices(fam.ms)
        if not sandwiches:
            continue
        words = UNIV.path_a_population(fam)
        labelled_110 = 0
        multiset_110 = 0
        count_total = 0
        lr_pairs = Counter()
        for word in words:
            for i in sandwiches:
                bL = (i - 1) % fam.n
                bR = (i + 1) % fam.n
                tL = l4a_triple(word, i, bL, fam.n)
                tR = l4a_triple(word, i, bR, fam.n)
                count_total += 1
                lr_pairs[(tuple(sorted(tL)), tuple(sorted(tR)))] += 1
                if tL == (1, 1, 0) and tR == (1, 1, 0):
                    labelled_110 += 1
                if sorted(tL) == [0, 1, 1] and sorted(tR) == [0, 1, 1]:
                    multiset_110 += 1
        grand_labelled_110 += labelled_110
        grand_multiset_110 += multiset_110
        grand_count_total += count_total
        for k, v in lr_pairs.items():
            grand_lr_pairs[k] += v
        print(f"### {fam.label}")
        print(f"  population: {len(words)}, sandwich-Ts: {sandwiches}")
        print(f"  per-sandwich entries: {count_total}")
        print(f"  labelled (1,1,0)/(1,1,0):   {labelled_110}")
        print(f"  multiset {{0,1,1}}/{{0,1,1}}: {multiset_110}")
        print(f"  top 6 (sortedL, sortedR) pairs:")
        for pair, c in lr_pairs.most_common(6):
            print(f"    {pair}: {c}")
        print()

    print("=" * 70)
    print(f"Grand totals: {grand_count_total} entries")
    print(f"Labelled (1,1,0)/(1,1,0):   {grand_labelled_110}")
    print(f"Multiset {{0,1,1}}/{{0,1,1}}: {grand_multiset_110}")
    print()
    if grand_multiset_110 == 0:
        print("VERDICT: even the rotation-invariant multiset version is empty.")
        print("L4d holds as a rotation-invariant claim:")
        print("  for every sandwich-T, the multiset {c_0, c_1, c_w} for at least one")
        print("  binary is NOT {0,1,1}.")
    else:
        print(f"VERDICT: multiset version has {grand_multiset_110} hits;")
        print("L4d as labelled is empirically vacuous, but the multiset version is not.")
    print("=" * 70)


if __name__ == "__main__":
    main()
