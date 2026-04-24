#!/usr/bin/env python3
"""
Phase 0g: histogram of interior size `I` across oscillatory B2B runs.

Sub-lemma 3 of the Lemma A proof attempt is proved for `I = 2`. This
probe reports how much of the oscillatory run population sits at `I = 2`
(already covered) vs `I >= 3` (still open), per family.

`I` is the number of strict interior positions in the gap between binary
anchors `b, c` that the run actually touches, i.e. the length of the
open cyclic segment `(s, e)`: `I = (e - s) mod L - 1` steps but measured
on RING positions is `R - 1` where `R = (e - s) mod L`. Here we report
`gap_size = |gap_interior_cw(b, c)|` and `run_len = (e - s) mod L`.
"""

import time
from collections import Counter

from zw_lemma_a_caseprobe import (
    enumerate_min_length_cycles,
    canonical_rotation,
    is_zw_cwpos,
    binary_pairs,
    find_gap_runs,
    is_oscillatory,
    gap_interior_cw,
)


def run_family(label, ms, n):
    L = sum(ms)
    print(f"\n=== {label}: n={n}, ms={tuple(ms)} ===", flush=True)
    t0 = time.time()
    raw = enumerate_min_length_cycles(list(ms), n)
    uniq = set(canonical_rotation(w) for w in raw)
    zw = [w for w in uniq if is_zw_cwpos(w, n)]
    t1 = time.time()
    print(f"  ZW cw>0 cycles: {len(zw)} (enum {t1 - t0:.1f}s)", flush=True)

    gap_hist = Counter()          # gap_size -> count
    runlen_hist = Counter()       # run_len  -> count
    joint_hist = Counter()        # (gap_size, run_len) -> count
    run_count = 0

    for w in zw:
        wlen = len(w)
        for b, c, interior in binary_pairs(list(ms), n):
            gap_size = len(interior)
            for (s, e) in find_gap_runs(w, b, c, interior):
                if not is_oscillatory(w, s, e, n):
                    continue
                run_count += 1
                run_len = (e - s) % wlen
                gap_hist[gap_size] += 1
                runlen_hist[run_len] += 1
                joint_hist[(gap_size, run_len)] += 1

    print(f"  Total oscillatory B2B runs: {run_count}", flush=True)
    print(f"  gap_size histogram: {dict(sorted(gap_hist.items()))}", flush=True)
    print(f"  run_len  histogram: {dict(sorted(runlen_hist.items()))}", flush=True)
    print(f"  (gap_size, run_len) histogram:", flush=True)
    for k, v in sorted(joint_hist.items()):
        print(f"    {k}  x {v}", flush=True)
    I2 = sum(v for (g, _), v in joint_hist.items() if g == 2)
    total = sum(joint_hist.values())
    if total > 0:
        print(f"  I=2 (gap_size=2) share: {I2}/{total} = {100.0*I2/total:.1f}%",
              flush=True)


if __name__ == "__main__":
    families = [
        (9,  "n9  all-odd-gap",       [2, 3, 3, 2, 3, 3, 2, 3, 3]),
        (9,  "n9  3-consec-binary",   [2, 2, 2, 3, 3, 3, 3, 3, 3]),
        (9,  "n9  pivot alt",         [2, 3, 2, 3, 2, 3, 3, 3, 3]),
        (9,  "n9  3-all-spaced",      [2, 3, 3, 3, 2, 3, 3, 3, 2]),
        (9,  "n9  gap-(2,3,4)",       [2, 3, 2, 3, 3, 2, 3, 3, 3]),
        (9,  "n9  4-bin alternating", [2, 3, 2, 3, 2, 3, 2, 3, 3]),
        (11, "n11 all-odd-gap",       [2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 3]),
        (11, "n11 3-consec-binary",   [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3]),
        (11, "n11 pivot 3bin",        [2, 3, 2, 3, 2, 3, 3, 3, 3, 3, 3]),
        (11, "n11 4-bin spaced",      [2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3]),
    ]
    for n, label, ms in families:
        run_family(label, ms, n)
