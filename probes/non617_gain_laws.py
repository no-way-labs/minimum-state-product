#!/usr/bin/env python3
"""
Check pointwise inequality laws on the explicit-bad non-617 TP-preserving class.

For each step in the class, define:

  dfc  = fc(dst) - fc(src)
  gain = (PhiFull(dst) - fc(dst)) - (PhiFull(src) - fc(src))

Then empirically, for n = 9,10,11,12:

  1. gain <= 1 always
  2. gain = 1 implies dfc = -2
  3. dfc >= 0 implies gain < 0

Together these imply:

  dphi = dfc + gain < 0

which is the positive bridge theorem on the tested sizes.
"""

from __future__ import annotations

import sys
from collections import Counter, defaultdict
from itertools import product

import cphi_bridge_exact_scan as scan
from cup2_theorem import build_system


def check_n(n: int):
    ms, fs = build_system(n)
    good = scan.explicit_good_cycle_configs(n)
    bad = [c for c in product(*(range(m) for m in ms)) if c not in good]
    bad_set = set(bad)

    def tp(c):
        return (scan.exp2_count(c, n), scan.int_21(c, n), scan.exp2_weight(c, n))

    fc_cache = {c: scan.fc(c, n) for c in bad}
    tp_cache = {c: tp(c) for c in bad}
    tp_fwd = defaultdict(list)
    for c in bad:
        for i in range(n):
            L, S, R = c[(i - 1) % n], c[i], c[(i + 1) % n]
            out = fs[i](L, S, R)
            if out == S:
                continue
            d = list(c)
            d[i] = out
            d = tuple(d)
            if d in bad_set and tp_cache.get(d) == tp_cache[c]:
                tp_fwd[c].append((d, scan.fc(d, n) - fc_cache[c]))

    g = {c: 0 for c in bad}
    for _ in range(2 * n + 10):
        changed = False
        for c in bad:
            best = g[c]
            for d, dfc in tp_fwd[c]:
                cand = dfc + g[d]
                if cand > best:
                    best = cand
            if best != g[c]:
                g[c] = best
                changed = True
        if not changed:
            break

    phi = {c: fc_cache[c] + g[c] for c in bad}

    law1 = True
    law2 = True
    law3 = True
    pairs = Counter()

    for c in bad:
        for i in (0, 1, 2, n - 3, n - 2, n - 1):
            L, S, R = c[(i - 1) % n], c[i], c[(i + 1) % n]
            out = fs[i](L, S, R)
            if out == S:
                continue
            d = list(c)
            d[i] = out
            d = tuple(d)
            if d not in bad_set or tp_cache.get(d) != tp_cache[c]:
                continue
            if scan.encode6(scan.boundary6(c, n)) == scan.encode6(scan.boundary6(d, n)):
                continue
            if (scan.encode6(scan.boundary6(c, n)), scan.encode6(scan.boundary6(d, n))) in scan.EDGE_617:
                continue

            dfc = scan.fc(d, n) - fc_cache[c]
            gain = (phi[d] - scan.fc(d, n)) - (phi[c] - fc_cache[c])
            pairs[(dfc, gain)] += 1

            if gain > 1:
                law1 = False
            if gain == 1 and dfc != -2:
                law2 = False
            if dfc >= 0 and gain >= 0:
                law3 = False

    print(f"\n=== n={n} ===")
    print(f"law1 gain<=1: {law1}")
    print(f"law2 gain=1 -> dfc=-2: {law2}")
    print(f"law3 dfc>=0 -> gain<0: {law3}")
    print(f"(dfc, gain) pairs: {sorted(pairs.items())}")


def main():
    if len(sys.argv) > 1:
        ns = [int(x) for x in sys.argv[1:]]
    else:
        ns = [9, 10, 11, 12]
    for n in ns:
        check_n(n)


if __name__ == "__main__":
    main()
