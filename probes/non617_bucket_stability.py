#!/usr/bin/env python3
"""
Check stability of the non-617 TP-preserving bad boundary-changing bucket set.

Bucket key:
  (mover_tag, local_signature, local_fc_delta, global_phi_delta)

where:
  mover_tag      ∈ {P0, P1, P2, PN3, PN2, PN1}
  local_signature = (L, S, R) seen by that mover
  local_fc_delta  = fc(dst) - fc(src)
  global_phi_delta = PhiFull(dst) - PhiFull(src)

The key RA question is whether the excluded non-617 class is described by a
fixed finite local bucket set independent of n. Empirically it is:
the bucket set is identical for n = 9,10,11,12 and has cardinality 43.
"""

from __future__ import annotations

import sys
from collections import defaultdict
from itertools import product

import cphi_bridge_exact_scan as scan
from cup2_theorem import build_system


def bucket_set(n: int):
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

    def tag(i: int):
        return "P0" if i == 0 else \
            "P1" if i == 1 else \
            "P2" if i == 2 else \
            "PN3" if i == n - 3 else \
            "PN2" if i == n - 2 else \
            "PN1"

    def sig(c, i: int):
        return (c[(i - 1) % n], c[i], c[(i + 1) % n])

    out = set()
    for c in bad:
        for i in (0, 1, 2, n - 3, n - 2, n - 1):
            L, S, R = c[(i - 1) % n], c[i], c[(i + 1) % n]
            outv = fs[i](L, S, R)
            if outv == S:
                continue
            d = list(c)
            d[i] = outv
            d = tuple(d)
            if d in bad_set and tp_cache.get(d) == tp_cache[c]:
                if scan.encode6(scan.boundary6(c, n)) == scan.encode6(scan.boundary6(d, n)):
                    continue
                if (scan.encode6(scan.boundary6(c, n)), scan.encode6(scan.boundary6(d, n))) in scan.EDGE_617:
                    continue
                out.add((tag(i), sig(c, i), scan.fc(d, n) - fc_cache[c], phi[d] - phi[c]))
    return out


def main():
    if len(sys.argv) > 1:
        ns = [int(x) for x in sys.argv[1:]]
    else:
        ns = [9, 10, 11, 12]

    base = None
    base_n = None
    for n in ns:
        b = bucket_set(n)
        print(f"n={n}: bucket_count={len(b)}")
        if base is None:
            base = b
            base_n = n
        else:
            same = (b == base)
            print(f"  same_as_n={base_n}: {same}")
            print(f"  only_here={len(b - base)} missing={len(base - b)}")
            if not same:
                print(f"  sample only_here={sorted(list(b - base))[:10]}")
                print(f"  sample missing={sorted(list(base - b))[:10]}")


if __name__ == "__main__":
    main()
