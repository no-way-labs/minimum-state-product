#!/usr/bin/env python3
"""
Profile non-617 TP-preserving bad boundary-changing steps under explicit badness.

This is an RA support tool for the positive bridge:

    boundary-changing CΦ -> sixTupleEdge

Since CΦ means TP-preserving + bad + boundary-changing + no PhiFull drop,
this profiler examines the larger class where the edge is non-617 and records:
  - mover class
  - local boundary data seen by the mover
  - local fc delta
  - global PhiFull delta

If every non-617 class has PhiFull drop for simple local reasons, that is the
analytic route to the positive bridge.
"""

from __future__ import annotations

import sys
from collections import Counter, defaultdict
from itertools import product

import cphi_bridge_exact_scan as scan
from cup2_theorem import build_system


def explicit_phi_data(n: int):
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
    return bad, bad_set, tp_cache, fc_cache, phi, fs


def mover_tag(n: int, i: int) -> str:
    if i == 0:
        return "P0"
    if i == 1:
        return "P1"
    if i == 2:
        return "P2"
    if i == n - 3:
        return "PN3"
    if i == n - 2:
        return "PN2"
    if i == n - 1:
        return "PN1"
    raise ValueError(i)


def local_signature(n: int, c, i: int):
    if i == 0:
        return (c[n - 1], c[0], c[1])
    if i == 1:
        return (c[0], c[1], c[2])
    if i == 2:
        return (c[1], c[2], c[3])
    if i == n - 3:
        return (c[n - 4], c[n - 3], c[n - 2])
    if i == n - 2:
        return (c[n - 3], c[n - 2], c[n - 1])
    if i == n - 1:
        return (c[n - 2], c[n - 1], c[0])
    raise ValueError(i)


def profile_n(n: int):
    bad, bad_set, tp_cache, fc_cache, phi, fs = explicit_phi_data(n)

    bucket_counts = Counter()
    examples = {}
    no_drop_non617 = 0

    for c in bad:
        for i in range(n):
            if i not in (0, 1, 2, n - 3, n - 2, n - 1):
                continue
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
            edge = (scan.encode6(scan.boundary6(c, n)), scan.encode6(scan.boundary6(d, n)))
            if edge in scan.EDGE_617:
                continue
            tag = mover_tag(n, i)
            sig = local_signature(n, c, i)
            dfc = scan.fc(d, n) - fc_cache[c]
            dphi = phi[d] - phi[c]
            bucket = (tag, sig, dfc, dphi)
            bucket_counts[bucket] += 1
            examples.setdefault(bucket, (c, d, edge))
            if dphi == 0:
                no_drop_non617 += 1

    print(f"\n=== n={n} ===")
    print(f"non-617 TP-preserving bad boundary-changing steps: {sum(bucket_counts.values())}")
    print(f"non-617 TP-preserving bad no-drop steps: {no_drop_non617}")
    print(f"bucket count: {len(bucket_counts)}")
    for bucket, count in bucket_counts.most_common(20):
        c, d, edge = examples[bucket]
        print(f"  {bucket}: count={count}, edge={edge}")
        print(f"    src={c}")
        print(f"    dst={d}")


def main():
    if len(sys.argv) > 1:
        ns = [int(x) for x in sys.argv[1:]]
    else:
        ns = [9, 10, 11, 12]
    for n in ns:
        profile_n(n)


if __name__ == "__main__":
    main()
