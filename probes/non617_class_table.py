#!/usr/bin/env python3
"""
Compressed class table for explicit-bad non-617 TP-preserving boundary-changing steps.

This compresses the stable 43-bucket system further by forgetting exact
`local_fc_delta` and `global_phi_delta` buckets and grouping by:

    (mover_tag, local_signature)

For each class it records the observed ranges of:
  - local fc delta
  - global PhiFull delta
  - source PhiFull-fc correction
  - destination PhiFull-fc correction

Empirically, the class set is stable across n = 9,10,11,12 and has size 26.
This is likely the right finite local target for an analytic proof of the
positive bridge.
"""

from __future__ import annotations

import sys
from collections import defaultdict
from itertools import product

import cphi_bridge_exact_scan as scan
from cup2_theorem import build_system


def class_table(n: int):
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

    out = defaultdict(lambda: {
        "count": 0,
        "dfc": set(),
        "dphi": set(),
        "src_delta": set(),
        "dst_delta": set(),
    })

    for c in bad:
        for i in (0, 1, 2, n - 3, n - 2, n - 1):
            L, S, R = c[(i - 1) % n], c[i], c[(i + 1) % n]
            outv = fs[i](L, S, R)
            if outv == S:
                continue
            d = list(c)
            d[i] = outv
            d = tuple(d)
            if d not in bad_set or tp_cache.get(d) != tp_cache[c]:
                continue
            if scan.encode6(scan.boundary6(c, n)) == scan.encode6(scan.boundary6(d, n)):
                continue
            if (scan.encode6(scan.boundary6(c, n)), scan.encode6(scan.boundary6(d, n))) in scan.EDGE_617:
                continue

            key = (tag(i), sig(c, i))
            out[key]["count"] += 1
            out[key]["dfc"].add(scan.fc(d, n) - fc_cache[c])
            out[key]["dphi"].add(phi[d] - phi[c])
            out[key]["src_delta"].add(phi[c] - fc_cache[c])
            out[key]["dst_delta"].add(phi[d] - scan.fc(d, n))

    return out


def print_table(n: int):
    table = class_table(n)
    print(f"\n=== n={n} ===")
    print(f"class_count={len(table)}")
    for key, info in sorted(table.items()):
        print(
            f"{key}: count={info['count']} "
            f"dfc={sorted(info['dfc'])} "
            f"dphi={sorted(info['dphi'])} "
            f"srcδ={sorted(info['src_delta'])} "
            f"dstδ={sorted(info['dst_delta'])}"
        )
    return table


def main():
    if len(sys.argv) > 1:
        ns = [int(x) for x in sys.argv[1:]]
    else:
        ns = [9]

    base = None
    base_n = None
    for n in ns:
        table = print_table(n)
        if base is None:
            base = table
            base_n = n
        else:
            same_keys = set(table) == set(base)
            print(f"same class keys as n={base_n}: {same_keys}")
            print(f"  only_here={len(set(table) - set(base))} missing={len(set(base) - set(table))}")


if __name__ == "__main__":
    main()
