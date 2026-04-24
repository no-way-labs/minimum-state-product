#!/usr/bin/env python3
"""
Finite proof split for the positive bridge.

Using the explicit-bad non-617 TP-preserving bad boundary-changing class,
partition the stable 26 local classes into:

1. Easy classes:
   local_fc_delta < 0 always, and correction_gain <= 0 always
2. Nonnegative-fc classes:
   local_fc_delta >= 0 is possible, but correction_gain < 0 always
3. Exceptional classes:
   correction_gain = 1 is possible

Then compress the exceptional classes by their exact quantitative profile.

Empirically this yields the stable split:

  - 12 easy classes
  - 3 nonnegative-fc classes
  - 11 exceptional classes = 4 profile groups

for n = 9,10,11,12.
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

    table = defaultdict(lambda: {
        "dfc": set(),
        "dphi": set(),
        "src_delta": set(),
        "dst_delta": set(),
        "gain": set(),
        "count": 0,
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
            info = table[key]
            info["count"] += 1
            info["dfc"].add(scan.fc(d, n) - fc_cache[c])
            info["dphi"].add(phi[d] - phi[c])
            info["src_delta"].add(phi[c] - fc_cache[c])
            info["dst_delta"].add(phi[d] - scan.fc(d, n))
            info["gain"].add((phi[d] - scan.fc(d, n)) - (phi[c] - fc_cache[c]))

    return table


def classify(table):
    easy = {}
    nonneg = {}
    exceptional = {}

    for k, v in table.items():
        max_dfc = max(v["dfc"])
        max_gain = max(v["gain"])
        if max_gain > 0:
            exceptional[k] = v
        elif max_dfc >= 0:
            nonneg[k] = v
        else:
            easy[k] = v
    return easy, nonneg, exceptional


def exceptional_profiles(exceptional):
    by_profile = defaultdict(list)
    for k, v in exceptional.items():
        prof = (
            tuple(sorted(v["dfc"])),
            tuple(sorted(v["dphi"])),
            tuple(sorted(v["src_delta"])),
            tuple(sorted(v["dst_delta"])),
            tuple(sorted(v["gain"])),
        )
        by_profile[prof].append(k)
    return by_profile


def main():
    if len(sys.argv) > 1:
        ns = [int(x) for x in sys.argv[1:]]
    else:
        ns = [9, 10, 11, 12]

    base = None
    for n in ns:
        table = class_table(n)
        easy, nonneg, exceptional = classify(table)
        profs = exceptional_profiles(exceptional)

        summary = (
            tuple(sorted(easy)),
            tuple(sorted(nonneg)),
            tuple(sorted(exceptional)),
            tuple(sorted((prof, tuple(sorted(vals))) for prof, vals in profs.items())),
        )

        print(f"\n=== n={n} ===")
        print(f"class_count={len(table)}")
        print(f"easy_count={len(easy)}")
        print(f"nonneg_count={len(nonneg)}")
        print(f"exceptional_count={len(exceptional)}")
        print(f"exceptional_profile_count={len(profs)}")
        print(f"nonneg_classes={sorted(nonneg)}")

        if base is None:
            base = summary
        else:
            print(f"same split as n=9: {summary == base}")


if __name__ == "__main__":
    main()
