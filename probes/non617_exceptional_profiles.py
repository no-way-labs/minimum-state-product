#!/usr/bin/env python3
"""
Compress the pointwise correction-increase classes into profile groups.

Input:
  the explicit-bad non-617 TP-preserving bad boundary-changing class table
  from `non617_class_table.py`

Output:
  the exceptional classes where pointwise correction gain

    (PhiFull(dst)-fc(dst)) - (PhiFull(src)-fc(src))

  can equal +1, grouped by exact quantitative profile.

Empirically at n=9 the 11 true exceptional classes collapse to 7 profile
groups, and every exceptional class already has local `dfc = -2`.
"""

from __future__ import annotations

from collections import defaultdict
from itertools import product

import cphi_bridge_exact_scan as scan
from cup2_theorem import build_system


def main():
    n = 9
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

    exceptional = defaultdict(lambda: {
        "dfc": set(),
        "dphi": set(),
        "src_delta": set(),
        "dst_delta": set(),
        "gain": set(),
    })

    for c in bad:
        for i in (0, 1, 2, n - 3, n - 2, n - 1):
            out = fs[i](c[(i - 1) % n], c[i], c[(i + 1) % n])
            if out == c[i]:
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
            gain = (phi[d] - scan.fc(d, n)) - (phi[c] - fc_cache[c])
            if gain > 0:
                key = (tag(i), sig(c, i))
                info = exceptional[key]
                info["dfc"].add(scan.fc(d, n) - fc_cache[c])
                info["dphi"].add(phi[d] - phi[c])
                info["src_delta"].add(phi[c] - fc_cache[c])
                info["dst_delta"].add(phi[d] - scan.fc(d, n))
                info["gain"].add(gain)

    by_profile = defaultdict(list)
    for k, prof in exceptional.items():
        by_profile[(
            tuple(sorted(prof["dfc"])),
            tuple(sorted(prof["dphi"])),
            tuple(sorted(prof["src_delta"])),
            tuple(sorted(prof["dst_delta"])),
            tuple(sorted(prof["gain"])),
        )].append(k)

    print(f"exceptional_class_count={len(exceptional)}")
    print(f"profile_group_count={len(by_profile)}")
    for prof, ks in by_profile.items():
        print()
        print(f"classes={ks}")
        print(f"profile={prof}")


if __name__ == "__main__":
    main()
