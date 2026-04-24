#!/usr/bin/env python3
"""
Split the explicit-bad non-617 no-drop boundary-changing class into:

  - active: destination has a deep copy pair
  - passive: destination has no deep copy pair

This is the exact bridge-facing question suggested by the existing
`PhiFull10.passiveCheck10` / `PhiFull11.activeCheck11` base files.

If the active count is zero, then the positive bridge reduces entirely to the
passive/no-copy theorem.
"""

from __future__ import annotations

import sys
from collections import Counter, defaultdict

import cphi_bridge_exact_scan as scan
import non617_tp_profile as prof


def has_deep_copy_pair(c, n: int) -> bool:
    return any(c[k] == c[k - 1] or c[k] == c[k + 1] for k in range(4, n - 3))


def split_n(n: int):
    bad, bad_set, tp_cache, fc_cache, phi, fs = prof.explicit_phi_data(n)

    total = 0
    active = 0
    passive = 0
    active_movers = Counter()
    passive_movers = Counter()
    active_samples = []
    passive_samples = []

    by_kind = defaultdict(set)

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

            src6 = scan.encode6(scan.boundary6(c, n))
            dst6 = scan.encode6(scan.boundary6(d, n))
            if src6 == dst6:
                continue
            if (src6, dst6) in scan.EDGE_617:
                continue
            if phi[d] != phi[c]:
                continue

            total += 1
            if has_deep_copy_pair(d, n):
                active += 1
                active_movers[i] += 1
                by_kind["active"].add((src6, dst6))
                if len(active_samples) < 10:
                    active_samples.append((c, d, i, (src6, dst6)))
            else:
                passive += 1
                passive_movers[i] += 1
                by_kind["passive"].add((src6, dst6))
                if len(passive_samples) < 10:
                    passive_samples.append((c, d, i, (src6, dst6)))

    print(f"\n=== n={n} ===")
    print(f"total non617 no-drop boundary-changing steps: {total}")
    print(f"active:  {active}  distinct_edges={len(by_kind['active'])}  movers={dict(sorted(active_movers.items()))}")
    print(f"passive: {passive}  distinct_edges={len(by_kind['passive'])}  movers={dict(sorted(passive_movers.items()))}")
    if active_samples:
        print("sample active witnesses:")
        for c, d, i, edge in active_samples:
            print(f"  mover={i} edge={edge}")
            print(f"    src={c}")
            print(f"    dst={d}")
    if passive_samples:
        print("sample passive witnesses:")
        for c, d, i, edge in passive_samples:
            print(f"  mover={i} edge={edge}")
            print(f"    src={c}")
            print(f"    dst={d}")


def main():
    if len(sys.argv) > 1:
        ns = [int(x) for x in sys.argv[1:]]
    else:
        ns = [9, 10, 11, 12]
    for n in ns:
        split_n(n)


if __name__ == "__main__":
    main()
