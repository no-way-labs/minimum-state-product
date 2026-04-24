#!/usr/bin/env python3
"""
Profile the realized explicit-CΦ boundary-changing edges by mover.

For each tested n, this script reports:
  - how many realized boundary-changing CΦ steps occur at each boundary mover
  - how many distinct encoded 6-tuple transitions each mover realizes
  - which movers realize the two SCC-subrank edges
  - whether the missing Lean edge 239->245 is ever realized (it should not be)

This is an RA support tool for freezing the exact bridge theorem shape.
"""

from __future__ import annotations

import sys
from collections import Counter, defaultdict

import cphi_bridge_exact_scan as scan


def profile_n(n: int):
    data = scan.compute_cphi_boundary_edges(n, "explicit")
    ms, fs = scan.build_system(n)
    good = scan.explicit_good_cycle_configs(n)
    bad = [c for c in scan.cartesian(*(range(m) for m in ms)) if c not in good]
    badset = set(bad)

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
            if d in badset and tp_cache.get(d) == tp_cache[c]:
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

    by_mover_steps = Counter()
    by_mover_edges = defaultdict(set)
    scc_edges = defaultdict(set)
    missing_239_245 = []

    for c in bad:
        for mover in range(n):
            L, S, R = c[(mover - 1) % n], c[mover], c[(mover + 1) % n]
            out = fs[mover](L, S, R)
            if out == S:
                continue
            d = list(c)
            d[mover] = out
            d = tuple(d)
            if d not in badset or tp_cache.get(d) != tp_cache[c] or phi.get(d) != phi[c]:
                continue
            bc = scan.boundary6(c, n)
            bd = scan.boundary6(d, n)
            if bc == bd:
                continue
            enc = (scan.encode6(bc), scan.encode6(bd))
            by_mover_steps[mover] += 1
            by_mover_edges[mover].add(enc)
            if enc in {(245, 251), (251, 239)}:
                scc_edges[mover].add(enc)
            if enc == (239, 245):
                missing_239_245.append((c, d, mover))

    print(f"\n=== n={n} ===")
    print(f"realized explicit-CΦ boundary transitions: {len(data['trans'])}")
    for mover in sorted(by_mover_steps):
        print(
            f"  mover={mover}: steps={by_mover_steps[mover]}, "
            f"distinct_edges={len(by_mover_edges[mover])}, "
            f"scc_edges={sorted(scc_edges[mover])}"
        )
    print(f"  realized 239->245 witnesses: {len(missing_239_245)}")
    if missing_239_245:
        c, d, mover = missing_239_245[0]
        print(f"    sample mover={mover} src={c} dst={d}")


def main():
    if len(sys.argv) > 1:
        ns = [int(x) for x in sys.argv[1:]]
    else:
        ns = [9, 10, 11, 12]
    for n in ns:
        profile_n(n)


if __name__ == "__main__":
    main()
