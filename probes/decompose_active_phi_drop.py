#!/usr/bin/env python3
"""
For broad active non617 boundary-changing TP-preserving bad steps, compare:
  - Phi drop
  - immediate deltas of (Exp2Count, Int21Count, Exp2Weight)
  - immediate delta of fc

Goal: determine whether the Phi drop is visible in the TP components or only in
the future structure.
"""

import os
import sys
from collections import Counter
from itertools import product

sys.path.insert(0, os.path.dirname(__file__))
from active_non617_scan_fast import (
    build_system,
    good_cycle_configs,
    tp_triple,
    fc,
    boundary6,
    encode6,
    has_deep_copy_pair,
    EDGE_617,
    exp2_count,
    int_21,
    exp2_weight,
)


def analyze(n):
    ms, fs = build_system(n)
    good_set = good_cycle_configs(n)
    bad_list = [c for c in product(*(range(m) for m in ms)) if c not in good_set]
    bad_set = set(bad_list)

    fc_cache = {c: fc(c, n) for c in bad_list}
    tp_cache = {c: tp_triple(c, n) for c in bad_list}
    b6_cache = {c: boundary6(c, n) for c in bad_list}

    tp_fwd = {c: [] for c in bad_list}
    for c in bad_list:
        tc = tp_cache[c]
        for mover in range(n):
            L, S, R = c[(mover - 1) % n], c[mover], c[(mover + 1) % n]
            out = fs[mover](L, S, R)
            if out == S:
                continue
            d = list(c)
            d[mover] = out
            d = tuple(d)
            if d not in bad_set:
                continue
            if tp_triple(d, n) != tc:
                continue
            tp_fwd[c].append((d, mover, fc_cache[d] - fc_cache[c]))

    g = {c: 0 for c in bad_list}
    for _ in range(2 * n + 20):
        changed = False
        for c in bad_list:
            best = g[c]
            for d, _, dfc in tp_fwd[c]:
                cand = dfc + g[d]
                if cand > best:
                    best = cand
            if best != g[c]:
                g[c] = best
                changed = True
        if not changed:
            break
    phi = {c: fc_cache[c] + g[c] for c in bad_list}

    boundary_movers = {0, 1, 2, n - 3, n - 2, n - 1}

    phi_drop_ctr = Counter()
    fc_delta_ctr = Counter()
    exp2_delta_ctr = Counter()
    int21_delta_ctr = Counter()
    weight_delta_ctr = Counter()
    samples = []

    for src in bad_list:
        src_code = encode6(b6_cache[src])
        src_phi = phi[src]
        for dst, mover, dfc in tp_fwd[src]:
            if mover not in boundary_movers:
                continue
            if b6_cache[dst] == b6_cache[src]:
                continue
            if not has_deep_copy_pair(dst, n):
                continue
            dst_code = encode6(b6_cache[dst])
            if (src_code, dst_code) in EDGE_617:
                continue
            pdrop = src_phi - phi[dst]
            phi_drop_ctr[pdrop] += 1
            fc_delta_ctr[dfc] += 1
            exp2_delta_ctr[exp2_count(dst, n) - exp2_count(src, n)] += 1
            int21_delta_ctr[int_21(dst, n) - int_21(src, n)] += 1
            weight_delta_ctr[exp2_weight(dst, n) - exp2_weight(src, n)] += 1
            if len(samples) < 10:
                samples.append((src, dst, mover, pdrop, dfc))

    print(f"n={n}")
    print("phi drops:", dict(phi_drop_ctr))
    print("fc deltas:", dict(fc_delta_ctr))
    print("exp2Count deltas:", dict(exp2_delta_ctr))
    print("int21 deltas:", dict(int21_delta_ctr))
    print("exp2Weight deltas:", dict(weight_delta_ctr))
    print("\nsamples:")
    for src, dst, mover, pdrop, dfc in samples:
        print(f"  mover={mover} phi_drop={pdrop} dfc={dfc}")
        print(f"    src={src}")
        print(f"    dst={dst}")


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    analyze(n)
