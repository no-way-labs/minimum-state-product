#!/usr/bin/env python3
"""
Check whether the Phi drop on broad active non617 boundary steps is determined
by the full active bucket key:

  (src boundary state, mover, seam value if needed, site class, dst boundary state)
"""

import sys
from collections import defaultdict
from itertools import product

sys.path.insert(0, "claude")
from active_non617_scan_fast import (
    build_system,
    good_cycle_configs,
    tp_triple,
    fc,
    boundary6,
    encode6,
    EDGE_617,
)


def site_classes(dst, n):
    out = set()
    for k in range(4, n - 3):
        if dst[k] == dst[k - 1] or dst[k] == dst[k + 1]:
            if k == 4:
                out.add("left")
            elif k == n - 4:
                out.add("right")
            else:
                out.add("mid")
    return out


def analyze(n=11):
    ms, fs = build_system(n)
    good_set = good_cycle_configs(n)
    bad = [c for c in product(*(range(m) for m in ms)) if c not in good_set]
    bad_set = set(bad)
    fc_cache = {c: fc(c, n) for c in bad}
    tp_cache = {c: tp_triple(c, n) for c in bad}
    b6_cache = {c: boundary6(c, n) for c in bad}
    tp_fwd = {c: [] for c in bad}
    for c in bad:
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

    g = {c: 0 for c in bad}
    for _ in range(2 * n + 20):
        changed = False
        for c in bad:
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
    phi = {c: fc_cache[c] + g[c] for c in bad}

    boundary_movers = {0, 1, 2, n - 3, n - 2, n - 1}
    bucket_drops = defaultdict(set)
    samples = {}

    for src in bad:
        src_code = encode6(b6_cache[src])
        for dst, mover, _ in tp_fwd[src]:
            if mover not in boundary_movers:
                continue
            dst_code = encode6(b6_cache[dst])
            if src_code == dst_code:
                continue
            if (src_code, dst_code) in EDGE_617:
                continue
            seam = None
            if mover == 2:
                seam = src[3]
            elif mover == n - 3:
                seam = src[n - 4]
            pdrop = phi[src] - phi[dst]
            for sc in site_classes(dst, n):
                key = (src_code, mover, seam, sc, dst_code)
                bucket_drops[key].add(pdrop)
                samples.setdefault(key, (src, dst, pdrop))

    nondet = [(k, v) for k, v in bucket_drops.items() if len(v) > 1]
    print(f"n={n}")
    print(f"non617 active buckets (full key): {len(bucket_drops)}")
    print(f"bucket-determined Phi drop? {'YES' if not nondet else 'NO'}")
    print(f"multi-drop buckets: {len(nondet)}")
    if nondet:
      print("\nSample multi-drop buckets:")
      for key, vals in nondet[:20]:
          src, dst, pdrop = samples[key]
          print(f"  key={key} drops={sorted(vals)} sample_drop={pdrop}")
          print(f"    src={src}")
          print(f"    dst={dst}")


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    analyze(n)
