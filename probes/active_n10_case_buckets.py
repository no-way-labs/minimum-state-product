#!/usr/bin/env python3
"""
Enumerate the n=10 active structural buckets.

For each pair:
  - mover in {0,1,2,7,8,9}
  - deep copy-pair site k in {4,5,6}

collect all TP-preserving bad boundary-changing steps src -> dst such that
dst has a copy pair at site k, then report:
  - total step count in the bucket
  - distinct boundary transitions
  - whether every realized transition lands in the 617 set

Also compute the same bucketization restricted to no-drop steps
`PhiFull(dst) = PhiFull(src)`, since that is the actual witness class.

This is discovery-only support for the structural n=10 active base theorem.
"""

import ast
import os
import re
import sys
from collections import defaultdict
from itertools import product as cartesian

sys.path.insert(0, os.path.dirname(__file__))
from cup2_final_verify import build_system


ROOT = os.path.dirname(__file__)
N = 10
BOUNDARY_MOVERS = (0, 1, 2, 7, 8, 9)
COPY_SITES = (4, 5, 6)


def load_edge_617():
    path = os.path.join(ROOT, "check_boundary_edges.py")
    with open(path, "r") as f:
        content = f.read()
    m = re.search(r"sixTupleEdgeVals = \[(.*?)\]\n", content, re.S)
    if not m:
        raise RuntimeError("Could not parse 617 edge set")
    return set(ast.literal_eval("[" + m.group(1) + "]"))


EDGE_617 = load_edge_617()


def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)


def int_20(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)


def exp2_count(c, n):
    return int_20(c, n) + int_21(c, n)


def intj_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)


def intj_21(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)


def exp2_weight(c, n):
    return intj_20(c, n) + intj_21(c, n)


def tp_triple(c, n):
    return (exp2_count(c, n), int_21(c, n), exp2_weight(c, n))


def boundary6(c, n):
    return (c[0], c[1], c[2], c[n - 3], c[n - 2], c[n - 1])


def encode6(t6):
    return ((((t6[0] * 3 + t6[1]) * 3 + t6[2]) * 3 + t6[3]) * 3 + t6[4]) * 2 + t6[5]


def cup2CycleVal(n, t, j):
    if t < n:
        return 1 if j < t else 0
    if t < 2 * n - 2:
        if j < 2 * n - 1 - t:
            return 1
        if j < n - 1:
            return 2
        return 1
    if t == 2 * n - 2:
        if j == 0:
            return 1
        if j < n - 1:
            return 2
        return 1
    k = t - (2 * n - 2)
    if k == 0:
        if j == 0:
            return 1
        if j < n - 1:
            return 2
        return 1
    if j < k:
        return 0
    if j < n - 1:
        return 2
    return 1


def cycle_config(n, t):
    return tuple(cup2CycleVal(n, t, j) for j in range(n))


def good_cycle_configs(n):
    return {cycle_config(n, t) for t in range(3 * n - 2)}


def deep_copy_at_site(c, k):
    return c[k] == c[k - 1] or c[k] == c[k + 1]


def main():
    ms, fs = build_system(N)
    good_set = good_cycle_configs(N)
    all_cfgs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_cfgs if c not in good_set]
    bad_set = set(bad_list)

    fc_cache = {}
    tp_cache = {}
    b6_cache = {c: boundary6(c, N) for c in bad_list}
    tp_fwd = {c: [] for c in bad_list}
    for c in bad_list:
        fc_cache[c] = sum(1 for j in range(N) if c[j] != c[(j + 1) % N])
        tp_cache[c] = tp_triple(c, N)

    def mk_buckets():
        return {
            (mover, site): {
                "steps": 0,
                "edges": set(),
                "edge_examples": {},
                "non617_edges": set(),
                "non617_examples": {},
            }
            for mover in BOUNDARY_MOVERS
            for site in COPY_SITES
        }

    buckets_all = mk_buckets()
    buckets_nodrop = mk_buckets()

    total_structural_steps = 0
    for src in bad_list:
        src_tp = tp_cache[src]
        for mover in BOUNDARY_MOVERS:
            L, S, R = src[(mover - 1) % N], src[mover], src[(mover + 1) % N]
            out = fs[mover](L, S, R)
            if out == S:
                continue
            dst = list(src)
            dst[mover] = out
            dst = tuple(dst)
            if dst not in bad_set:
                continue
            if tp_triple(dst, N) != src_tp:
                continue
            tp_fwd[src].append((dst, mover, fc_cache[dst] - fc_cache[src]))

    g = {c: 0 for c in bad_list}
    for _ in range(2 * N + 20):
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

    for src in bad_list:
        src_b6 = b6_cache[src]
        src_code = encode6(src_b6)
        src_phi = phi[src]
        for dst, mover, _ in tp_fwd[src]:
            dst_b6 = b6_cache[dst]
            if dst_b6 == src_b6:
                continue
            total_structural_steps += 1
            dst_code = encode6(dst_b6)
            edge = (src_code, dst_code)
            in_617 = edge in EDGE_617
            nodrop = (phi[dst] == src_phi)
            for site in COPY_SITES:
                if not deep_copy_at_site(dst, site):
                    continue
                for buckets in (buckets_all, buckets_nodrop) if nodrop else (buckets_all,):
                    info = buckets[(mover, site)]
                    info["steps"] += 1
                    info["edges"].add(edge)
                    info["edge_examples"].setdefault(edge, (src, dst))
                    if not in_617:
                        info["non617_edges"].add(edge)
                        info["non617_examples"].setdefault(edge, (src, dst))

    def dump(title, buckets):
        print(title)
        all_good = True
        for mover in BOUNDARY_MOVERS:
            for site in COPY_SITES:
                info = buckets[(mover, site)]
                edge_count = len(info["edges"])
                bad_edge_count = len(info["non617_edges"])
                if bad_edge_count:
                    all_good = False
                print(
                    f"mover={mover} site={site}: "
                    f"steps={info['steps']}, "
                    f"distinct_edges={edge_count}, "
                    f"all_in_617={'YES' if bad_edge_count == 0 else 'NO'}"
                )
                if bad_edge_count:
                    for edge in sorted(info["non617_edges"])[:5]:
                        src, dst = info["non617_examples"][edge]
                        print(f"  non617 edge={edge} src={src} dst={dst}")
        print()
        print(f"{title} verdict: {'ALL BUCKETS SUBSET 617' if all_good else 'SOME BUCKET HAS NON617 EDGE'}")
        print()

    print(f"n={N}")
    print(f"bad configs: {len(bad_list)}")
    print(f"TP-preserving bad boundary-changing steps with boundary mover: {total_structural_steps}")
    print()
    dump("Broad active buckets", buckets_all)
    dump("No-drop active buckets", buckets_nodrop)


if __name__ == "__main__":
    main()
