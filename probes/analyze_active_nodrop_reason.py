#!/usr/bin/env python3
"""
Discovery script for the structural reason behind active_noDrop_subset_G617.

For a given n, compare:
  - broad active boundary-changing TP-preserving bad steps
  - no-drop active boundary-changing TP-preserving bad steps

and summarize what separates the non617 failures from the no-drop-success class.
"""

import ast
import os
import re
import sys
import time
from collections import Counter, defaultdict
from itertools import product as cartesian

sys.path.insert(0, os.path.dirname(__file__))
from cup2_final_verify import build_system


ROOT = os.path.dirname(__file__)


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


def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


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


def site_class(n, k):
    if k == 4:
        return "left"
    if k == n - 4:
        return "right"
    return "mid"


def deep_copy_sites(c, n):
    return [k for k in range(4, n - 3) if c[k] == c[k - 1] or c[k] == c[k + 1]]


def analyze(n):
    t0 = time.time()
    ms, fs = build_system(n)
    good_set = good_cycle_configs(n)
    bad_list = [c for c in cartesian(*(range(m) for m in ms)) if c not in good_set]
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

    broad_non617_phi_drop = Counter()
    broad_non617_fc_delta = Counter()
    broad_non617_site = Counter()
    nodrop_site = Counter()
    nodrop_fc_delta = Counter()
    nodrop_mover = Counter()
    broad_non617_examples = []

    for src in bad_list:
        src_b6 = b6_cache[src]
        src_code = encode6(src_b6)
        src_phi = phi[src]
        for dst, mover, dfc in tp_fwd[src]:
            if mover not in boundary_movers:
                continue
            dst_b6 = b6_cache[dst]
            if dst_b6 == src_b6:
                continue
            sites = deep_copy_sites(dst, n)
            if not sites:
                continue
            edge = (src_code, encode6(dst_b6))
            in617 = edge in EDGE_617
            if not in617:
                broad_non617_phi_drop[src_phi - phi[dst]] += 1
                broad_non617_fc_delta[dfc] += 1
                for k in sites:
                    broad_non617_site[(mover, site_class(n, k))] += 1
                if len(broad_non617_examples) < 20:
                    broad_non617_examples.append((src, dst, mover, dfc, src_phi - phi[dst], sites, edge))
            if phi[dst] == src_phi:
                for k in sites:
                    nodrop_site[(mover, site_class(n, k))] += 1
                nodrop_fc_delta[dfc] += 1
                nodrop_mover[mover] += 1

    print(f"n={n}, elapsed={time.time() - t0:.1f}s")
    print("\nBroad active non617 counts by Phi drop:")
    for k, v in broad_non617_phi_drop.most_common():
        print(f"  drop={k}: {v}")
    print("\nBroad active non617 counts by fc delta:")
    for k, v in broad_non617_fc_delta.most_common():
        print(f"  dfc={k}: {v}")
    print("\nBroad active non617 counts by (mover, site_class):")
    for k, v in broad_non617_site.most_common():
        print(f"  {k}: {v}")
    print("\nNo-drop active counts by mover:")
    for k, v in nodrop_mover.most_common():
        print(f"  mover={k}: {v}")
    print("\nNo-drop active counts by fc delta:")
    for k, v in nodrop_fc_delta.most_common():
        print(f"  dfc={k}: {v}")
    print("\nNo-drop active counts by (mover, site_class):")
    for k, v in nodrop_site.most_common():
        print(f"  {k}: {v}")
    print("\nSample broad non617 active examples:")
    for src, dst, mover, dfc, phidrop, sites, edge in broad_non617_examples:
        print(f"  mover={mover} dfc={dfc} phi_drop={phidrop} sites={sites} edge={edge}")
        print(f"    src={src}")
        print(f"    dst={dst}")


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    analyze(n)
