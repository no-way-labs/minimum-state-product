#!/usr/bin/env python3
"""
Boundary-successor view of active boundary steps.

For a chosen n:
1. enumerate deterministic boundary successors from source boundary 6-tuple
   and boundary mover (plus seam value for p=2/n-3)
2. mark which such boundary transitions are in 617
3. scan realized TP-preserving bad boundary-changing steps and attach Phi deltas
   to those boundary buckets

This is meant to expose the exact structural statement:
non-617 boundary successors only occur on Phi-dropping active realizations.
"""

import ast
import os
import re
import sys
from collections import Counter, defaultdict
from itertools import product

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


def deep_copy_sites(c, n):
    return [k for k in range(4, n - 3) if c[k] == c[k - 1] or c[k] == c[k + 1]]


def boundary_successor(fs, n, b6, mover, seam=None):
    c0, c1, c2, cN3, cN2, cN1 = b6
    out = list(b6)
    if mover == 0:
        out[0] = fs[0](cN1, c0, c1)
    elif mover == 1:
        out[1] = fs[1](c0, c1, c2)
    elif mover == 2:
        out[2] = fs[2](c1, c2, seam)
    elif mover == n - 3:
        out[3] = fs[n - 3](seam, cN3, cN2)
    elif mover == n - 2:
        out[4] = fs[n - 2](cN3, cN2, cN1)
    elif mover == n - 1:
        out[5] = fs[n - 1](cN2, cN1, c0)
    else:
        raise ValueError(mover)
    return tuple(out)


def analyze(n):
    ms, fs = build_system(n)
    good_set = good_cycle_configs(n)
    all_cfgs = list(product(*(range(m) for m in ms)))
    bad_list = [c for c in all_cfgs if c not in good_set]
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

    boundary_movers = [0, 1, 2, n - 3, n - 2, n - 1]
    all_b6 = [
        (c0, c1, c2, cN3, cN2, cN1)
        for c0 in range(2)
        for c1 in range(3)
        for c2 in range(3)
        for cN3 in range(3)
        for cN2 in range(3)
        for cN1 in range(2)
    ]

    print(f"n={n}")
    print("\nDeterministic boundary successor counts:")
    for mover in boundary_movers:
        seam_values = [None] if mover not in (2, n - 3) else [0, 1, 2]
        total = 0
        non617 = 0
        for b6 in all_b6:
            for seam in seam_values:
                dst_b6 = boundary_successor(fs, n, b6, mover, seam)
                total += 1
                if (encode6(b6), encode6(dst_b6)) not in EDGE_617:
                    non617 += 1
        print(f"  mover={mover}: total buckets={total}, non617 buckets={non617}")

    bucket_phi = defaultdict(Counter)
    bucket_count = Counter()
    for src in bad_list:
        src_b6 = b6_cache[src]
        src_phi = phi[src]
        for dst, mover, _ in tp_fwd[src]:
            if mover not in boundary_movers:
                continue
            dst_b6 = b6_cache[dst]
            if dst_b6 == src_b6:
                continue
            sites = deep_copy_sites(dst, n)
            if not sites:
                continue
            seam = None
            if mover == 2:
                seam = src[3]
            elif mover == n - 3:
                seam = src[n - 4]
            key = (encode6(src_b6), mover, seam, encode6(dst_b6))
            bucket_count[key] += 1
            bucket_phi[key][src_phi - phi[dst]] += 1

    print("\nSample non617 realized buckets with Phi drops:")
    shown = 0
    for (src_code, mover, seam, dst_code), cnt in sorted(bucket_count.items()):
        if (src_code, dst_code) in EDGE_617:
            continue
        print(
            f"  src={src_code} mover={mover} seam={seam} dst={dst_code} "
            f"count={cnt} phiDrops={dict(bucket_phi[(src_code, mover, seam, dst_code)])}"
        )
        shown += 1
        if shown >= 20:
            break


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    analyze(n)
