#!/usr/bin/env python3
"""
Scan the no-drop active witness buckets for n = 11..15.

For each n and each bucket:
  - mover in {0,1,2,n-3,n-2,n-1}
  - deep copy-pair site k in {4,...,n-4}

collect all TP-preserving bad boundary-changing no-drop steps src -> dst with
copy pair at site k, then report whether every realized boundary transition
lands in the 617 set.
"""

import ast
import os
import re
import sys
import time
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


def deep_copy_at_site(c, k):
    return c[k] == c[k - 1] or c[k] == c[k + 1]


def scan_n(n):
    t0 = time.time()
    ms, fs = build_system(n)
    good_set = good_cycle_configs(n)
    all_cfgs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_cfgs if c not in good_set]
    bad_set = set(bad_list)

    boundary_movers = (0, 1, 2, n - 3, n - 2, n - 1)
    copy_sites = tuple(range(4, n - 3))

    fc_cache = {}
    tp_cache = {}
    b6_cache = {}
    tp_fwd = {c: [] for c in bad_list}

    for c in bad_list:
      fc_cache[c] = fc(c, n)
      tp_cache[c] = tp_triple(c, n)
      b6_cache[c] = boundary6(c, n)

    for idx, c in enumerate(bad_list, start=1):
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
        if idx % 200000 == 0:
            print(f"n={n}: built TP edges for {idx}/{len(bad_list)} bad configs ({time.time() - t0:.1f}s)")

    g = {c: 0 for c in bad_list}
    for iteration in range(2 * n + 20):
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
        print(f"n={n}: PhiFull iteration {iteration + 1} ({time.time() - t0:.1f}s)")
        if not changed:
            break
    phi = {c: fc_cache[c] + g[c] for c in bad_list}

    buckets = {
        (mover, site): {
            "steps": 0,
            "edges": set(),
            "bad_edges": set(),
            "first_bad": None,
        }
        for mover in boundary_movers
        for site in copy_sites
    }

    total_nodrop_active = 0
    for src in bad_list:
        src_b6 = b6_cache[src]
        src_code = encode6(src_b6)
        src_phi = phi[src]
        for dst, mover, _ in tp_fwd[src]:
            if mover not in boundary_movers:
                continue
            dst_b6 = b6_cache[dst]
            if dst_b6 == src_b6:
                continue
            if phi[dst] != src_phi:
                continue
            dst_code = encode6(dst_b6)
            edge = (src_code, dst_code)
            in_617 = edge in EDGE_617
            for site in copy_sites:
                if not deep_copy_at_site(dst, site):
                    continue
                total_nodrop_active += 1
                info = buckets[(mover, site)]
                info["steps"] += 1
                info["edges"].add(edge)
                if not in_617:
                    info["bad_edges"].add(edge)
                    if info["first_bad"] is None:
                        info["first_bad"] = (src, dst, edge)

    print(f"\n=== n={n} ===")
    print(f"bad configs: {len(bad_list)}")
    print(f"no-drop active bucket memberships counted: {total_nodrop_active}")
    all_good = True
    for mover in boundary_movers:
        for site in copy_sites:
            info = buckets[(mover, site)]
            ok = not info["bad_edges"]
            all_good = all_good and ok
            print(
                f"mover={mover} site={site}: "
                f"steps={info['steps']}, "
                f"distinct_edges={len(info['edges'])}, "
                f"all_in_617={'YES' if ok else 'NO'}"
            )
            if not ok:
                src, dst, edge = info["first_bad"]
                print(f"  first_bad edge={edge} src={src} dst={dst}")
    print(f"n={n} verdict: {'ALL BUCKETS SUBSET 617' if all_good else 'SOME BUCKET HAS NON617 EDGE'}")
    print(f"elapsed: {time.time() - t0:.1f}s\n")
    return all_good


def main():
    ns = [int(x) for x in sys.argv[1:]] if len(sys.argv) > 1 else [11, 12, 13, 14, 15]
    overall = True
    for n in ns:
        overall = scan_n(n) and overall
    print(f"GLOBAL verdict over {ns}: {'ALL BUCKETS SUBSET 617' if overall else 'FOUND NON617 BUCKET'}")


if __name__ == "__main__":
    main()
