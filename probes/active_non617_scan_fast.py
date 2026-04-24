#!/usr/bin/env python3
"""
Fast scan for non-617 active no-drop witnesses at a given n.

Goal:
- find whether there exist boundary-changing TP-preserving bad steps src -> dst
  with PhiFull(src) = PhiFull(dst),
  boundary edge not in 617,
  and dst has a deep copy-pair.

This does NOT try to prove path transport. It only finds the actual target
instances, if any, at a given size.
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


def has_deep_copy_pair(c, n):
    return any(c[k] == c[k - 1] or c[k] == c[k + 1] for k in range(4, n - 3))


def cup2CycleVal(n, t, j):
    if t < n:
        return 1 if j < t else 0
    elif t < 2 * n - 2:
        if j < 2 * n - 1 - t:
            return 1
        elif j < n - 1:
            return 2
        else:
            return 1
    elif t == 2 * n - 2:
        if j == 0:
            return 1
        elif j < n - 1:
            return 2
        else:
            return 1
    else:
        k = t - (2 * n - 2)
        if k == 0:
            if j == 0:
                return 1
            elif j < n - 1:
                return 2
            else:
                return 1
        else:
            if j < k:
                return 0
            elif j < n - 1:
                return 2
            else:
                return 1


def cycle_config(n, t):
    return tuple(cup2CycleVal(n, t, j) for j in range(n))


def good_cycle_configs(n):
    return {cycle_config(n, t) for t in range(3 * n - 2)}


def scan(n, limit_print=20):
    t0 = time.time()
    ms, fs = build_system(n)
    good_set = good_cycle_configs(n)

    total_configs = 1
    for m in ms:
        total_configs *= m

    bad_list = []
    t_bad = time.time()
    for idx, c in enumerate(cartesian(*(range(m) for m in ms)), start=1):
        if c not in good_set:
            bad_list.append(c)
        if idx % 500000 == 0:
            print(f"  scanned {idx}/{total_configs} configs for bad-state filter ({time.time() - t_bad:.1f}s)")
    bad_set = set(bad_list)

    print(f"n={n}")
    print(f"  total configs: {total_configs}")
    print(f"  bad configs:   {len(bad_list)}")

    fc_cache = {c: fc(c, n) for c in bad_list}
    tp_cache = {c: tp_triple(c, n) for c in bad_list}
    b6_cache = {c: boundary6(c, n) for c in bad_list}

    tp_fwd = {c: [] for c in bad_list}
    edge_count = 0

    t1 = time.time()
    for idx, c in enumerate(bad_list, start=1):
        tc = tp_cache[c]
        for i in range(n):
            L, S, R = c[(i - 1) % n], c[i], c[(i + 1) % n]
            out = fs[i](L, S, R)
            if out == S:
                continue
            d = list(c)
            d[i] = out
            d = tuple(d)
            if d not in bad_set:
                continue
            if tp_triple(d, n) != tc:
                continue
            edge_count += 1
            tp_fwd[c].append((d, i, fc_cache[d] - fc_cache[c]))
        if idx % 200000 == 0:
            print(f"  built TP edges for {idx}/{len(bad_list)} bad configs ({time.time() - t1:.1f}s)")
    print(f"  tp-preserving bad edges: {edge_count} ({time.time() - t1:.1f}s)")

    # PhiFull via fixpoint on g[c] = max additional gain over c.
    g = {c: 0 for c in bad_list}
    t2 = time.time()
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
        print(f"  PhiFull iteration {iteration + 1} complete ({time.time() - t2:.1f}s)")
        if not changed:
            break
    phi = {c: fc_cache[c] + g[c] for c in bad_list}
    print(f"  PhiFull fixpoint done ({time.time() - t2:.1f}s)")

    total_nodrop_bdry = 0
    non617_total = 0
    non617_active = 0
    examples = []

    t3 = time.time()
    for c in bad_list:
        pc = phi[c]
        bc = b6_cache[c]
        ec = encode6(bc)
        for d, mover, _ in tp_fwd[c]:
            if phi[d] != pc:
                continue
            bd = b6_cache[d]
            if bd == bc:
                continue
            total_nodrop_bdry += 1
            ed = encode6(bd)
            if (ec, ed) in EDGE_617:
                continue
            non617_total += 1
            if has_deep_copy_pair(d, n):
                non617_active += 1
                if len(examples) < limit_print:
                    examples.append((c, d, mover, bc, bd, phi[c], sorted(
                        k for k in range(4, n - 3) if d[k] == d[k - 1] or d[k] == d[k + 1]
                    )))

    print(f"  no-drop boundary-changing TP-bad steps: {total_nodrop_bdry}")
    print(f"  non617 among them: {non617_total}")
    print(f"  non617 active among them: {non617_active} ({time.time() - t3:.1f}s)")

    if examples:
        print("\n  sample non617 active witnesses:")
        for c, d, mover, bc, bd, ph, sites in examples:
            print(f"    mover={mover} phi={ph} sites={sites}")
            print(f"      src={c}")
            print(f"      dst={d}")
            print(f"      beta={bc}->{bd}")

    print(f"\n  total elapsed: {time.time() - t0:.1f}s")


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    limit_print = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    scan(n, limit_print)
def cup2CycleVal(n, t, j):
    if t < n:
        return 1 if j < t else 0
    elif t < 2 * n - 2:
        if j < 2 * n - 1 - t:
            return 1
        elif j < n - 1:
            return 2
        else:
            return 1
    elif t == 2 * n - 2:
        if j == 0:
            return 1
        elif j < n - 1:
            return 2
        else:
            return 1
    else:
        k = t - (2 * n - 2)
        if k == 0:
            if j == 0:
                return 1
            elif j < n - 1:
                return 2
            else:
                return 1
        else:
            if j < k:
                return 0
            elif j < n - 1:
                return 2
            else:
                return 1


def cycle_config(n, t):
    return tuple(cup2CycleVal(n, t, j) for j in range(n))


def good_cycle_configs(n):
    return {cycle_config(n, t) for t in range(3 * n - 2)}
