#!/usr/bin/env python3
"""
Empirical check for the active delete-projectable path theorem.

For boundary-changing TP-preserving no-drop bad steps src -> dst, examine
PhiFull-achieving terminals u reachable from dst and test:

1. Does there exist SOME deep copy-pair site k at u with a delete-projectable
   TP path dst ->* u?
2. Does this hold for EVERY deep copy-pair site of u?

This distinguishes:
- existence-of-some-site theorem shapes, versus
- overly strong fixed-site-for-any-copy-pair theorem shapes.
"""

import sys
import os
import ast
import re
from itertools import product as cartesian
from collections import defaultdict, deque

sys.path.insert(0, os.path.dirname(__file__))
from cup2_final_verify import build_system
from verifier import verify_system

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


def deep_copy_pair_sites(c, n):
    sites = []
    for k in range(4, n - 3):
        if c[k] == c[k - 1] or c[k] == c[k + 1]:
            sites.append(k)
    return sites


def delete_config(c, k):
    return tuple(c[j] if j < k else c[j + 1] for j in range(len(c) - 1))


def main(n, limit_witnesses=200, max_print=20, only_non617=False):
    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    assert result["valid"]
    good_set = result["good_configs"]
    good_set_nm1 = verify_system(build_system(n - 1)[0], build_system(n - 1)[1])["good_configs"]

    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = {c for c in all_configs if c not in good_set}

    fc_cache = {c: fc(c, n) for c in all_configs}
    tp_adj = defaultdict(list)              # src -> [(dst, mover)]
    tp_adj_k = {k: defaultdict(list) for k in range(4, n - 3)}  # delete-projectable edges at k

    for c in all_configs:
        if c not in bad_set:
            continue
        tc = tp_triple(c, n)
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
            tp_adj[c].append((d, i))

            for k in range(4, n - 3):
                if i == k:
                    tp_adj_k[k][c].append(d)
                elif i not in (k - 1, k, k + 1):
                    dc = delete_config(c, k)
                    dd = delete_config(d, k)
                    if dc not in good_set_nm1 and dd not in good_set_nm1:
                        tp_adj_k[k][c].append(d)

    # PhiFull fixpoint
    g = {c: 0 for c in bad_set}
    for _ in range(2 * n + 10):
        changed = False
        for c in bad_set:
            best = g[c]
            for d, _ in tp_adj.get(c, []):
                cand = fc_cache[d] - fc_cache[c] + g[d]
                if cand > best:
                    best = cand
            if best != g[c]:
                g[c] = best
                changed = True
        if not changed:
            break
    phi = {c: fc_cache[c] + g[c] for c in bad_set}

    # Broad witness set: boundary-changing TP no-drop bad steps
    witnesses = []
    for c, outs in tp_adj.items():
        for d, mover in outs:
            if phi[d] != phi[c]:
                continue
            if boundary6(c, n) == boundary6(d, n):
                continue
            if only_non617:
                if (encode6(boundary6(c, n)), encode6(boundary6(d, n))) in EDGE_617:
                    continue
            witnesses.append((c, d, mover))

    label = "non617 " if only_non617 else "broad "
    print(f"n={n}: {len(witnesses)} {label}active-candidate no-drop boundary-changing TP-bad steps")

    checked = 0
    some_site_fail = 0
    every_site_fail = 0

    for src, dst, mover in witnesses[:limit_witnesses]:
        # Find all reachable phi achievers from dst
        q = deque([dst])
        seen = {dst}
        achievers = []
        while q:
            c = q.popleft()
            if fc_cache[c] == phi[dst]:
                achievers.append(c)
            for d, _ in tp_adj.get(c, []):
                if d not in seen:
                    seen.add(d)
                    q.append(d)

        for u in achievers:
            sites = deep_copy_pair_sites(u, n)
            if not sites:
                continue
            checked += 1

            works = []
            for k in sites:
                qk = deque([dst])
                seenk = {dst}
                found = False
                while qk:
                    c = qk.popleft()
                    if c == u:
                        found = True
                        break
                    for d in tp_adj_k[k].get(c, []):
                        if d not in seenk:
                            seenk.add(d)
                            qk.append(d)
                works.append((k, found))

            if not any(ok for _, ok in works):
                every_site_fail += 1
                if every_site_fail <= max_print:
                    print("NO PROJECTABLE SITE")
                    print(f"  src={src}")
                    print(f"  dst={dst}")
                    print(f"  achiever={u}")
                    print(f"  sites={works}")
                break

            if not all(ok for _, ok in works):
                some_site_fail += 1
                if some_site_fail <= max_print:
                    print("NOT EVERY SITE WORKS")
                    print(f"  src={src}")
                    print(f"  dst={dst}")
                    print(f"  achiever={u}")
                    print(f"  sites={works}")
                break

    print()
    print(f"Checked achiever instances: {checked}")
    print(f"Instances with NO projectable site: {every_site_fail}")
    print(f"Instances where some sites fail but some succeed: {some_site_fail}")


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    max_print = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    only_non617 = bool(int(sys.argv[4])) if len(sys.argv) > 4 else False
    main(n, limit, max_print, only_non617)
