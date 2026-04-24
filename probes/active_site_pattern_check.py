#!/usr/bin/env python3
"""
Inspect which deep copy-pair sites work for delete-projectable maximizing paths.

Current goal:
- understand whether the existential-in-k theorem can be sharpened to
  a deterministic site choice on the broad active class.
"""

import sys
import os
from collections import Counter, defaultdict, deque
from itertools import product as cartesian

sys.path.insert(0, os.path.dirname(__file__))
from cup2_final_verify import build_system
from verifier import verify_system


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


def delete_config(c, k):
    return tuple(c[j] if j < k else c[j + 1] for j in range(len(c) - 1))


def deep_copy_pair_sites(c, n):
    return tuple(k for k in range(4, n - 3) if c[k] == c[k - 1] or c[k] == c[k + 1])


def analyze(n, limit=200):
    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    assert result["valid"]
    good_set = result["good_configs"]
    good_set_nm1 = verify_system(build_system(n - 1)[0], build_system(n - 1)[1])["good_configs"]

    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = {c for c in all_configs if c not in good_set}
    fc_cache = {c: fc(c, n) for c in all_configs}
    tp_adj = defaultdict(list)
    tp_adj_k = {k: defaultdict(list) for k in range(4, n - 3)}

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
            if d not in bad_set or tp_triple(d, n) != tc:
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

    witnesses = []
    for c, outs in tp_adj.items():
        for d, mover in outs:
            if phi[d] == phi[c] and boundary6(c, n) != boundary6(d, n):
                witnesses.append((c, d, mover))

    pattern_counter = Counter()
    site_counter = Counter()
    checked = 0

    for src, dst, _ in witnesses[:limit]:
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
                if found:
                    works.append(k)
                    site_counter[k] += 1
            pattern_counter[(sites, tuple(works))] += 1

    print(f"n={n}, checked achiever instances={checked}")
    print("Working-site pattern histogram:")
    for (sites, works), cnt in pattern_counter.most_common(20):
        print(f"  sites={sites} -> works={works}: {cnt}")
    print("Per-site success counts:")
    for k in sorted(site_counter):
        print(f"  k={k}: {site_counter[k]}")


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    analyze(n, limit)
