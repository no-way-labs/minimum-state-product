#!/usr/bin/env python3
"""
Check at n=10:

For no-drop active boundary-changing TP-preserving bad steps src -> dst,
does src also always have a deep copy-pair?
"""

import sys
from itertools import product

sys.path.insert(0, "claude")
from active_non617_scan_fast import (
    build_system,
    good_cycle_configs,
    tp_triple,
    fc,
    boundary6,
    has_deep_copy_pair,
)


def analyze(n=10, limit=20):
    ms, fs = build_system(n)
    good = good_cycle_configs(n)
    bad = [c for c in product(*(range(m) for m in ms)) if c not in good]
    bad_set = set(bad)
    fc_cache = {c: fc(c, n) for c in bad}
    tp_cache = {c: tp_triple(c, n) for c in bad}
    b6_cache = {c: boundary6(c, n) for c in bad}
    tp_fwd = {c: [] for c in bad}

    for c in bad:
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
            tp_fwd[c].append((d, i, fc_cache[d] - fc_cache[c]))

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

    total = 0
    src_copy = 0
    counterexamples = []
    for src in bad:
        for dst, mover, _ in tp_fwd[src]:
            if phi[dst] != phi[src]:
                continue
            if b6_cache[dst] == b6_cache[src]:
                continue
            if not has_deep_copy_pair(dst, n):
                continue
            total += 1
            if has_deep_copy_pair(src, n):
                src_copy += 1
            elif len(counterexamples) < limit:
                counterexamples.append((src, dst, mover))

    print(f"n={n}")
    print(f"no-drop active boundary-changing TP-bad steps: {total}")
    print(f"src also has deep copy-pair: {src_copy}")
    print(f"all src active? {src_copy == total}")
    if counterexamples:
        print("\ncounterexamples:")
        for src, dst, mover in counterexamples:
            print(f"  mover={mover}")
            print(f"    src={src}")
            print(f"    dst={dst}")


if __name__ == "__main__":
    analyze()
