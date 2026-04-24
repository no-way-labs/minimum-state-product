#!/usr/bin/env python3
"""
Check candidate local measures on broad active non617 boundary-changing
TP-preserving bad steps.

Measures checked:
  - immediate fc delta
  - TP triple deltas
  - condensationRank(boundary)
  - sccSubRank(boundary)
"""

import ast
import os
import re
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


ROOT = os.path.dirname(__file__)


def parse_nat_list(name):
    path = os.path.join(ROOT, "..", "lean", "LeanMn", "Convergence", "SixTuple.lean")
    with open(path, "r") as f:
        content = f.read()
    m = re.search(rf"def {name} : List Nat :=\s*\[(.*?)\]\n\n", content, re.S)
    if not m:
        raise RuntimeError(f"Could not parse {name}")
    return ast.literal_eval("[" + m.group(1) + "]")


COND_RANK = parse_nat_list("condensationRankVals")
SCC_SUB = parse_nat_list("sccSubRankVals")


def analyze(n=11):
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

    dfc_ctr = Counter()
    dexp2_ctr = Counter()
    dint21_ctr = Counter()
    dweight_ctr = Counter()
    drank_ctr = Counter()
    dscc_ctr = Counter()
    samples = []

    boundary_movers = {0, 1, 2, n - 3, n - 2, n - 1}
    for src in bad:
        src_code = encode6(b6_cache[src])
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
            dfc_ctr[dfc] += 1
            dexp2_ctr[exp2_count(dst, n) - exp2_count(src, n)] += 1
            dint21_ctr[int_21(dst, n) - int_21(src, n)] += 1
            dweight_ctr[exp2_weight(dst, n) - exp2_weight(src, n)] += 1
            drank_ctr[COND_RANK[dst_code] - COND_RANK[src_code]] += 1
            dscc_ctr[SCC_SUB[dst_code] - SCC_SUB[src_code]] += 1
            if len(samples) < 10:
                samples.append((src, dst, mover, dfc, dst_code, src_code))

    print(f"n={n}")
    print("broad active non617 immediate fc delta:", dict(dfc_ctr))
    print("broad active non617 ΔExp2Count:", dict(dexp2_ctr))
    print("broad active non617 ΔInt21:", dict(dint21_ctr))
    print("broad active non617 ΔExp2Weight:", dict(dweight_ctr))
    print("broad active non617 ΔcondensationRank:", dict(drank_ctr))
    print("broad active non617 ΔsccSubRank:", dict(dscc_ctr))
    print("\nsamples:")
    for src, dst, mover, dfc, dst_code, src_code in samples:
        print(f"  mover={mover} dfc={dfc} rankΔ={COND_RANK[dst_code]-COND_RANK[src_code]} sccΔ={SCC_SUB[dst_code]-SCC_SUB[src_code]}")
        print(f"    src={src}")
        print(f"    dst={dst}")


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    analyze(n)
