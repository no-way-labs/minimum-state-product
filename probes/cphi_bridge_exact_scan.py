#!/usr/bin/env python3
"""
Exact CΦ boundary-edge scan against the Lean 617-edge list.

For each n:
  1. use the exact CUP-2 system from cup2_theorem.py
  2. choose a good-set notion:
     - explicit good cycle (Lean semantics)
     - verifier basin (broader computational model)
  3. build TP-preserving bad edges
  4. compute PhiFull by fixpoint on TP edges
  5. extract boundary-changing constant-PhiFull edges
  6. compare their encoded 6-tuple transitions to SixTuple.lean's sixTupleEdgeVals

This is the right RA tool for freezing the bridge target:

    boundary-changing CΦ step -> sixTupleEdge

because it uses the exact same notion of badness as Lean's explicit good cycle,
or lets us compare that to the verifier basin when needed.
"""

from __future__ import annotations

import ast
import os
import re
import sys
import time
from collections import defaultdict
from itertools import product as cartesian

ROOT = os.path.dirname(__file__)
sys.path.insert(0, ROOT)

from cup2_theorem import build_system
from verifier import verify_system


LEAN_SIX_TUPLE = os.path.join(
    os.path.dirname(ROOT),
    "lean",
    "LeanMn",
    "Convergence",
    "SixTuple.lean",
)


def load_lean_617_edges() -> set[tuple[int, int]]:
    with open(LEAN_SIX_TUPLE, "r") as f:
        content = f.read()
    m = re.search(r"def sixTupleEdgeVals : List \(Nat × Nat\) :=\n  \[(.*?)\n  \]", content, re.S)
    if not m:
        raise RuntimeError("could not parse sixTupleEdgeVals from SixTuple.lean")
    # Convert Lean tuple syntax to Python tuple syntax.
    pairs = ast.literal_eval("[" + m.group(1) + "]")
    return set((a, b) for a, b in pairs)


EDGE_617 = load_lean_617_edges()


def _load_nat_list(def_name: str):
    with open(LEAN_SIX_TUPLE, "r") as f:
        content = f.read()
    m = re.search(
        rf"def {def_name} : List Nat :=\n  \[(.*?)\]\n\ntheorem {def_name}_length",
        content,
        re.S,
    )
    if not m:
        raise RuntimeError(f"could not parse {def_name} from SixTuple.lean")
    return ast.literal_eval("[" + m.group(1) + "]")


COND_RANK = _load_nat_list("condensationRankVals")
SCC_RANK = _load_nat_list("sccSubRankVals")


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


def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def boundary6(c, n):
    return (c[0], c[1], c[2], c[n - 3], c[n - 2], c[n - 1])


def encode6(t6):
    return ((((t6[0] * 3 + t6[1]) * 3 + t6[2]) * 3 + t6[3]) * 3 + t6[4]) * 2 + t6[5]


def classify_rank_behavior(edges: set[tuple[int, int]]):
    counts = {
        "cond_drop": 0,
        "cond_eq_scc_drop": 0,
        "special_239_245": 0,
        "other": 0,
    }
    bad_samples = []
    for src, dst in edges:
        c_src = COND_RANK[src]
        c_dst = COND_RANK[dst]
        s_src = SCC_RANK[src]
        s_dst = SCC_RANK[dst]
        if c_dst < c_src:
            counts["cond_drop"] += 1
        elif c_dst == c_src and s_dst < s_src:
            counts["cond_eq_scc_drop"] += 1
        elif (src, dst) == (239, 245):
            counts["special_239_245"] += 1
        else:
            counts["other"] += 1
            if len(bad_samples) < 10:
                bad_samples.append((src, dst, c_src, c_dst, s_src, s_dst))
    return counts, bad_samples


def compute_cphi_boundary_edges(n: int):
    t0 = time.time()
    ms, fs = build_system(n)
    good = None
    bad = None
    raise RuntimeError("compute_cphi_boundary_edges requires a good-set mode")


def cup2_cycle_val(n: int, t: int, j: int) -> int:
    if t < n:
        return 1 if j < t else 0
    if t < 2 * n - 2:
        return 1 if j < 2 * n - 1 - t else (2 if j < n - 1 else 1)
    if t == 2 * n - 2:
        return 1 if j == 0 else (2 if j < n - 1 else 1)
    k = t - (2 * n - 2)
    if k == 0:
        return 1 if j == 0 else (2 if j < n - 1 else 1)
    return 0 if j < k else (2 if j < n - 1 else 1)


def explicit_good_cycle_configs(n: int):
    return {
        tuple(cup2_cycle_val(n, t, j) for j in range(n))
        for t in range(3 * n - 2)
    }


def compute_cphi_boundary_edges(n: int, good_mode: str):
    t0 = time.time()
    ms, fs = build_system(n)
    if good_mode == "explicit":
        good = explicit_good_cycle_configs(n)
    elif good_mode == "basin":
        result = verify_system(ms, fs)
        if not result["valid"]:
            raise RuntimeError(f"system invalid at n={n}")
        good = result["good_configs"]
    else:
        raise ValueError(f"unknown good_mode={good_mode}")

    bad = [c for c in cartesian(*(range(m) for m in ms)) if c not in good]
    bad_set = set(bad)

    fc_cache = {c: fc(c, n) for c in bad}
    tp_fwd = defaultdict(list)
    tp_edges = []

    for c in bad:
        e2c = exp2_count(c, n)
        i21c = int_21(c, n)
        ewc = exp2_weight(c, n)
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            out = fs[i](L, S, R)
            if out == S:
                continue
            d = list(c)
            d[i] = out
            succ = tuple(d)
            if succ not in bad_set:
                continue
            e2s = exp2_count(succ, n)
            i21s = int_21(succ, n)
            ews = exp2_weight(succ, n)
            if e2s == e2c and i21s == i21c and ews == ewc:
                dfc = fc_cache.get(succ, fc(succ, n)) - fc_cache[c]
                tp_edges.append((c, succ, i, dfc))
                tp_fwd[c].append((succ, dfc))

    g = {c: 0 for c in bad}
    for _ in range(2 * n + 10):
        changed = False
        for c in bad:
            best = g[c]
            for succ, dfc in tp_fwd.get(c, []):
                cand = dfc + g[succ]
                if cand > best:
                    best = cand
            if best != g[c]:
                g[c] = best
                changed = True
        if not changed:
            break

    phi = {c: fc_cache[c] + g[c] for c in bad}

    trans = set()
    mover_hist = defaultdict(int)
    sample_edges = []
    sample_witness = {}
    for c, succ, mover, _dfc in tp_edges:
        if phi[succ] != phi[c]:
            continue
        bc = boundary6(c, n)
        bs = boundary6(succ, n)
        if bc == bs:
            continue
        enc = (encode6(bc), encode6(bs))
        trans.add(enc)
        mover_hist[mover] += 1
        sample_witness.setdefault(enc, (c, succ, mover, phi[c], fc_cache[c], fc_cache[succ]))
        if len(sample_edges) < 12:
            sample_edges.append((enc, mover, bc, bs))

    elapsed = time.time() - t0
    return {
        "n": n,
        "num_bad": len(bad),
        "num_tp_edges": len(tp_edges),
        "trans": trans,
        "mover_hist": dict(sorted(mover_hist.items())),
        "sample_edges": sample_edges,
        "sample_witness": sample_witness,
        "elapsed": elapsed,
    }


def scan(ns, good_mode: str):
    print(f"Lean 617-edge count: {len(EDGE_617)}")
    print(f"good-set mode: {good_mode}")
    baseline = None
    baseline_n = None
    ok_all = True
    for n in ns:
        data = compute_cphi_boundary_edges(n, good_mode)
        trans = data["trans"]
        only_here = trans - EDGE_617
        missing_here = EDGE_617 - trans
        same_as_lean = not only_here and not missing_here
        ok_all = ok_all and same_as_lean

        print(f"\n=== n={n} ===")
        print(f"bad configs: {data['num_bad']}")
        print(f"TP-preserving bad edges: {data['num_tp_edges']}")
        print(f"CΦ boundary transitions: {len(trans)}")
        print(f"matches Lean 617 exactly: {same_as_lean}")
        print(f"mover histogram: {data['mover_hist']}")
        rank_counts, bad_samples = classify_rank_behavior(trans)
        print(f"rank classification: {rank_counts}")
        print(f"elapsed: {data['elapsed']:.1f}s")

        if only_here:
            print(f"  transitions realized here but not in Lean: {len(only_here)}")
            print(f"  sample: {sorted(only_here)[:10]}")
            ex = sorted(only_here)[0]
            c, succ, mover, ph, fc_src, fc_dst = data["sample_witness"][ex]
            print(f"  witness mover={mover} phi={ph} fc={fc_src}->{fc_dst}")
            print(f"    src={c}")
            print(f"    dst={succ}")
        if missing_here:
            print(f"  Lean transitions not realized here: {len(missing_here)}")
            print(f"  sample: {sorted(missing_here)[:10]}")
        if bad_samples:
            print(f"  rank-classification bad samples: {bad_samples}")

        if baseline is None:
            baseline = set(trans)
            baseline_n = n
        else:
            same_as_baseline = (trans == baseline)
            print(f"same as n={baseline_n}: {same_as_baseline}")
            if not same_as_baseline:
                print(f"  only in n={n}: {len(trans - baseline)}")
                print(f"  only in n={baseline_n}: {len(baseline - trans)}")

    print(f"\nGLOBAL verdict over {ns}: {'MATCHES LEAN 617' if ok_all else 'MISMATCH'}")


def main():
    args = sys.argv[1:]
    good_mode = "explicit"
    if args[:2] == ["--good", "basin"]:
        good_mode = "basin"
        args = args[2:]
    elif args[:2] == ["--good", "explicit"]:
        good_mode = "explicit"
        args = args[2:]

    if args:
        ns = [int(x) for x in args]
    else:
        ns = [9, 10, 11]
    scan(ns, good_mode)


if __name__ == "__main__":
    main()
