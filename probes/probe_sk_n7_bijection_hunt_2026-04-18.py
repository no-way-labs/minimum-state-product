#!/usr/bin/env python3
"""Bijection hunt — at n=7 with |peel|=2^(n-1)=64, identify the bijection.

Prior probe (probe_sk_peel_structure_n7_2026-04-16.py) showed 165/165 cycles at
sub-M_7 multisets have |peel(N_1(C) ∩ VC-NG)| = 64 exactly, all peel configs
Hamming-1 from cycle.

Keston 2026-04-18: exact equality means a bijection exists. Hunt it.

Hypothesis candidates:
  H1: peel ↔ {0,1}^(n-1) via binary-position pattern
  H2: peel ↔ subset of (cycle_index, flip_position) pairs of size 2^(n-1)
  H3: peel ↔ set of configs with Σ c_i ≡ fixed (mod 2) at binary coords only
  H4: peel ↔ (i, direction) where direction indicates left/right in some cyclic order

Output: per-cycle breakdown of peel survivors grouped by (i, q) and (q, v).
"""
from __future__ import annotations
from collections import Counter, defaultdict
from itertools import product as iproduct
import importlib.util, os, sys, time, json

sys.setrecursionlimit(100000)

_HERE = os.path.dirname(os.path.abspath(__file__))
_PROBE = os.path.join(_HERE, "probe_sk_hamming1_chain_closure_2026-04-17.py")
spec = importlib.util.spec_from_file_location("probe_c", _PROBE)
probe_c = importlib.util.module_from_spec(spec); spec.loader.exec_module(probe_c)

enumerate_cycles_multistart = probe_c.enumerate_cycles_multistart
build_N1_and_peel = probe_c.build_N1_and_peel
forced_successors = probe_c.forced_successors


def analyze_peel_bijection(ms, n, cycle, det, L, verbose=False):
    """Compute peel and report bijection-relevant stats."""
    N1, adj, peel_set, provenance, V, move_entries, cycle_set = build_N1_and_peel(
        ms, n, cycle, det)
    # Per-survivor canonical (q, v, i) — pick lex-first from provenance list
    # to ensure uniqueness.
    records = []
    by_q = Counter()
    by_i = Counter()
    by_qi = Counter()
    by_qv = Counter()
    for c in peel_set:
        prov = sorted(provenance[c])  # list of (q, v, i)
        q, v, i = prov[0]
        records.append((c, q, v, i, prov))
        by_q[q] += 1
        by_i[i] += 1
        by_qi[(q, i)] += 1
        by_qv[(q, v)] += 1

    # Check: is the map c ↦ (q, i) (canonical) injective?
    qi_set = {(q, i) for (_, q, _, i, _) in records}
    qi_inj = len(qi_set) == len(records)

    # Check: is the map c ↦ (q, v, i) injective across all choices?
    qvi_multi = Counter((q, v, i) for (_, q, v, i, _) in records)
    qvi_inj = all(v == 1 for v in qvi_multi.values())

    # Number of distinct cycle configs that contribute (by canonical i)
    distinct_i = {i for (_, _, _, i, _) in records}
    # Per cycle config i: how many peel survivors have canonical i?
    per_i = Counter(i for (_, _, _, i, _) in records)

    # Look at binary positions: what values appear in peel at each binary position?
    binary_positions = [p for p in range(n) if ms[p] == 2]
    binary_patterns = Counter()
    for c, _, _, _, _ in records:
        b = tuple(c[p] for p in binary_positions)
        binary_patterns[b] += 1

    summary = {
        "L": L,
        "peel_size": len(peel_set),
        "ms": list(ms),
        "V_sizes": [len(v) for v in V],
        "by_q": dict(by_q),
        "by_qv": {f"q={q},v={v}": c for ((q, v), c) in by_qv.items()},
        "qi_injective": qi_inj,
        "qvi_canonical_injective": qvi_inj,
        "distinct_i_count": len(distinct_i),
        "per_i_histogram": dict(Counter(per_i.values())),
        "binary_positions": binary_positions,
        "binary_pattern_count": {str(k): v for k, v in binary_patterns.items()},
        "num_binary_patterns": len(binary_patterns),
    }

    if verbose:
        print(json.dumps(summary, indent=2))
        print("\n  First 16 peel survivors (sorted):")
        for rec in sorted(records)[:16]:
            c, q, v, i, prov = rec
            print(f"    {list(c)}  canonical (q={q}, v={v}, i={i})  "
                  f"cycle[i]={list(cycle[i])}")

    return summary, records


def run():
    n = 7
    # 3-binary + 4-ternary multisets — matches the 165-records regime.
    candidates = [
        (2, 2, 2, 3, 3, 3, 3),   # 648
        (2, 3, 2, 3, 2, 3, 3),   # 648 (permutation)
        (2, 2, 3, 3, 3, 3, 2),   # 648
    ]
    out_all = []
    for ms in candidates:
        prod = 1
        for m in ms: prod *= m
        print(f"\n=== n={n} ms={ms} product={prod} ===")
        cycles = enumerate_cycles_multistart(ms, n, L_min=2*n+2, L_max=2*n+4,
                                              time_budget=30, max_cycles=6)
        print(f"  {len(cycles)} cycles enumerated")
        for idx, (cycle, movers, det) in enumerate(cycles[:3]):
            L = len(movers)
            print(f"\n  -- cycle[{idx}] L={L} --")
            summary, records = analyze_peel_bijection(
                ms, n, cycle, det, L, verbose=(idx == 0))
            out_all.append({"ms": list(ms), "idx": idx, **summary})
            if idx > 0:
                # Short summary only
                print(f"    |peel|={summary['peel_size']}  "
                      f"by_q={summary['by_q']}  "
                      f"qi_inj={summary['qi_injective']}  "
                      f"distinct_i={summary['distinct_i_count']}")

    # Save
    with open(os.path.join(_HERE, "sk_phase0_out", "n7_bijection_hunt.json"), "w") as f:
        json.dump(out_all, f, indent=2)
    print("\n=== DONE ===")


if __name__ == "__main__":
    run()
