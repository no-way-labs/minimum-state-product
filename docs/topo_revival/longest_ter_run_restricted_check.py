#!/usr/bin/env python3
"""Strengthening #5 — empirical check of the restricted LP statement
    `longest_ter_run(ms) ≤ 1  ⟹  LP-feasible without c_self edges`
on the full n = 5..8 sub-threshold corpus (lifted from n ∈ {5, 6, 7}
19 records to n ∈ {5, 6, 7, 8} via task #1, then appended with the n = 9
Table 7 records).

This is the *flow-weighted* version of the Wave 5 / Wave 6 T2
observation: "on records where the cycle has no two consecutive
ternary positions, the lifted circulation can be routed entirely
through transport + sided-context (c_left / c_right) edges; c_self
is never needed."

A record is in the subclass iff `longest_ter_run(ms) ≤ 1` — equivalently,
no two cyclically consecutive m_i entries are both equal to 3.

Two predicates are computed per record:
  (a) in_subclass     — `longest_ter_run(ms) ≤ 1`
  (b) restricted_lp_feasible — the LP  Σ Φ_e ≥ 1, B^T Φ = 0, Φ ≥ 0
      restricted to {transport, c_left, c_right, other} edges (i.e.
      deleting all c_self edges from E_lift) is feasible.

The Wave 6 T2 observation is restated as:  (a) ⟹ (b).

Outputs:
  - longest_ter_run_audit.json  (per-record + LP residue if any)
  - console cross-tabulation and n=9 stretch commentary.

References:
  - Wave 5 addendum §2 (sk/wave5/item2_subclass_proof_attempt_2026-05-17.md)
  - Wave 6 T2 memo (topo_revival/wave6/item2_t_sided_only_empirical_2026-05-17.md)
  - task #1 driver produces `phase1_n8_sub_corpus.json` (68 records).
"""

from __future__ import annotations

import importlib.util
import json
import os
import sys
from collections import Counter, defaultdict

import numpy as np
from scipy.optimize import linprog

HERE = os.path.dirname(os.path.abspath(__file__))
CLAUDE_DIR = os.path.abspath(os.path.join(HERE, "..", "..", "..", "claude"))
sys.path.insert(0, CLAUDE_DIR)

spec_probe = importlib.util.spec_from_file_location(
    "probe_main",
    os.path.join(HERE, "probe_strengthening1_n8_subthreshold.py"),
)
probe_main = importlib.util.module_from_spec(spec_probe)
spec_probe.loader.exec_module(probe_main)


def longest_ter_run(ms) -> int:
    """Longest cyclic run of positions with m_i = 3 (ternary).
    Wraps around at the ring boundary."""
    n = len(ms)
    is_ter = [m == 3 for m in ms]
    if not any(is_ter):
        return 0
    if all(is_ter):
        return n
    best = 0
    extended = is_ter + is_ter
    current = 0
    for v in extended:
        if v:
            current += 1
            best = max(best, current)
        else:
            current = 0
    return min(best, n)


def restricted_lp(n_vertices, E_lift, excluded_types=("c_self",)):
    """Solve the circulation LP on E_lift \\ {edges of excluded types}.

    Returns the same dict shape as probe_main.solve_circulation_lp but
    restricted to the filtered edge set."""
    kept = [(s, t, et) for (s, t, et) in E_lift
            if et.split('[')[0] not in excluded_types]
    return probe_main.solve_circulation_lp(n_vertices, kept), len(kept)


def check_record(rec):
    ms = rec["ms"]
    V_lift, E_lift, _ = probe_main.build_lifted_graph(rec)
    lr = longest_ter_run(ms)
    in_subclass = lr <= 1

    lp_full = probe_main.solve_circulation_lp(len(V_lift), E_lift)
    lp_rest, n_edges_rest = restricted_lp(
        len(V_lift), E_lift, excluded_types=("c_self",))

    etype_total = Counter(e[2].split('[')[0] for e in E_lift)

    return {
        "class": rec.get("class"),
        "n": rec["n"],
        "ms": ms,
        "L": rec["L"],
        "product": rec["product"],
        "longest_ter_run": lr,
        "in_subclass": in_subclass,
        "nV_lift": len(V_lift),
        "nE_lift": len(E_lift),
        "nE_no_cself": n_edges_rest,
        "edge_types": dict(etype_total),
        "full_lp_feasible": lp_full.get("feasible", False),
        "restricted_lp_feasible": lp_rest.get("feasible", False),
        "supports_conjecture": (
            (not in_subclass) or lp_rest.get("feasible", False)
        ),
    }


def main():
    corpus_path = os.path.join(HERE, "phase1_n8_sub_corpus.json")
    if not os.path.exists(corpus_path):
        print(f"ERROR: {corpus_path} not found.")
        return 1
    with open(corpus_path) as f:
        corpus = json.load(f)

    print("=" * 72)
    print("Restricted LP feasibility check — longest_ter_run ≤ 1 subclass")
    print("Conjecture:  longest_ter_run(ms) ≤ 1  ⟹  LP feasible without c_self")
    print("=" * 72)

    def rebuild(summary_rec, L_max=55, budget=15.0):
        ms = summary_rec["ms"]
        n = summary_rec["n"]
        cycles = probe_main.enumerate_cycles(
            ms, n, L_max, budget, max_cycles=1)
        if not cycles:
            return None
        cycle, movers, det = cycles[0]
        return {
            "class": summary_rec.get("class"),
            "n": n,
            "ms": ms,
            "cycle": cycle,
            "movers": movers,
            "det": det,
            "L": len(cycle),
            "product": summary_rec["product"],
        }

    all_results = []
    rebuild_failures = []

    print("\n--- n=8 sub-threshold (59 records from task #1) ---")
    for summary in corpus["n8_sub"]["records"]:
        rec = rebuild(summary)
        if rec is None:
            rebuild_failures.append(summary)
            continue
        result = check_record(rec)
        all_results.append(result)
        sub_tag = "in " if result["in_subclass"] else "OUT"
        rest_tag = "REST-FEAS" if result["restricted_lp_feasible"] else "REST-INFEAS"
        print(f"  [{sub_tag}/{rest_tag:11s}] n=8 ms={result['ms']} "
              f"L={result['L']} ltr={result['longest_ter_run']} "
              f"full-feas={result['full_lp_feasible']}")

    print("\n--- n=9 Table 7 (9 records from task #1) ---")
    for summary in corpus["n9_table7_sub"]["records"]:
        rec = rebuild(summary)
        if rec is None:
            rebuild_failures.append(summary)
            continue
        result = check_record(rec)
        all_results.append(result)
        sub_tag = "in " if result["in_subclass"] else "OUT"
        rest_tag = "REST-FEAS" if result["restricted_lp_feasible"] else "REST-INFEAS"
        print(f"  [{sub_tag}/{rest_tag:11s}] n=9 ms={result['ms']} "
              f"L={result['L']} ltr={result['longest_ter_run']} "
              f"full-feas={result['full_lp_feasible']}")

    # Cross-tabulation
    print("\n" + "=" * 72)
    print("SUMMARY (all records: n=8 sub + n=9 Table 7)")
    print("=" * 72)
    total = len(all_results)
    in_sub = [r for r in all_results if r["in_subclass"]]
    out_sub = [r for r in all_results if not r["in_subclass"]]
    rest_feas = [r for r in all_results if r["restricted_lp_feasible"]]
    rest_infeas = [r for r in all_results if not r["restricted_lp_feasible"]]
    cross = {
        "in_subclass_restricted_feas":    0,
        "in_subclass_restricted_infeas":  0,
        "out_subclass_restricted_feas":   0,
        "out_subclass_restricted_infeas": 0,
    }
    for r in all_results:
        key = ("in_subclass" if r["in_subclass"] else "out_subclass")
        key += "_restricted_feas" if r["restricted_lp_feasible"] else "_restricted_infeas"
        cross[key] += 1

    print(f"  Total records: {total}")
    print(f"  In subclass (longest_ter_run ≤ 1):  {len(in_sub)}")
    print(f"  Out subclass (longest_ter_run ≥ 2): {len(out_sub)}")
    print(f"  Restricted LP feasible:              {len(rest_feas)}")
    print(f"  Restricted LP infeasible:            {len(rest_infeas)}")
    print("\n  Cross-tabulation:")
    for k, v in cross.items():
        print(f"    {k}: {v}")

    # The restricted conjecture: in_subclass ⟹ restricted_lp_feasible
    violators = [r for r in in_sub if not r["restricted_lp_feasible"]]
    print(f"\n  Conjecture violations (in_subclass ∧ restricted_lp INFEAS): "
          f"{len(violators)}/{len(in_sub)}")
    if violators:
        print("  Violator details:")
        for r in violators[:10]:
            print(f"    n={r['n']} ms={r['ms']} ltr={r['longest_ter_run']} "
                  f"full-feas={r['full_lp_feasible']}")
    else:
        print(f"  Conjecture HOLDS on all {len(in_sub)} in-subclass records.")

    # Also flag: out-of-subclass records that happen to be restricted-feasible
    # (these are in the hypothesis's implication-shadow; not violations, but
    # interesting for a sharper converse).
    spurious_feas = [r for r in out_sub if r["restricted_lp_feasible"]]
    print(f"\n  Out-of-subclass with restricted-feas: {len(spurious_feas)}/{len(out_sub)} "
          f"(not violations — just shows converse is loose).")

    payload = {
        "conjecture": (
            "longest_ter_run(ms) ≤ 1  ⟹  restricted LP (E_lift \\ c_self) is feasible"
        ),
        "total_records": total,
        "subclass_counts": {
            "in_subclass": len(in_sub),
            "out_subclass": len(out_sub),
            "restricted_feas": len(rest_feas),
            "restricted_infeas": len(rest_infeas),
            **cross,
        },
        "conjecture_violations": len(violators),
        "records": all_results,
        "rebuild_failures": [{"ms": s["ms"], "n": s["n"]} for s in rebuild_failures],
    }
    out_path = os.path.join(HERE, "longest_ter_run_audit.json")
    with open(out_path, "w") as f:
        json.dump(payload, f, indent=2)
    print(f"\nWrote {out_path}")
    print("=" * 72)
    if len(violators) == 0:
        print(f"RESTRICTED CONJECTURE HOLDS: all {len(in_sub)} in-subclass "
              f"records (n=5..8 sub + n=9 Table 7) admit a c_self-free "
              f"circulation.")
    else:
        print(f"RESTRICTED CONJECTURE FAILS: {len(violators)}/{len(in_sub)} "
              f"in-subclass records have no c_self-free circulation.")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    sys.exit(main())
