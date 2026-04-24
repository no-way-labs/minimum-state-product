#!/usr/bin/env python3
"""Axis C of n9_detector_design.md §3 — full-forced-NG SK detector.

Drops the Hamming-1 tube restriction. For each record (ms, cycle, det):
  - V = all non-good configs NG (i.e., all configs \ cycle_set)
  - E = { (c, c') : some p has det[(p, c[p-1], c[p], c[p+1])] != c[p] and
         applying that move yields c' in NG }
  - SK = sink-kernel = largest S ⊆ NG such that every c ∈ S has an out-edge
         in S (computed by sink-peeling iteration).

Detector: fires iff SK ≠ ∅.  SK ≠ ∅ <==> a directed cycle in forced-NG
<==> peel witness outside the 1-tube <==> LB certificate exists.

Note on det-partiality: records built via enumerate_cycles have det covering
only triples encountered in the good-cycle construction. Triples appearing
in NG configs but not in det get treated as "no forced move" (no edge).
This is the conservative reading: we only fire on certificates the CURRENT
det dict enforces. If SK is empty, it can mean either (a) det is too partial
to pin down a peel, or (b) no peel exists. Axis D (extension-LP) disambiguates.

Records built via build_record_from_witness (w5..w8) have totally-extended
det; for those, SK = ∅ <==> the valid system converges, as expected.

Outputs:
  - axis_c_forced_ng_results.json
  - axis_c_forced_ng_summary.md
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from itertools import product as iproduct

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import probe_strengthening1_n8_subthreshold as probe_main  # type: ignore


def build_forced_ng_graph(ms, cycle, det):
    """Return (NG, adjacency) where adjacency[c] = list of c' reachable via det."""
    n = len(ms)
    cycle_set = set(tuple(c) for c in cycle)
    all_configs = list(iproduct(*[range(m) for m in ms]))
    ng = [c for c in all_configs if c not in cycle_set]
    ng_set = set(ng)

    # Parse det: keys may have been stringified on JSON round-trip
    if det and isinstance(next(iter(det.keys())), str):
        det = {eval(k): v for k, v in det.items()}

    adj = {c: [] for c in ng}
    n_partial_misses = 0
    for c in ng:
        for p in range(n):
            triple_key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            out_val = det.get(triple_key)
            if out_val is None:
                n_partial_misses += 1
                continue
            if out_val == c[p]:
                continue
            c_next = list(c)
            c_next[p] = out_val
            c_next = tuple(c_next)
            if c_next in ng_set:
                adj[c].append(c_next)
    return ng, adj, n_partial_misses


def compute_sk(ng, adj):
    """Sink-peeling: repeatedly remove vertices without out-edge in current set."""
    alive = set(ng)
    while True:
        to_remove = set()
        for v in alive:
            if not any(t in alive for t in adj[v]):
                to_remove.add(v)
        if not to_remove:
            break
        alive -= to_remove
    return alive


def scc_analysis(alive, adj):
    """Quick SCC-based diagnostics on SK: number of SCCs and largest-SCC size."""
    if not alive:
        return {"n_scc": 0, "largest_scc_size": 0}
    # Tarjan's algorithm iterative
    index_counter = [0]
    stack = []
    lowlinks = {}
    index = {}
    on_stack = {}
    result = []

    def strongconnect(v):
        work = [(v, iter(adj[v]))]
        index[v] = index_counter[0]
        lowlinks[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack[v] = True
        while work:
            cur, it = work[-1]
            try:
                w = next(it)
                if w not in alive:
                    continue
                if w not in index:
                    index[w] = index_counter[0]
                    lowlinks[w] = index_counter[0]
                    index_counter[0] += 1
                    stack.append(w)
                    on_stack[w] = True
                    work.append((w, iter(adj[w])))
                elif on_stack.get(w):
                    lowlinks[cur] = min(lowlinks[cur], index[w])
            except StopIteration:
                if lowlinks[cur] == index[cur]:
                    scc = []
                    while True:
                        w = stack.pop()
                        on_stack[w] = False
                        scc.append(w)
                        if w == cur:
                            break
                    result.append(scc)
                work.pop()
                if work:
                    parent = work[-1][0]
                    lowlinks[parent] = min(lowlinks[parent], lowlinks[cur])

    for v in alive:
        if v not in index:
            strongconnect(v)
    nontrivial = [s for s in result if len(s) > 1 or (s[0] in adj[s[0]])]
    return {
        "n_scc": len(result),
        "n_nontrivial_scc": len(nontrivial),
        "largest_scc_size": max((len(s) for s in result), default=0),
    }


def analyze_record(rec):
    t0 = time.time()
    cycle = [tuple(c) if not isinstance(c, tuple) else c for c in rec["cycle"]]
    det = dict(rec["det"])
    ng, adj, n_misses = build_forced_ng_graph(rec["ms"], cycle, det)
    n_ng = len(ng)
    n_edges = sum(len(v) for v in adj.values())
    sk = compute_sk(ng, adj)
    scc = scc_analysis(sk, adj)
    dt = time.time() - t0
    return {
        "n": rec["n"], "ms": rec["ms"], "L": rec["L"],
        "product": rec.get("product", int(np.prod(rec["ms"]))),
        "class": rec.get("class", ""),
        "name": rec.get("name", ""),
        "n_ng": n_ng, "n_edges": n_edges,
        "det_partial_misses": n_misses,
        "sk_size": len(sk),
        "sk_nonempty": len(sk) > 0,
        "sk_frac": round(len(sk) / max(n_ng, 1), 4),
        "scc": scc,
        "dt_s": round(dt, 2),
    }


def pretty(r, c1_feasible=None):
    base = f"  n={r['n']} prod={r['product']:>5} L={r['L']:>2} ms={r['ms']} " \
           f"|NG|={r['n_ng']:>5} |E|={r['n_edges']:>6} " \
           f"|SK|={r['sk_size']:>5} frac={r['sk_frac']:.3f} " \
           f"misses={r['det_partial_misses']:>5} " \
           f"scc={r['scc']} dt={r['dt_s']:.1f}s"
    if c1_feasible is not None:
        tag = ("C1=FEAS " if c1_feasible else "C1=INFE ")
        verdict = ("SK-fires " if r["sk_nonempty"] else "SK=empty ")
        base = f"  [{tag} {verdict}] " + base[2:]
    name = r.get("name") or r.get("class")
    return base + f"  ({name})"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--include-n8-sub", action="store_true")
    parser.add_argument("--skip-n9", action="store_true")
    parser.add_argument("--n8-budget", type=float, default=4.0)
    parser.add_argument("--n8-max-orderings", type=int, default=12)
    parser.add_argument("--n9-budget", type=float, default=15.0)
    parser.add_argument("--n9-max-orderings", type=int, default=150)
    parser.add_argument("--output-json",
                        default=os.path.join(HERE, "axis_c_forced_ng_results.json"))
    parser.add_argument("--output-summary",
                        default=os.path.join(HERE, "axis_c_forced_ng_summary.md"))
    args = parser.parse_args()

    print("=" * 72)
    print("Axis C detector — full-forced-NG SK (n9_detector_design.md §3)")
    print("=" * 72)
    t0 = time.time()

    print("\n--- at-threshold reference (w5..w8) ---")
    at = probe_main.load_smalln_witnesses()
    for r in at:
        print(f"  {r['name']} ms={r['ms']} prod={r['product']} L={r['L']}")

    n8_sub = []
    if args.include_n8_sub:
        print("\n--- n=8 sub-threshold sweep ---")
        n8_sub, _ = probe_main.build_sub_corpus_n8(
            per_ordering_budget=args.n8_budget,
            max_orderings=args.n8_max_orderings,
        )

    n9 = []
    if not args.skip_n9:
        print("\n--- n=9 Table 7 sweep ---")
        n9, _ = probe_main.build_n9_table7_corpus(
            per_ordering_budget=args.n9_budget,
            max_orderings=args.n9_max_orderings,
        )

    print(f"\n--- running Axis C SK: {len(at)} at + {len(n8_sub)} n=8 + {len(n9)} n=9 ---")
    at_res = []
    for r in at:
        print(f"  . at {r['name']}", flush=True)
        at_res.append(analyze_record(r))
    n8_res = []
    for r in n8_sub:
        print(f"  . n=8 ms={r['ms']}", flush=True)
        n8_res.append(analyze_record(r))
    n9_res = []
    for r in n9:
        print(f"  . n=9 ms={r['ms']}", flush=True)
        n9_res.append(analyze_record(r))

    # Also compute C1 for direct comparison (quick — reuses lifted graph build)
    def c1_feas(r):
        V_lift, E_lift, _ = probe_main.build_lifted_graph(r)
        return probe_main.solve_circulation_lp(len(V_lift), E_lift).get("feasible", False)

    at_c1 = [c1_feas(r) for r in at]
    n8_c1 = [c1_feas(r) for r in n8_sub]
    n9_c1 = [c1_feas(r) for r in n9]

    print("\n--- per-record (at-threshold) ---")
    for r, f in zip(at_res, at_c1):
        print(pretty(r, c1_feasible=f))
    if n8_res:
        print("\n--- per-record (n=8 sub) ---")
        for r, f in zip(n8_res, n8_c1):
            print(pretty(r, c1_feasible=f))
    print("\n--- per-record (n=9 Table 7) ---")
    for r, f in zip(n9_res, n9_c1):
        print(pretty(r, c1_feasible=f))

    # Counterexample spotlight
    ce_ms = {
        tuple([2, 3, 2, 3, 3, 3, 2, 3, 4]),
        tuple([2, 3, 2, 3, 3, 3, 2, 4, 3]),
        tuple([2, 3, 2, 3, 2, 3, 3, 3, 4]),
        tuple([2, 3, 2, 3, 3, 3, 3, 2, 4]),
    }
    ce_results = [(r, f) for r, f in zip(n9_res, n9_c1) if tuple(r["ms"]) in ce_ms]

    print("\n" + "=" * 72)
    print("SEPARATION AUDIT — Axis C (SK nonempty) vs C1 (LP feasible)")
    print("=" * 72)

    def summary(group, results, c1s):
        if not results:
            return None
        n = len(results)
        sk_fires = sum(1 for r in results if r["sk_nonempty"])
        c1_feas_count = sum(1 for f in c1s if f)
        recovered = sum(1 for r, f in zip(results, c1s)
                        if r["sk_nonempty"] and not f)
        lost = sum(1 for r, f in zip(results, c1s)
                   if not r["sk_nonempty"] and f)
        print(f"  {group:>12}: SK fires {sk_fires}/{n}   "
              f"C1 feas {c1_feas_count}/{n}   "
              f"SK-recovers-C1-miss {recovered}   SK-loses-C1-win {lost}")
        return {"group": group, "n": n, "sk_fires": sk_fires,
                "c1_feas": c1_feas_count, "sk_recovers": recovered,
                "sk_loses": lost}

    summaries = [
        summary("at_thresh", at_res, at_c1),
        summary("n8_sub", n8_res, n8_c1),
        summary("n9_table7", n9_res, n9_c1),
    ]

    print("\nCounterexample spotlight (the 4 non-adjacent orderings):")
    ce_recovered = 0
    for r, f in ce_results:
        fired = "SK-FIRES" if r["sk_nonempty"] else "SK-empty"
        if r["sk_nonempty"] and not f:
            ce_recovered += 1
        print(f"  ms={r['ms']} L={r['L']} C1={'FEAS' if f else 'INFE'} "
              f"{fired}  |SK|={r['sk_size']}  nontrivSCC={r['scc'].get('n_nontrivial_scc')}  "
              f"largestSCC={r['scc'].get('largest_scc_size')}")
    print(f"\n  Axis C recovers {ce_recovered}/4 counterexamples "
          f"(fires where C1 missed)")

    payload = {
        "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
        "parameters": vars(args),
        "summaries": summaries,
        "at_results": at_res, "at_c1": at_c1,
        "n8_results": n8_res, "n8_c1": n8_c1,
        "n9_results": n9_res, "n9_c1": n9_c1,
        "counterexample_recovered": ce_recovered,
        "runtime_s": round(time.time() - t0, 1),
    }
    try:
        with open(args.output_json, "w") as f:
            json.dump(payload, f, indent=2, default=str)
        print(f"\nWrote {args.output_json}")
    except Exception as e:
        print(f"JSON write failed: {e}")

    # Summary markdown
    lines = ["# Axis C detector (full-forced-NG SK) — results\n",
             f"Run {payload['timestamp']}. Runtime {payload['runtime_s']}s.\n"]
    lines.append("Detector fires iff sink-kernel of forced-NG graph is nonempty.\n")
    lines.append("\n## Separation audit\n")
    lines.append("| group | n | SK fires | C1 feas | SK-recovers-C1-miss | SK-loses-C1-win |")
    lines.append("|---|---|---|---|---|---|")
    for s in summaries:
        if s is None:
            continue
        lines.append(f"| {s['group']} | {s['n']} | {s['sk_fires']} | "
                     f"{s['c1_feas']} | {s['sk_recovers']} | {s['sk_loses']} |")
    lines.append(f"\n## Counterexample recovery\n")
    lines.append(f"Axis C recovers **{ce_recovered}/4** of the n=9 `{{2^3,3^5,4}}` "
                 f"non-adjacent counterexamples that C1 misses.\n")
    for r, f in ce_results:
        fired = "SK-FIRES" if r["sk_nonempty"] else "SK-empty"
        lines.append(f"- ms={r['ms']} L={r['L']} C1={'FEAS' if f else 'INFE'} "
                     f"{fired} |SK|={r['sk_size']} "
                     f"nontrivSCC={r['scc'].get('n_nontrivial_scc')}")

    try:
        with open(args.output_summary, "w") as f:
            f.write("\n".join(lines))
        print(f"Wrote {args.output_summary}")
    except Exception as e:
        print(f"Summary write failed: {e}")


if __name__ == "__main__":
    main()
