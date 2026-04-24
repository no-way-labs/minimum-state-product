"""§1.1 Full-NG Axis C at n = 10 — partial sub-threshold sweep.

Enumerates every sorted multiset on n=10 with product < B_10 = 26244 (291 in
total), canonicalizes orderings modulo D_n (cyclic rotation + reflection),
and for each ordering attempts to find a good cycle within a bounded budget.
For every (cycle, det) found, runs probe_axis_c_forced_ng.analyze_record to
produce the Axis-C sink-kernel verdict on the full forced-NG digraph.

Records:
  - sub-threshold multisets visited
  - orderings tried per multiset
  - cycles found
  - Axis-C verdict per found (cycle, det)
  - timing per multiset

Outcome gates for §1.1 at n=10:
  - All sub-threshold candidates have SK(detOf) ≠ ∅ → Conjecture 20
    empirically verified through n=10 (at this enumeration depth).
  - Some sub-threshold candidate has SK = ∅: either a real falsification
    or a det-coverage artifact. Record per-record coverage so the
    downstream analysis can tell these apart.

Budget knobs:
  - --max-multisets: cap multisets processed (default 50, partial pass)
  - --budget-per-ord: per-ordering enumeration time budget (default 8s)
  - --max-orderings: per-multiset ordering cap (default 4)
  - --out: output json path

Artifact: JSON with per-multiset records and overall summary.
"""
from __future__ import annotations
import argparse
import json
import os
import sys
import time
from itertools import permutations
from collections import defaultdict

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))
# The LP strengthening-task-1 helper + axis-C forced-NG helper were
# developed in lean/docs/paper_upgrade_1/ under the private research
# tree; they are expected to sit next to this file (or on PYTHONPATH)
# in STAGE.  Keep this discovery lightweight so the probe runs from
# any cwd under the repo.
for candidate in (HERE,
                  os.path.join(REPO, "probes"),
                  os.path.join(REPO, "docs", "axisc")):
    if candidate not in sys.path:
        sys.path.insert(0, candidate)

import probe_strengthening1_n8_subthreshold as psub
import probe_axis_c_forced_ng as axc


def enum_sub_threshold_multisets(n: int, max_prod: int) -> list[tuple[int, ...]]:
    out = []
    def rec(i, prefix, prod):
        if i == n:
            if 1 <= prod < max_prod:
                out.append(tuple(prefix))
            return
        lo = prefix[-1] if prefix else 2
        m_max = max_prod // max(prod, 1)
        for m in range(lo, m_max + 1):
            if prod * m < max_prod:
                rec(i + 1, prefix + [m], prod * m)
    rec(0, [], 1)
    return out


def canonical_dihedral_reps(sorted_ms: tuple[int, ...], max_reps: int) -> list[tuple[int, ...]]:
    """Return canonical cyclic orderings modulo D_n (rotation + reflection)."""
    n = len(sorted_ms)
    seen = set(); reps = []
    for perm in set(permutations(sorted_ms)):
        rots = [perm[i:] + perm[:i] for i in range(n)]
        refls = [tuple(reversed(r)) for r in rots]
        canon = min(rots + refls)
        if canon not in seen:
            seen.add(canon); reps.append(perm)
        if len(reps) >= max_reps:
            break
    return reps


def process_multiset(
    sorted_ms: tuple[int, ...], n: int, max_orderings: int,
    budget_per_ord: float, L_max: int, verbose: bool = True,
) -> dict:
    """Return dict with per-ordering records + aggregates for one multiset."""
    orderings = canonical_dihedral_reps(sorted_ms, max_orderings)
    per_ord_records = []
    n_cycles_found = 0
    axc_verdicts = []  # list of (nonempty, sk_size, sk_frac, coverage_pct)
    for ord_idx, ord_ in enumerate(orderings, start=1):
        if verbose:
            print(f"      [ord {ord_idx}/{len(orderings)}] {list(ord_)}",
                  flush=True)
        t0 = time.time()
        cycles = psub.enumerate_cycles(list(ord_), n, L_max, budget_per_ord,
                                        max_cycles=1)
        dt_enum = time.time() - t0
        if not cycles:
            if verbose:
                print(f"        NO CYCLE in {dt_enum:.1f}s "
                      f"(budget {budget_per_ord:.0f}s)", flush=True)
            per_ord_records.append({
                "ordering": list(ord_), "cycle_found": False,
                "dt_enum_s": round(dt_enum, 2),
            })
            continue
        cycle, movers, det = cycles[0]
        rec = {"ms": list(ord_), "n": n, "cycle": cycle, "movers": movers,
               "det": dict(det), "L": len(cycle),
               "product": int(np.prod(ord_))}
        if verbose:
            print(f"        cycle L={len(cycle)} in {dt_enum:.1f}s; "
                  f"running Axis-C...", flush=True)
        t1 = time.time()
        axc_r = axc.analyze_record(rec)
        dt_axc = time.time() - t1
        n_cycles_found += 1
        cov_pct = 100.0 * len(det) / max(sum(m ** 3 for m in ord_), 1)
        verdict = "FIRE" if axc_r["sk_nonempty"] else "SILENT"
        if verbose:
            print(f"        Axis-C {verdict}: "
                  f"|NG|={axc_r['n_ng']} |SK|={axc_r['sk_size']} "
                  f"frac={axc_r['sk_frac']} "
                  f"cov={cov_pct:.2f}% ({dt_axc:.1f}s)", flush=True)
        axc_verdicts.append((axc_r["sk_nonempty"], axc_r["sk_size"],
                             axc_r["sk_frac"], cov_pct))
        per_ord_records.append({
            "ordering": list(ord_),
            "cycle_found": True,
            "L": len(cycle),
            "coverage_pct": round(cov_pct, 3),
            "n_det": len(det),
            "axc_n_ng": axc_r["n_ng"],
            "axc_n_edges": axc_r["n_edges"],
            "axc_sk_size": axc_r["sk_size"],
            "axc_sk_nonempty": axc_r["sk_nonempty"],
            "axc_sk_frac": axc_r["sk_frac"],
            "axc_scc": axc_r["scc"],
            "axc_det_partial_misses": axc_r["det_partial_misses"],
            "dt_enum_s": round(dt_enum, 2),
            "dt_axc_s": round(dt_axc, 2),
        })
    return {
        "sorted_ms": list(sorted_ms),
        "product": int(np.prod(sorted_ms)),
        "n_orderings_tried": len(orderings),
        "n_cycles_found": n_cycles_found,
        "n_axc_fire": sum(1 for v, *_ in axc_verdicts if v),
        "n_axc_silent": sum(1 for v, *_ in axc_verdicts if v is False),
        "per_ordering": per_ord_records,
    }


def _fmt_eta(seconds_remaining: float) -> str:
    if seconds_remaining < 60:
        return f"{seconds_remaining:.0f}s"
    if seconds_remaining < 3600:
        return f"{seconds_remaining/60:.1f}min"
    return f"{seconds_remaining/3600:.2f}h"


def _checkpoint(out_path: str, payload: dict):
    """Atomic-ish checkpoint: write to .tmp then rename."""
    tmp = out_path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(payload, f, indent=2, default=str)
    os.replace(tmp, out_path)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=10,
                        help="ring size (default 10)")
    parser.add_argument("--max-multisets", type=int, default=0,
                        help="cap multisets processed (0 = ALL, default)")
    parser.add_argument("--max-orderings", type=int, default=4,
                        help="per-multiset canonical-ordering cap (default 4)")
    parser.add_argument("--budget-per-ord", type=float, default=60.0,
                        help="per-ordering cycle-enumeration budget in "
                             "seconds (default 60 — was 8s for session probe)")
    parser.add_argument("--L-max", type=int, default=0,
                        help="max cycle length to enumerate "
                             "(0 = auto: 6n, default)")
    parser.add_argument("--out", default="",
                        help="output path (default: auto "
                             "axc_n{N}_sweep_results.json under paper_upgrade_3/)")
    parser.add_argument("--checkpoint-every", type=int, default=5,
                        help="flush results to disk every N multisets "
                             "(default 5)")
    parser.add_argument("--quiet-ordering", action="store_true",
                        help="suppress per-ordering progress lines")
    args = parser.parse_args()

    n = args.n
    B_n = 4 * 3 ** (n - 2)
    L_max = args.L_max if args.L_max > 0 else 6 * n
    out_path = args.out or os.path.join(
        ROOT, "lean/docs/paper_upgrade_3",
        f"axc_n{n}_sweep_results.json")

    print("=" * 78, flush=True)
    print(f"§1.1 Full-NG Axis C sweep — n = {n}", flush=True)
    print("=" * 78, flush=True)
    print(f"  threshold B_n     = {B_n}")
    print(f"  L_max             = {L_max}")
    print(f"  budget_per_ord    = {args.budget_per_ord}s")
    print(f"  max_orderings/ms  = {args.max_orderings}")
    print(f"  checkpoint_every  = {args.checkpoint_every} multisets")
    print(f"  output            = {out_path}", flush=True)

    print(f"\nEnumerating sub-threshold multisets at n = {n}...", flush=True)
    all_ms = enum_sub_threshold_multisets(n, B_n)
    print(f"  {len(all_ms)} multisets with Π m_i < {B_n}", flush=True)

    all_ms_sorted = sorted(all_ms, key=lambda ms: (int(np.prod(ms)), ms))
    if args.max_multisets > 0 and args.max_multisets < len(all_ms_sorted):
        stride = len(all_ms_sorted) / args.max_multisets
        picked = [all_ms_sorted[int(i * stride)] for i in range(args.max_multisets)]
        print(f"  stride-sampled to {len(picked)} multisets "
              f"(--max-multisets={args.max_multisets})", flush=True)
    else:
        picked = all_ms_sorted
        print(f"  processing ALL {len(picked)} multisets", flush=True)

    # Estimate worst-case runtime
    worst_s = len(picked) * args.max_orderings * args.budget_per_ord
    print(f"  worst-case budget: {len(picked)} ms × {args.max_orderings} ord × "
          f"{args.budget_per_ord:.0f}s/ord = {_fmt_eta(worst_s)}", flush=True)
    print(flush=True)

    t0 = time.time()
    results = []
    totals = defaultdict(int)
    totals["no_cycle_multisets"] = 0
    for idx, ms in enumerate(picked, start=1):
        dt_total = time.time() - t0
        frac = idx / len(picked)
        est_total = dt_total / frac if frac > 0 else 0
        eta = est_total - dt_total
        print(f"[{idx:>3}/{len(picked)}  {100*frac:5.1f}%  elapsed={_fmt_eta(dt_total)}  "
              f"eta={_fmt_eta(eta)}] ms={list(ms)} prod={int(np.prod(ms))}",
              flush=True)
        r = process_multiset(ms, n, args.max_orderings, args.budget_per_ord,
                             L_max, verbose=not args.quiet_ordering)
        results.append(r)
        if r["n_cycles_found"] == 0:
            totals["no_cycle_multisets"] += 1
        totals["cycles_found"] += r["n_cycles_found"]
        totals["axc_fire"]     += r["n_axc_fire"]
        totals["axc_silent"]   += r["n_axc_silent"]
        print(f"    -> this_ms: cycles={r['n_cycles_found']}/"
              f"{r['n_orderings_tried']}  fire={r['n_axc_fire']}  "
              f"silent={r['n_axc_silent']}", flush=True)
        print(f"    -> TOTALS: cycles={totals['cycles_found']} fire="
              f"{totals['axc_fire']} silent={totals['axc_silent']} "
              f"no_cycle_ms={totals['no_cycle_multisets']}", flush=True)
        # Alert immediately on silent
        if r["n_axc_silent"] > 0:
            print(f"    *** ALERT: {r['n_axc_silent']} silent on this "
                  f"multiset — check per_ordering in the JSON checkpoint ***",
                  flush=True)
        # Checkpoint
        if idx % args.checkpoint_every == 0 or idx == len(picked):
            os.makedirs(os.path.dirname(out_path), exist_ok=True)
            _checkpoint(out_path, {
                "parameters": vars(args),
                "n_multisets_total": len(all_ms),
                "n_multisets_processed": idx,
                "n_multisets_picked": len(picked),
                "totals": dict(totals),
                "results": results,
                "runtime_s": round(time.time() - t0, 2),
                "checkpoint_at": time.strftime("%Y-%m-%d %H:%M:%S"),
                "in_progress": idx < len(picked),
            })
            print(f"    [checkpoint @ {idx}/{len(picked)} → {out_path}]",
                  flush=True)

    print(flush=True)
    print("=" * 78, flush=True)
    print(f"DONE  runtime={_fmt_eta(time.time() - t0)}", flush=True)
    print(f"  multisets processed: {len(picked)}")
    print(f"  cycles found:        {totals['cycles_found']}")
    print(f"  Axis-C fire:         {totals['axc_fire']}")
    print(f"  Axis-C silent:       {totals['axc_silent']}")
    print(f"  no-cycle multisets:  {totals['no_cycle_multisets']}  "
          "(budget-limited)")
    print("=" * 78, flush=True)
    print(f"Wrote {out_path}", flush=True)
    if totals["axc_silent"] > 0:
        print("\n*** FINAL ALERT: axc_silent > 0 — coverage-artifact audit "
              "required (see axisc_n10_n11_findings.md §3) ***", flush=True)
    else:
        print(f"\nAxis-C fires on all {totals['cycles_found']} cycles "
              f"found; Conjecture 20 consistent with data at n = {n} on "
              f"the tested enumeration depth.", flush=True)


if __name__ == "__main__":
    main()
