#!/usr/bin/env python3
"""Closure-Debt Obstruction (CDO) — exhaustive subset probe (2026-04-19).

Verdict memo (predecessor): docs/lean_docs/sk/sk_a1_closure_debt_probe_2026-04-19.md
Spec memo:                  docs/lean_docs/sk/sk_a1_stuck_closure_observation_2026-04-18.md

Reframing: the prior 726-seed sweep timed out on every seed. This probe
trades coverage breadth for coverage depth: ~25 hardcoded seeds, NO
max_terminals_per_start cap, generous 60s (or 120s for n=6 ms=(2,3,3,3,3,3))
per-seed wall budget. Reuses dfs_seeded_with_terminals and CDO classification
logic from prior probes UNCHANGED.

Per-seed outcome tags:
    EXHAUSTIVE  : DFS closed (no time-cap hit)  → CDO classified on every terminal
    UNBOUNDABLE : DFS time-capped (terminals collected before timeout count
                  toward CDO classification but seed is excluded from verdict)

Pre-committed verdict thresholds (binding, per §7 of the verdict memo):
    GREEN-subset  : ≥ 20 seeds EXHAUSTIVE, 0 CDO violators on those
    YELLOW-subset : 0 violators on EXHAUSTIVE seeds but ≥ 50% of subset is
                    UNBOUNDABLE
    RED-subset    : ≥ 1 CDO violator on an EXHAUSTIVELY-classified seed
"""
from __future__ import annotations
from collections import defaultdict
import importlib.util, json, os, sys, time

sys.setrecursionlimit(200000)
_HERE = os.path.dirname(os.path.abspath(__file__))


# ---------------------------------------------------------------------------
# Import dfs_seeded_with_terminals + enumerate_starts unchanged from prior
# stay-saturation probe; import cdo_analyze_terminal unchanged from the prior
# CDO probe.
# ---------------------------------------------------------------------------
def _load_module(filename, modname):
    path = os.path.join(_HERE, filename)
    spec = importlib.util.spec_from_file_location(modname, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

_SS = _load_module("probe_sk_case_b_stay_saturation_2026-04-18.py", "ssprobe")
_CDO = _load_module("probe_sk_case_b_closure_debt_2026-04-19.py", "cdoprobe")

dfs_seeded_with_terminals = _SS.dfs_seeded_with_terminals
enumerate_starts = _SS.enumerate_starts
cdo_analyze_terminal = _CDO.cdo_analyze_terminal


# ---------------------------------------------------------------------------
# Hardcoded subset (canonical iteration order, see audit at script bottom).
# Format per entry: (n, ms, p, l, r, v, s1, s2, label_group)
# label_group is used only for subset_composition reporting.
# ---------------------------------------------------------------------------
SUBSET = [
    # 3 seeds: n=5 ms=(2,2,2,3,4), p=3, l=0, r=0   (sanity-check family)
    (5, (2,2,2,3,4), 3, 0, 0, 0, 1, 2, "n5_2_2_2_3_4_p3_l0r0"),
    (5, (2,2,2,3,4), 3, 0, 0, 1, 0, 2, "n5_2_2_2_3_4_p3_l0r0"),
    (5, (2,2,2,3,4), 3, 0, 0, 2, 0, 1, "n5_2_2_2_3_4_p3_l0r0"),

    # 8 seeds: n=6 ms=(2,3,3,3,3,3) — adversarial dense ternary
    # First 8 in canonical iteration order (p=1, l=0, ...).
    (6, (2,3,3,3,3,3), 1, 0, 0, 0, 1, 2, "n6_dense_ternary"),
    (6, (2,3,3,3,3,3), 1, 0, 0, 1, 0, 2, "n6_dense_ternary"),
    (6, (2,3,3,3,3,3), 1, 0, 0, 2, 0, 1, "n6_dense_ternary"),
    (6, (2,3,3,3,3,3), 1, 0, 1, 0, 1, 2, "n6_dense_ternary"),
    (6, (2,3,3,3,3,3), 1, 0, 1, 1, 0, 2, "n6_dense_ternary"),
    (6, (2,3,3,3,3,3), 1, 0, 1, 2, 0, 1, "n6_dense_ternary"),
    (6, (2,3,3,3,3,3), 1, 0, 2, 0, 1, 2, "n6_dense_ternary"),
    (6, (2,3,3,3,3,3), 1, 0, 2, 1, 0, 2, "n6_dense_ternary"),

    # 5 seeds: n=5 other geometries (3 from (2,2,3,3,3) + 2 from (2,3,3,3,3))
    (5, (2,2,3,3,3), 2, 0, 0, 0, 1, 2, "n5_other_geo"),
    (5, (2,2,3,3,3), 2, 0, 0, 1, 0, 2, "n5_other_geo"),
    (5, (2,2,3,3,3), 2, 0, 0, 2, 0, 1, "n5_other_geo"),
    (5, (2,3,3,3,3), 1, 0, 0, 0, 1, 2, "n5_other_geo"),
    (5, (2,3,3,3,3), 1, 0, 0, 1, 0, 2, "n5_other_geo"),

    # 5 seeds: n=6 other geometries (3 from (2,2,3,3,3,3) + 2 from (2,2,2,3,3,3))
    (6, (2,2,3,3,3,3), 2, 0, 0, 0, 1, 2, "n6_other_geo"),
    (6, (2,2,3,3,3,3), 2, 0, 0, 1, 0, 2, "n6_other_geo"),
    (6, (2,2,3,3,3,3), 2, 0, 0, 2, 0, 1, "n6_other_geo"),
    (6, (2,2,2,3,3,3), 3, 0, 0, 0, 1, 2, "n6_other_geo"),
    (6, (2,2,2,3,3,3), 3, 0, 0, 1, 0, 2, "n6_other_geo"),

    # 5 seeds: n=7 (3 from (2,2,3,3,3,3,3) + 2 from (2,2,2,3,3,3,3))
    (7, (2,2,3,3,3,3,3), 2, 0, 0, 0, 1, 2, "n7"),
    (7, (2,2,3,3,3,3,3), 2, 0, 0, 1, 0, 2, "n7"),
    (7, (2,2,3,3,3,3,3), 2, 0, 0, 2, 0, 1, "n7"),
    (7, (2,2,2,3,3,3,3), 3, 0, 0, 0, 1, 2, "n7"),
    (7, (2,2,2,3,3,3,3), 3, 0, 0, 1, 0, 2, "n7"),
]

# Per-(n, ms) DFS bounds (matches prior probe SWEEP_PLANS).
DFS_BOUNDS = {
    5: (6, 18),
    6: (7, 20),
    7: (8, 22),
}

# Per-seed wall budget. Dense-ternary n=6 gets the upper bound (120s); the
# rest get 60s. Time-cap is sanity bound, NOT a coverage knob.
def per_seed_budget_s(n, ms):
    if n == 6 and ms == (2, 3, 3, 3, 3, 3):
        return 120.0
    return 60.0

# Effectively unbounded terminals/start (no per-start cap).
NO_CAP = 10**9


# ---------------------------------------------------------------------------
# Run a single seed exhaustively (no terminal cap; one wall budget across
# all starts).
# ---------------------------------------------------------------------------
def run_seed_exhaustive(n, ms, p, l, r, v, s1, s2):
    seed_det = {
        (p, l, s1, r): v,
        (p, l, s2, r): v,
        (p, l, v,  r): v,
    }
    L_min, L_max = DFS_BOUNDS[n]
    budget_total = per_seed_budget_s(n, ms)

    starts = enumerate_starts(ms, n, p, l, s1, r, max_starts=3)
    per_start_budget = budget_total / max(1, len(starts))

    all_terminals = []
    full_cycles = []
    timed_out_any = False
    max_depth = 0

    t_seed_start = time.time()
    for s_cfg in starts:
        cycles, terminals, timed_out = dfs_seeded_with_terminals(
            ms, n, seed_det, s_cfg,
            L_min=L_min, L_max=L_max,
            time_budget=per_start_budget,
            max_terminals=NO_CAP,
            early_exit_on_zero_ss=False,   # need ALL terminals for CDO
        )
        full_cycles.extend(cycles)
        for t in terminals:
            all_terminals.append((s_cfg, t))
            # path is t[0]; depth = len(path) (configs visited including start)
            d = len(t[0])
            if d > max_depth:
                max_depth = d
        if timed_out:
            timed_out_any = True

    wall_time = time.time() - t_seed_start

    # CDO classification (only on stuck / closed_unfair terminals; depth_cap
    # is out of CDO scope per spec §5).
    n_terminals_in_scope = 0
    n_cdo_sat = 0
    violators = []
    for s_cfg, (path, movers, det, kind) in all_terminals:
        if kind not in ("stuck", "closed_unfair"):
            continue
        n_terminals_in_scope += 1
        info = cdo_analyze_terminal(path, movers, det, ms, n,
                                    seed_det, s_cfg)
        if info["cdo_satisfied"]:
            n_cdo_sat += 1
        else:
            violators.append({
                "start": list(s_cfg),
                "kind": kind,
                "path": [list(c) for c in path],
                "movers": list(movers),
                "delta": info["delta"],
                "fire_count": info["fire_count"],
                "move_budget": info["move_budget"],
                "blocked": info["blocked"],
            })

    exhaustive = not timed_out_any
    n_violated = len(violators)

    return {
        "n_terminals_total": len(all_terminals),
        "n_terminals_in_scope": n_terminals_in_scope,
        "n_full_cycles": len(full_cycles),
        "n_CDO_satisfied": n_cdo_sat,
        "n_CDO_violated": n_violated,
        "violators": violators,
        "exhaustive": exhaustive,
        "wall_time_s": wall_time,
        "max_depth": max_depth,
        "timed_out": timed_out_any,
    }


# ---------------------------------------------------------------------------
# Sweep + verdict.
# ---------------------------------------------------------------------------
def main():
    print("=" * 72)
    print("CDO subset probe — Case B (exhaustive, hardcoded ~25 seeds)")
    print("=" * 72)
    t0 = time.time()

    # subset_composition
    composition = defaultdict(int)
    for entry in SUBSET:
        composition[entry[8]] += 1

    per_seed = []
    for entry in SUBSET:
        n, ms, p, l, r, v, s1, s2, label = entry
        print(f"\n-- n={n} ms={ms} p={p} l={l} r={r} v={v} s1={s1} s2={s2} "
              f"[{label}]", flush=True)
        budget = per_seed_budget_s(n, ms)
        print(f"   budget={budget:.0f}s  L∈[{DFS_BOUNDS[n][0]},"
              f"{DFS_BOUNDS[n][1]}]  no-terminal-cap", flush=True)
        res = run_seed_exhaustive(n, ms, p, l, r, v, s1, s2)
        tag = "EXHAUSTIVE" if res["exhaustive"] else "UNBOUNDABLE"
        print(f"   tag={tag}  terminals={res['n_terminals_in_scope']}  "
              f"max_depth={res['max_depth']}  "
              f"CDO_sat={res['n_CDO_satisfied']}  "
              f"CDO_vio={res['n_CDO_violated']}  "
              f"wall={res['wall_time_s']:.1f}s", flush=True)

        per_seed.append({
            "seed": {"n": n, "ms": list(ms),
                     "p": p, "l": l, "r": r,
                     "v": v, "s1": s1, "s2": s2,
                     "label_group": label},
            "n_terminals": res["n_terminals_in_scope"],
            "n_terminals_total": res["n_terminals_total"],
            "n_full_cycles": res["n_full_cycles"],
            "max_depth": res["max_depth"],
            "wall_time_s": res["wall_time_s"],
            "exhaustive": res["exhaustive"],
            "n_CDO_satisfied": res["n_CDO_satisfied"],
            "n_CDO_violated": res["n_CDO_violated"],
            "violators_data": res["violators"],
        })

    # Verdict
    n_seeds = len(per_seed)
    n_exhaustive = sum(1 for s in per_seed if s["exhaustive"])
    n_unboundable = n_seeds - n_exhaustive
    n_seeds_with_violators = sum(1 for s in per_seed if s["n_CDO_violated"] > 0)
    # Violators on EXHAUSTIVE-classified seeds (binding for RED-subset).
    n_seeds_with_violators_exhaustive = sum(
        1 for s in per_seed
        if s["exhaustive"] and s["n_CDO_violated"] > 0
    )

    if n_seeds_with_violators_exhaustive >= 1:
        verdict = "RED-subset"
    elif n_exhaustive >= 20 and n_seeds_with_violators == 0:
        verdict = "GREEN-subset"
    elif n_unboundable >= n_seeds // 2 and n_seeds_with_violators_exhaustive == 0:
        verdict = "YELLOW-subset"
    else:
        # Below 20 exhaustive and below 50% unboundable; report best-effort.
        verdict = "INCONCLUSIVE-subset"

    summary = {
        "n_exhaustive": n_exhaustive,
        "n_unboundable": n_unboundable,
        "n_seeds_with_violators": n_seeds_with_violators,
        "n_seeds_with_violators_exhaustive": n_seeds_with_violators_exhaustive,
        "verdict": verdict,
    }

    print("\n" + "=" * 72)
    print("SUMMARY")
    print("=" * 72)
    print(f"  total seeds:               {n_seeds}")
    print(f"  EXHAUSTIVE seeds:          {n_exhaustive}")
    print(f"  UNBOUNDABLE seeds:         {n_unboundable}")
    print(f"  seeds w/ ≥1 CDO violator:  {n_seeds_with_violators}")
    print(f"  seeds w/ violators (exh):  {n_seeds_with_violators_exhaustive}")
    print(f"\n  VERDICT: {verdict}")
    print(f"\n  Elapsed: {time.time() - t0:.1f}s")

    out = {
        "n_subset": n_seeds,
        "subset_composition": dict(composition),
        "per_seed": per_seed,
        "summary": summary,
    }

    out_dir = os.path.join(_HERE, "sk_phase0_out")
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, "case_b_closure_debt_subset.json")
    with open(out_path, "w") as f:
        json.dump(out, f, indent=2, default=str)
    print(f"\n  wrote {out_path}")


if __name__ == "__main__":
    main()
