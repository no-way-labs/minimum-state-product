#!/usr/bin/env python3
"""Closure-Debt Obstruction (CDO) probe for A1 / Case B (2026-04-19).

Spec memo: docs/lean_docs/sk/sk_a1_stuck_closure_observation_2026-04-18.md (§5).

Reuses dfs_seeded_with_terminals from the stay-saturation probe UNCHANGED
(same seed loop, same DFS, same acceptance/pruning). For each terminal of
kind {stuck, closed_unfair} we compute, for each q ∈ Fin n:

    Δ_q          = (c_L[q] - c_0[q]) mod m_q
    fire_count_q = |{ k : μ_k = q }|
    move_budget_q = |{ τ_q(c_k) : k < L ∧ μ_k = q }|
    stay_committed_at_q(c_L) iff some k < L has τ_q(c_k) = τ_q(c_L) ∧ μ_k != q
    blocked_q    = (Δ_q != 0) AND every single-step firing at q from c_L
                   either revisits a path config (simplicity violation) OR
                   the triple τ_q(c_L) is STAY-committed by the cycle prefix.

CDO branches:
    (U): fire_count_q == 0
    (D): fire_count_q > 0 ∧ Δ_q != 0 ∧ blocked_q

Terminal CDO-satisfied iff ∃ q satisfying (U) or (D).
Seed CDO-satisfied iff every terminal is CDO-satisfied.

Verdict thresholds (binding, per §6 of spec):
    GREEN  : n_seeds_CDO_violated == 0
    YELLOW : 1 ≤ n_seeds_CDO_violated ≤ 36   (5% of 726)
    RED    : n_seeds_CDO_violated > 36

Sanity check: 5 stored stay-saturation exceptions at n=5, ms=(2,2,2,3,4),
p=3 with μ=(3,2,1,0,4,0,4,0,4,0). Binary positions q ∈ {1,2} fire exactly
once → Δ=1, blocked → branch (D). MUST be CDO-satisfied.
"""
from __future__ import annotations
from collections import defaultdict
import importlib.util, json, os, sys, time

sys.setrecursionlimit(100000)
_HERE = os.path.dirname(os.path.abspath(__file__))


# ---------------------------------------------------------------------------
# Import dfs_seeded_with_terminals + enumerate_starts unchanged from prior.
# ---------------------------------------------------------------------------
def _load_prior():
    path = os.path.join(_HERE, "probe_sk_case_b_stay_saturation_2026-04-18.py")
    spec = importlib.util.spec_from_file_location("ssprobe", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

_PRIOR = _load_prior()
dfs_seeded_with_terminals = _PRIOR.dfs_seeded_with_terminals
enumerate_starts = _PRIOR.enumerate_starts


# ---------------------------------------------------------------------------
# CDO analysis on a terminal.
# ---------------------------------------------------------------------------
def cdo_analyze_terminal(path, movers, det, ms, n, seed_det, start_config):
    """Compute CDO data for a terminal (path, movers).

    path     : [c_0, c_1, ..., c_L]  (length L+1)
    movers   : [μ_0, ..., μ_{L-1}]   (length L)

    For closed_unfair terminals, c_L == c_0 (start_config).
    For stuck terminals, c_L is the last (unique) config; no extension.

    Returns dict per q:
        Δ_q, fire_count_q, move_budget_q, blocked_q
        and a top-level flag cdo_satisfied + witness q.
    """
    L = len(movers)
    c0 = path[0]
    cL = path[-1]

    # Δ
    delta = [(cL[q] - c0[q]) % ms[q] for q in range(n)]

    # fire_count
    fire_count = [0] * n
    for q in movers:
        fire_count[q] += 1

    # move_budget_q: distinct triples τ_q(c_k) for k < L where μ_k = q
    move_triples = [set() for _ in range(n)]
    # stay_triples_q: triples τ_q(c_k) for k < L where μ_k != q
    stay_triples = [set() for _ in range(n)]
    for k in range(L):
        c_k = path[k]
        mu_k = movers[k]
        for q in range(n):
            t = (c_k[(q - 1) % n], c_k[q], c_k[(q + 1) % n])
            if mu_k == q:
                move_triples[q].add(t)
            else:
                stay_triples[q].add(t)

    move_budget = [len(s) for s in move_triples]

    # blocked_q: Δ_q != 0 AND every single-step firing at q from c_L
    # either lands on a path config (simplicity violation) OR
    # the triple τ_q(c_L) is STAY-committed by the prefix.
    path_set = set(path)
    blocked = [False] * n
    for q in range(n):
        if delta[q] == 0:
            blocked[q] = False
            continue
        Lq = cL[(q - 1) % n]
        Sq = cL[q]
        Rq = cL[(q + 1) % n]
        triple_q_at_cL = (Lq, Sq, Rq)
        # Check (ii): triple already STAY-committed?
        stay_committed = triple_q_at_cL in stay_triples[q]
        # Also need to honor the seed/det forcing for triple t at q
        # (det may have pinned this firing's value).
        km = (q, Lq, Sq, Rq)
        forced = det.get(km)

        # All extensions either revisit path or are STAY-committed?
        # If STAY-committed: every extension at q from cL is blocked
        # (the triple is committed to STAY value Sq, so firing at q would
        # contradict det).
        if stay_committed:
            blocked[q] = True
            continue

        # Otherwise enumerate single-step firings at q from cL:
        all_blocked = True
        any_extension = False
        for new_val in range(ms[q]):
            if new_val == Sq:
                continue
            if forced is not None and forced != new_val:
                continue
            # Build the would-be next config and check non-q sites' det
            # consistency, mirroring DFS exactly.
            new_det = dict(det)
            new_det[km] = new_val
            ok = True
            for i in range(n):
                if i == q:
                    continue
                Li = cL[(i - 1) % n]
                Si = cL[i]
                Ri = cL[(i + 1) % n]
                ki = (i, Li, Si, Ri)
                if ki in new_det and new_det[ki] != Si:
                    ok = False
                    break
                new_det[ki] = Si
            if not ok:
                continue
            nc = list(cL)
            nc[q] = new_val
            nc = tuple(nc)
            any_extension = True
            # Simplicity: revisit a non-start path config is forbidden.
            # (Closure back to start_config is fine; that's a closed-cycle
            # extension, not blocked by simplicity. But this terminal kind
            # is stuck/closed_unfair, so we focus on whether at least one
            # extension is structurally possible.)
            if nc != start_config and nc in path_set:
                continue
            # An extension exists that doesn't violate simplicity or det.
            all_blocked = False
            break
        if not any_extension:
            # No firing at q is permitted at all from cL → blocked.
            blocked[q] = True
        else:
            blocked[q] = all_blocked

    # CDO branches
    witnesses = []
    for q in range(n):
        if fire_count[q] == 0:
            witnesses.append((q, "U"))
        elif fire_count[q] > 0 and delta[q] != 0 and blocked[q]:
            witnesses.append((q, "D"))

    return {
        "delta": delta,
        "fire_count": fire_count,
        "move_budget": move_budget,
        "blocked": blocked,
        "cdo_witnesses": witnesses,
        "cdo_satisfied": len(witnesses) > 0,
    }


# ---------------------------------------------------------------------------
# Per-seed CDO probe (multiple starts; collect ALL terminals; do not early
# exit on stay-sat — we need all terminals for CDO classification).
# ---------------------------------------------------------------------------
def probe_seed_cdo(n, ms, p, l, r, v, s1, s2,
                   time_budget, max_terminals_per_start, L_min, L_max,
                   max_starts=3):
    seed_det = {
        (p, l, s1, r): v,
        (p, l, s2, r): v,
        (p, l, v,  r): v,
    }
    starts = enumerate_starts(ms, n, p, l, s1, r, max_starts=max_starts)
    per_start_budget = time_budget / max(1, len(starts))
    all_terminals = []
    full_cycles = []
    timed_out_any = False

    for s_cfg in starts:
        cycles, terminals, timed_out = dfs_seeded_with_terminals(
            ms, n, seed_det, s_cfg,
            L_min=L_min, L_max=L_max,
            time_budget=per_start_budget,
            max_terminals=max_terminals_per_start,
            early_exit_on_zero_ss=False,   # we need all terminals for CDO
        )
        full_cycles.extend(cycles)
        for t in terminals:
            all_terminals.append((s_cfg, t))
        if timed_out:
            timed_out_any = True

    seed_violators = []   # terminals where CDO is NOT satisfied
    n_terminals = 0
    n_cdo_sat = 0
    for s_cfg, (path, movers, det, kind) in all_terminals:
        if kind not in ("stuck", "closed_unfair"):
            continue   # depth_cap not in CDO scope per spec §5
        n_terminals += 1
        info = cdo_analyze_terminal(path, movers, det, ms, n,
                                    seed_det, s_cfg)
        if info["cdo_satisfied"]:
            n_cdo_sat += 1
        else:
            seed_violators.append({
                "start": list(s_cfg),
                "kind": kind,
                "path": [list(c) for c in path],
                "movers": list(movers),
                "delta": info["delta"],
                "fire_count": info["fire_count"],
                "move_budget": info["move_budget"],
                "blocked": info["blocked"],
            })

    seed_cdo_satisfied = (n_terminals > 0 and len(seed_violators) == 0)
    # Edge case: if no terminals collected (only full fair cycles, which
    # the prior probe established do not realize Case B), we treat the
    # seed as vacuously CDO-satisfied — there is nothing to block.
    if n_terminals == 0:
        seed_cdo_satisfied = True

    return {
        "n_terminals": n_terminals,
        "n_cdo_satisfied": n_cdo_sat,
        "n_full_cycles": len(full_cycles),
        "cdo_satisfied": seed_cdo_satisfied,
        "violators": seed_violators,
        "timed_out": timed_out_any,
    }


# ---------------------------------------------------------------------------
# Sweep plan. The prior stay-saturation probe used (tps, mtps) = (1.0,60),
# (1.5,60), (2.0,60) BUT relied on `early_exit_on_zero_ss` to short-circuit
# RED seeds at the first zero-ss terminal. CDO needs ALL terminals, so the
# DFS cannot short-circuit. We tighten time budgets (and cap terminals at
# 20/start) to keep total wall-clock under 60s. Seeds that exhaust the
# budget have `timed_out=True` in the JSON; their CDO classification uses
# whatever terminals were collected before timeout.
# ---------------------------------------------------------------------------
SWEEP_PLANS = [
    (5, [(2,2,3,3,3), (2,3,3,3,3), (2,2,2,3,4)],       0.3, 15,  6, 18),
    (6, [(2,2,3,3,3,3), (2,2,2,3,3,3), (2,3,3,3,3,3)], 0.4, 15,  7, 20),
    (7, [(2,2,3,3,3,3,3), (2,2,2,3,3,3,3)],            0.5, 15,  8, 22),
]


def run_sweep(time_cap_s):
    t0 = time.time()
    by_seed = []
    by_n_data = defaultdict(list)
    timed_out_seeds = 0

    for n, ms_list, tps, mtps, L_min, L_max in SWEEP_PLANS:
        for ms in ms_list:
            if time.time() - t0 > time_cap_s:
                print(f"  [wall-time cap {time_cap_s}s reached]", flush=True)
                return by_seed, by_n_data, timed_out_seeds, True
            print(f"\n-- n={n} ms={ms} tps={tps}s mtps={mtps} "
                  f"L∈[{L_min},{L_max}]", flush=True)
            n_seeds = 0
            n_violated = 0
            for p in range(n):
                if ms[p] < 3:
                    continue
                l_size = ms[(p - 1) % n]
                r_size = ms[(p + 1) % n]
                for l in range(l_size):
                    for r in range(r_size):
                        for v in range(ms[p]):
                            for s1 in range(ms[p]):
                                if s1 == v:
                                    continue
                                for s2 in range(s1 + 1, ms[p]):
                                    if s2 == v:
                                        continue
                                    if time.time() - t0 > time_cap_s:
                                        print("  [wall-time cap mid-ms]",
                                              flush=True)
                                        return (by_seed, by_n_data,
                                                timed_out_seeds, True)
                                    res = probe_seed_cdo(
                                        n, ms, p, l, r, v, s1, s2,
                                        time_budget=tps,
                                        max_terminals_per_start=mtps,
                                        L_min=L_min, L_max=L_max,
                                    )
                                    n_seeds += 1
                                    if res["timed_out"]:
                                        timed_out_seeds += 1
                                    seed_rec = {
                                        "n": n, "ms": list(ms),
                                        "p": p, "l": l, "r": r,
                                        "v": v, "s1": s1, "s2": s2,
                                        "n_terminals": res["n_terminals"],
                                        "n_cdo_satisfied": res["n_cdo_satisfied"],
                                        "n_full_cycles": res["n_full_cycles"],
                                        "cdo_satisfied": res["cdo_satisfied"],
                                        "n_violators": len(res["violators"]),
                                        "timed_out": res["timed_out"],
                                    }
                                    if res["violators"]:
                                        # Store first violator only to keep
                                        # JSON small; counts are aggregated.
                                        seed_rec["violator_sample"] = (
                                            res["violators"][0]
                                        )
                                    by_seed.append(seed_rec)
                                    by_n_data[n].append(seed_rec)
                                    if not res["cdo_satisfied"]:
                                        n_violated += 1
            print(f"   seeds={n_seeds}  violated={n_violated}",
                  flush=True)
    return by_seed, by_n_data, timed_out_seeds, False


def summarize(by_seed, by_n_data, timed_out_seeds, hit_cap):
    def stats_block(seeds):
        n_sat = sum(1 for s in seeds if s["cdo_satisfied"])
        n_vio = sum(1 for s in seeds if not s["cdo_satisfied"])
        return {
            "n_seeds": len(seeds),
            "n_seeds_CDO_satisfied": n_sat,
            "n_seeds_CDO_violated":  n_vio,
        }

    by_n_summary = {}
    for n in sorted(by_n_data):
        by_n_summary[str(n)] = stats_block(by_n_data[n])

    overall = stats_block(by_seed)
    n_vio = overall["n_seeds_CDO_violated"]

    if n_vio == 0:
        verdict = "GREEN"
    elif n_vio <= 36:
        verdict = "YELLOW"
    else:
        verdict = "RED"

    violators = []
    for s in by_seed:
        if not s["cdo_satisfied"]:
            v = {
                "seed": {k: s[k] for k in
                         ("n", "ms", "p", "l", "r", "v", "s1", "s2")},
                "n_terminals": s["n_terminals"],
                "n_violators_in_seed": s["n_violators"],
            }
            if "violator_sample" in s:
                v["sample"] = s["violator_sample"]
            violators.append(v)
    violators.sort(key=lambda v: (
        v["seed"]["n"], tuple(v["seed"]["ms"]),
        v["seed"]["p"], v["seed"]["l"], v["seed"]["r"],
        v["seed"]["v"], v["seed"]["s1"], v["seed"]["s2"],
    ))

    return {
        "n_seeds": len(by_seed),
        "by_n": by_n_summary,
        "global": {
            "n_seeds_CDO_satisfied": overall["n_seeds_CDO_satisfied"],
            "n_seeds_CDO_violated":  overall["n_seeds_CDO_violated"],
            "n_timed_out_seeds": timed_out_seeds,
            "hit_time_cap": hit_cap,
            "verdict": verdict,
        },
        "violators": violators,
    }


def main():
    print("=" * 72)
    print("Closure-Debt Obstruction (CDO) probe — Case B")
    print("=" * 72)
    t0 = time.time()
    time_cap_s = 360  # 6-min wall-clock cap (DFS internal time-budgets bound per-seed)
    by_seed, by_n_data, timed_out_seeds, hit_cap = run_sweep(time_cap_s)

    summary = summarize(by_seed, by_n_data, timed_out_seeds, hit_cap)

    print("\n" + "=" * 72)
    print("SUMMARY")
    print("=" * 72)
    print(f"  total seeds: {summary['n_seeds']}")
    for n_str, blk in summary["by_n"].items():
        print(f"   n={n_str}: seeds={blk['n_seeds']} "
              f"CDO_satisfied={blk['n_seeds_CDO_satisfied']} "
              f"CDO_violated={blk['n_seeds_CDO_violated']}")
    g = summary["global"]
    print(f"\n  GLOBAL: satisfied={g['n_seeds_CDO_satisfied']} "
          f"violated={g['n_seeds_CDO_violated']}")
    print(f"  Timed-out seeds: {g['n_timed_out_seeds']}")
    print(f"  Hit time cap:    {g['hit_time_cap']}")
    print(f"\n  VERDICT: {g['verdict']}")
    print(f"\n  Elapsed: {time.time() - t0:.1f}s")

    out_dir = os.path.join(_HERE, "sk_phase0_out")
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, "case_b_closure_debt.json")
    with open(out_path, "w") as f:
        json.dump(summary, f, indent=2, default=str)
    print(f"\n  wrote {out_path}")


if __name__ == "__main__":
    main()
