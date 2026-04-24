#!/usr/bin/env python3
"""Stay-graph saturation probe for A1 / Case B (2026-04-18).

Extension of `probe_sk_case_b_vacuity_2026-04-18.py`. The prior probe
established that no fair simple closed cycle realizes Case B (0/726
seeds). This probe asks the next question:

    For every DFS terminal node T (closed-with-failed-fairness OR stuck
    at no-valid-extension), how many of the n positions are
    "stay-saturated" by the partial cycle prefix (μ_0, ..., μ_{k-1})?

Definitions (per `docs/lean_docs/sk/sk_a1_stay_graph_definition_2026-04-18.md`):

    Triple at q in c:
        τ_q(c) := (c[(q-1) mod n], c[q], c[(q+1) mod n])
    Cycle-visited triple set at q:
        T_q(C) := { τ_q(c_i) : i ∈ 0..k-1 }
    Vertex (q, t) is MOVE-committed iff ∃ i. τ_q(c_i) = t ∧ μ_i = q
    Vertex (q, t) is STAY-committed iff ∃ i. τ_q(c_i) = t ∧ μ_i ≠ q
    Position q is stay-saturated iff every t ∈ T_q(C) is STAY-committed
        AND no vertex at q is MOVE-committed.

For each seed, compute:
    min_stay_saturated(seed) = min over all DFS terminals T of
                                 #{ q : q stay-saturated at T }

Conjecture: min_stay_saturated(seed) ≥ 1 for every seed.

Verdict per §6:
    GREEN  : n_seeds_min_ss_zero == 0
    YELLOW : 1 ≤ n_seeds_min_ss_zero ≤ 36   (5% of 726)
    RED    : n_seeds_min_ss_zero > 36

The DFS enumerator is reused from the prior probe. We do NOT silently
fix bugs — we extend it to also collect terminal nodes.
"""
from __future__ import annotations
from collections import defaultdict
import importlib.util, json, os, sys, time

sys.setrecursionlimit(100000)
_HERE = os.path.dirname(os.path.abspath(__file__))


# ---------------------------------------------------------------------------
# Stay-saturation analysis on a terminal (defined first so DFS can use it).
# ---------------------------------------------------------------------------
def stay_saturation_counts(path, movers, n):
    """Given path = [c_0, c_1, ..., c_k] and movers = [μ_0, ..., μ_{k-1}],
    compute for each q ∈ Fin n:
        T_q = { τ_q(c_i) : i ∈ 0..k-1 }
        For each t ∈ T_q, classify as:
          MOVE if ∃ i. τ_q(c_i) = t ∧ μ_i = q
          STAY if ∃ i. τ_q(c_i) = t ∧ μ_i ≠ q
        q is stay-saturated iff T_q is non-empty AND every t ∈ T_q has
          STAY classification AND no t has MOVE classification.

    Returns:
        ss_positions : set of q that are stay-saturated.
        per_q_classes: dict q -> dict t -> {"MOVE", "STAY", "BOTH"}.
        n_unfair_q   : # positions q that are never the mover.
    """
    k = len(movers)
    per_q_classes = {q: {} for q in range(n)}
    for i in range(k):
        c_i = path[i]
        mu_i = movers[i]
        for q in range(n):
            t = (c_i[(q - 1) % n], c_i[q], c_i[(q + 1) % n])
            cur = per_q_classes[q].get(t)
            if mu_i == q:
                if cur == "STAY":
                    per_q_classes[q][t] = "BOTH"
                elif cur != "BOTH":
                    per_q_classes[q][t] = "MOVE"
            else:
                if cur == "MOVE":
                    per_q_classes[q][t] = "BOTH"
                elif cur != "BOTH":
                    per_q_classes[q][t] = "STAY"
    ss_positions = set()
    for q in range(n):
        triples = per_q_classes[q]
        if not triples:
            continue
        if all(cls == "STAY" for cls in triples.values()):
            ss_positions.add(q)
    movers_set = set(movers)
    n_unfair_q = sum(1 for q in range(n) if q not in movers_set)
    return ss_positions, per_q_classes, n_unfair_q


# ---------------------------------------------------------------------------
# Extended DFS — same enumerator as prior probe but records terminal nodes.
# ---------------------------------------------------------------------------
def dfs_seeded_with_terminals(ms, n, seed_det, start_config,
                              L_min, L_max,
                              time_budget, max_terminals,
                              early_exit_on_zero_ss=True):
    """DFS for fair simple closed cycles starting at start_config.

    Returns:
        cycles    : list of (path[:L], movers, det) for full fair-closed cycles.
        terminals : list of (path, movers, det, kind) for DFS terminals where
                    kind ∈ {"closed_unfair", "stuck"}. path/movers are the
                    sequences at the terminal moment (path is configs visited
                    so far including start_config; len(movers) == len(path)-1
                    for "stuck" leaves; for "closed_unfair", path[-1] returns
                    to start_config).

    Terminal-node policy:
      - "closed_unfair": at some node, an attempted extension leads back to
        start_config but movers (including this fire) != all of Fin n. We
        record the would-be cycle (movers including the closing fire).
      - "stuck": at some node, NO valid extension exists (no firable position
        passes seed/det/simple constraints). We record path/movers as-is.
      - We do NOT record proper-prefix nodes that have at least one valid
        extension — only true leaves.

    To avoid blow-up we cap total recorded terminals (per start) at
    max_terminals; if more would be recorded, we keep the first
    max_terminals. We do NOT cap the DFS itself on terminals (only on
    time_budget and L_max).
    """
    cycles = []
    terminals = []
    seen_cycles = set()
    seen_terminals = set()
    t0 = time.time()
    state = {"timed_out": False, "found_zero_ss": False}

    def maybe_add_terminal(path, movers, det, kind):
        if len(terminals) >= max_terminals:
            return
        # Dedup by (kind, tuple(movers), tuple(path))
        key = (kind, tuple(movers), tuple(path))
        if key in seen_terminals:
            return
        seen_terminals.add(key)
        terminals.append((list(path), list(movers), dict(det), kind))
        # Early exit: if this terminal has 0 stay-saturated positions,
        # we already know min_ss=0 for this seed; signal early termination.
        if early_exit_on_zero_ss:
            ss, _, _ = stay_saturation_counts(path, movers, n)
            if len(ss) == 0:
                state["found_zero_ss"] = True

    def dfs(config, det, path, movers):
        # Time budget check
        if time.time() - t0 > time_budget:
            state["timed_out"] = True
            return
        if state["found_zero_ss"]:
            return
        # Closed?
        if len(path) > 1 and config == start_config:
            # path[-1] == start_config; movers length == len(path)-1
            L = len(movers)
            if L < L_min:
                return
            if set(movers) == set(range(n)):
                # Fair closed cycle.
                norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
                if norm not in seen_cycles:
                    seen_cycles.add(norm)
                    cycles.append((list(path[:L]), list(movers), dict(det)))
            else:
                # Closed but unfair → terminal.
                maybe_add_terminal(path, movers, det, "closed_unfair")
            return
        if len(path) >= L_max:
            # Length cap reached; treat as a (truncated) leaf.
            # Not strictly "stuck" — we mark it as such so it's not silently
            # dropped. Still subject to stay-saturation analysis.
            maybe_add_terminal(path, movers, det, "depth_cap")
            return
        # Try extensions.
        any_extension = False
        for p_fire in range(n):
            Lp = config[(p_fire - 1) % n]
            Sp = config[p_fire]
            Rp = config[(p_fire + 1) % n]
            km = (p_fire, Lp, Sp, Rp)
            forced = det.get(km)
            for new_val in range(ms[p_fire]):
                if new_val == Sp:
                    continue
                if forced is not None and forced != new_val:
                    continue
                new_det = dict(det)
                new_det[km] = new_val
                ok = True
                for i in range(n):
                    if i == p_fire:
                        continue
                    Li = config[(i - 1) % n]
                    Si = config[i]
                    Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si:
                        ok = False
                        break
                    new_det[ki] = Si
                if not ok:
                    continue
                nc = list(config)
                nc[p_fire] = new_val
                nc = tuple(nc)
                if nc != start_config and nc in set(path):
                    # Simple-cycle violation: revisits a non-start config.
                    # This is an extension attempt that fails; not a leaf.
                    continue
                any_extension = True
                dfs(nc, new_det, path + [nc], movers + [p_fire])
                if state["timed_out"] or state["found_zero_ss"]:
                    return
        if not any_extension:
            # Stuck leaf.
            maybe_add_terminal(path, movers, det, "stuck")

    dfs(start_config, dict(seed_det), [start_config], [])
    return cycles, terminals, state["timed_out"]


# ---------------------------------------------------------------------------
# Reuse start-config enumerator from prior probe.
# ---------------------------------------------------------------------------
def enumerate_starts(ms, n, p, l, s1, r, max_starts=5):
    starts = []
    base = [0] * n
    base[(p - 1) % n] = l
    base[p] = s1
    base[(p + 1) % n] = r
    starts.append(tuple(base))
    for i in range(n):
        if i in {p, (p - 1) % n, (p + 1) % n}:
            continue
        if ms[i] < 2:
            continue
        c = list(base)
        c[i] = 1
        starts.append(tuple(c))
        if len(starts) >= max_starts:
            break
    diag = [((i % 2) * (ms[i] - 1)) for i in range(n)]
    diag[(p - 1) % n] = l
    diag[p] = s1
    diag[(p + 1) % n] = r
    starts.append(tuple(diag))
    seen = set()
    out = []
    for s in starts:
        if s not in seen:
            seen.add(s)
            out.append(s)
    return out[:max_starts]


# ---------------------------------------------------------------------------
# Per-seed stay-saturation probe.
# ---------------------------------------------------------------------------
def probe_seed(n, ms, p, l, r, v, s1, s2,
               time_budget, max_terminals_per_start, L_min, L_max,
               max_starts=3):
    """Run extended DFS for one seed across multiple starts. Return:
        min_ss : min over all collected terminals of #stay-saturated positions
        n_terminals : total terminals collected
        n_full_cycles : full fair cycles found (should be 0 per prior probe)
        worst_terminal : (path, movers, ss_set, kind) of a min-witness
                         (the one achieving min_ss; None if no terminals)
    """
    seed_det = {
        (p, l, s1, r): v,
        (p, l, s2, r): v,
        (p, l, v, r): v,
    }
    starts = enumerate_starts(ms, n, p, l, s1, r, max_starts=max_starts)
    per_start_budget = time_budget / max(1, len(starts))
    all_terminals = []
    full_cycles = []
    timed_out_any = False
    found_zero = False
    for s_cfg in starts:
        cycles, terminals, timed_out = dfs_seeded_with_terminals(
            ms, n, seed_det, s_cfg,
            L_min=L_min, L_max=L_max,
            time_budget=per_start_budget,
            max_terminals=max_terminals_per_start,
        )
        full_cycles.extend(cycles)
        all_terminals.extend(terminals)
        if timed_out:
            timed_out_any = True
        # Early-exit across starts: once any start yields a zero-ss terminal,
        # we know min_ss=0 for this seed.
        for path, movers, det, kind in terminals:
            ss, _, _ = stay_saturation_counts(path, movers, n)
            if len(ss) == 0:
                found_zero = True
                break
        if found_zero:
            break

    if not all_terminals:
        # No terminals collected — only full fair cycles (which are not
        # Case B realizations per prior probe). Conjecture is vacuous here.
        return {
            "min_ss": None, "n_terminals": 0,
            "n_full_cycles": len(full_cycles),
            "worst_terminal": None, "timed_out": timed_out_any,
        }

    # Per spec: terminals = closed_unfair + stuck (+ depth_cap). Full fair
    # cycles are NOT counted as terminals (they are not Case B candidates;
    # the prior 726/0 probe established no fair cycle realizes Case B).
    candidates = []
    for path, movers, det, kind in all_terminals:
        ss, _, _ = stay_saturation_counts(path, movers, n)
        candidates.append((len(ss), path, movers, ss, kind))

    candidates.sort(key=lambda x: x[0])
    min_ss = candidates[0][0]
    worst = candidates[0]
    return {
        "min_ss": min_ss,
        "n_terminals": len(all_terminals),
        "n_full_cycles": len(full_cycles),
        "worst_terminal": {
            "kind": worst[4],
            "path": [list(c) for c in worst[1]],
            "movers": worst[2],
            "stay_saturated_positions": sorted(worst[3]),
        },
        "timed_out": timed_out_any,
    }


# ---------------------------------------------------------------------------
# Sweep over seeds (mirror prior probe's plan exactly).
# ---------------------------------------------------------------------------
SWEEP_PLANS = [
    # (n, [ms...], time_per_seed (s), max_terminals_per_start, L_min, L_max)
    (5, [(2,2,3,3,3), (2,3,3,3,3), (2,2,2,3,4)],     1.0, 60,  6, 18),
    (6, [(2,2,3,3,3,3), (2,2,2,3,3,3), (2,3,3,3,3,3)], 1.5, 60,  7, 20),
    (7, [(2,2,3,3,3,3,3), (2,2,2,3,3,3,3)],          2.0, 60,  8, 22),
]


def run_sweep(time_cap_s):
    t0 = time.time()
    by_seed = []          # list of dicts, one per seed
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
            n_zero = 0
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
                                        print("  [wall-time cap reached mid-ms]",
                                              flush=True)
                                        return (by_seed, by_n_data,
                                                timed_out_seeds, True)
                                    res = probe_seed(
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
                                        "min_ss": res["min_ss"],
                                        "n_terminals": res["n_terminals"],
                                        "n_full_cycles": res["n_full_cycles"],
                                        "timed_out": res["timed_out"],
                                        "worst_terminal": res["worst_terminal"],
                                    }
                                    by_seed.append(seed_rec)
                                    by_n_data[n].append(seed_rec)
                                    if res["min_ss"] == 0:
                                        n_zero += 1
            print(f"   seeds={n_seeds}  min_ss==0: {n_zero}",
                  flush=True)
    return by_seed, by_n_data, timed_out_seeds, False


def summarize(by_seed, by_n_data, timed_out_seeds, hit_cap):
    def stats_block(seeds):
        mins = [s["min_ss"] for s in seeds if s["min_ss"] is not None]
        mins_sorted = sorted(mins)
        if not mins:
            return {
                "n_seeds": len(seeds),
                "n_seeds_with_terminals": 0,
                "min_min_ss": None, "max_min_ss": None,
                "median_min_ss": None,
                "n_seeds_min_ss_zero": 0,
                "n_seeds_min_ss_ge_1": 0,
            }
        med = mins_sorted[len(mins_sorted) // 2]
        return {
            "n_seeds": len(seeds),
            "n_seeds_with_terminals": len(mins),
            "min_min_ss": min(mins),
            "max_min_ss": max(mins),
            "median_min_ss": med,
            "n_seeds_min_ss_zero": sum(1 for x in mins if x == 0),
            "n_seeds_min_ss_ge_1": sum(1 for x in mins if x >= 1),
        }

    by_n_summary = {}
    for n in sorted(by_n_data):
        by_n_summary[str(n)] = stats_block(by_n_data[n])

    overall = stats_block(by_seed)
    n_zero = overall["n_seeds_min_ss_zero"]
    n_eq1 = sum(1 for s in by_seed
                if s["min_ss"] is not None and s["min_ss"] == 1)
    n_ge2 = sum(1 for s in by_seed
                if s["min_ss"] is not None and s["min_ss"] >= 2)

    if n_zero == 0:
        verdict = "GREEN"
    elif n_zero <= 36:
        verdict = "YELLOW"
    else:
        verdict = "RED"

    # Top 5 exceptions: seeds with min_ss == 0, ranked by (n, ms, p, l, r, v, s1, s2)
    exceptions = []
    for s in by_seed:
        if s["min_ss"] == 0:
            exceptions.append(s)
    exceptions.sort(key=lambda s: (s["n"], tuple(s["ms"]),
                                    s["p"], s["l"], s["r"],
                                    s["v"], s["s1"], s["s2"]))
    top_exceptions = exceptions[:5]

    return {
        "n_seeds": len(by_seed),
        "by_n": by_n_summary,
        "exceptions": top_exceptions,
        "global": {
            "n_seeds_min_ss_zero": n_zero,
            "n_seeds_min_ss_eq_1": n_eq1,
            "n_seeds_min_ss_ge_2": n_ge2,
            "n_timed_out_seeds": timed_out_seeds,
            "hit_time_cap": hit_cap,
            "verdict": verdict,
        },
    }


def main():
    print("=" * 72)
    print("Stay-graph saturation probe — Case B")
    print("=" * 72)
    t0 = time.time()
    time_cap_s = 55 * 60   # below 60-min hard cap
    by_seed, by_n_data, timed_out_seeds, hit_cap = run_sweep(time_cap_s)

    summary = summarize(by_seed, by_n_data, timed_out_seeds, hit_cap)

    print("\n" + "=" * 72)
    print("SUMMARY")
    print("=" * 72)
    print(f"  total seeds: {summary['n_seeds']}")
    for n_str, blk in summary["by_n"].items():
        print(f"   n={n_str}: seeds={blk['n_seeds']} "
              f"with_terminals={blk['n_seeds_with_terminals']} "
              f"min_min_ss={blk['min_min_ss']} "
              f"max_min_ss={blk['max_min_ss']} "
              f"median={blk['median_min_ss']} "
              f"#min_ss==0: {blk['n_seeds_min_ss_zero']} "
              f"#min_ss>=1: {blk['n_seeds_min_ss_ge_1']}")
    g = summary["global"]
    print(f"\n  GLOBAL: zero={g['n_seeds_min_ss_zero']} "
          f"eq1={g['n_seeds_min_ss_eq_1']} ge2={g['n_seeds_min_ss_ge_2']}")
    print(f"  Timed-out seeds: {g['n_timed_out_seeds']}")
    print(f"  Hit time cap: {g['hit_time_cap']}")
    print(f"\n  VERDICT: {g['verdict']}")
    print(f"\n  Elapsed: {time.time() - t0:.1f}s")

    out_dir = os.path.join(_HERE, "sk_phase0_out")
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, "case_b_stay_saturation.json")
    with open(out_path, "w") as f:
        json.dump(summary, f, indent=2, default=str)
    print(f"\n  wrote {out_path}")


if __name__ == "__main__":
    main()
