#!/usr/bin/env python3
"""Case B vacuity probe for f-injectivity-on-cycles lemma (2026-04-18).

Goal: determine if Case B (T(v) = v with two distinct cycle-active sources
(l, s_1, r), (l, s_2, r) both firing to v at position p) can be realized
by ANY fair simple closed good cycle. Constructive: seed f-tables with
the Case B configuration baked in, then enumerate cycles respecting the
seed. Post-filter for actual realization.

This is distinct from the L/L* = 1 sweep, which scanned naturally-
occurring cycles. Here we *try to construct* a Case B witness.

Seed protocol: for each (p, l, r) with m_p >= 3 and each distinct triple
(v, s_1, s_2) in Fin m_p:
    det-seed = {
        (p, l, s_1, r): v,   # s_1 fires to v at p
        (p, l, s_2, r): v,   # s_2 fires to v at p
        (p, l, v,   r): v,   # v is a stay-fixed-point at (l, r)
    }
DFS from c_start with p-triple (l, s_1, r), enforcing seed consistency.
The seed pinning forces p to fire at c_start (to avoid det contradiction
at (p, l, s_1, r)), land at c_1 with p-triple (l, v, r), and require some
q != p to fire there (since p is stay at (l, v, r) by seed).

Post-filter: a cycle is a Case B HIT iff it visits all three source
triples (s_1, v, s_2 middles at p with neighbors (l, r)) AND uses each
in its fired role — (l, s_1, r) fires at p to v, (l, v, r) is present
with p stay, (l, s_2, r) fires at p to v.

Interpretation:
  - 0 hits across broad seed sweep: Case B is structurally vacuous in
    fair simple cycles. Strong evidence the conjecture's full lemma
    holds even without Case B's analytical closure.
  - >=1 hit: Case B is realizable. Dissect the witness.

Output: JSON dump of hits (if any) + aggregate counts per n.
"""
from __future__ import annotations
from collections import defaultdict, Counter
from itertools import product as iproduct
import importlib.util, json, os, sys, time

sys.setrecursionlimit(100000)
_HERE = os.path.dirname(os.path.abspath(__file__))


def dfs_seeded(ms, n, seed_det, start_config, L_min, L_max,
               time_budget, max_cycles):
    """DFS for fair simple closed cycles starting from start_config,
    with det pre-populated by seed_det (forced entries).

    Fair = every position fires at least once.
    Simple = configs on path are pairwise distinct.
    Closed = last step returns to start_config.
    """
    found = []
    seen = set()
    t0 = time.time()

    def dfs(config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            return
        if len(path) > 1 and config == start_config:
            if set(movers) != set(range(n)):
                return
            L = len(movers)
            if L < L_min:
                return
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen:
                seen.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max:
            return
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
                    continue
                dfs(nc, new_det, path + [nc], movers + [p_fire])

    dfs(start_config, dict(seed_det), [start_config], [])
    return found


def check_case_b(cycle, det, p, l, r, v, s1, s2, n):
    """Post-filter: does cycle realize Case B at (p, l, r, v, s1, s2)?

    Returns dict of which conditions met. Hit iff all three:
    - some config has p-triple (l, s1, r) AND det fires p to v
    - some config has p-triple (l, v, r) AND det has p stay (val = v)
    - some config has p-triple (l, s2, r) AND det fires p to v
    """
    fires_s1 = False
    stays_v  = False
    fires_s2 = False
    # Collect firing steps for provenance
    fires_s1_steps = []
    fires_s2_steps = []
    stay_v_steps   = []
    for i, c in enumerate(cycle):
        Lp = c[(p - 1) % n]
        Sp = c[p]
        Rp = c[(p + 1) % n]
        if Lp != l or Rp != r:
            continue
        key = (p, Lp, Sp, Rp)
        val = det.get(key)
        if val is None:
            continue
        if Sp == s1 and val == v:
            fires_s1 = True
            fires_s1_steps.append(i)
        elif Sp == s2 and val == v:
            fires_s2 = True
            fires_s2_steps.append(i)
        elif Sp == v and val == v:
            stays_v = True
            stay_v_steps.append(i)
    return {
        "fires_s1": fires_s1,
        "stays_v": stays_v,
        "fires_s2": fires_s2,
        "case_b_hit": fires_s1 and stays_v and fires_s2,
        "fires_s1_steps": fires_s1_steps,
        "fires_s2_steps": fires_s2_steps,
        "stay_v_steps": stay_v_steps,
    }


def enumerate_starts(ms, n, p, l, s1, r, max_starts=5):
    """Generate a handful of start configs with p-triple (l, s1, r)."""
    # Base: (p-1) = l, p = s1, (p+1) = r, others 0
    starts = []
    base = [0] * n
    base[(p - 1) % n] = l
    base[p]           = s1
    base[(p + 1) % n] = r
    starts.append(tuple(base))

    # Variation 1: set each remaining position to 1 (capped at m_i - 1)
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

    # Diagonal: alternate 0/max
    diag = [((i % 2) * (ms[i] - 1)) for i in range(n)]
    diag[(p - 1) % n] = l
    diag[p]           = s1
    diag[(p + 1) % n] = r
    starts.append(tuple(diag))

    # Dedup
    seen = set()
    out = []
    for s in starts:
        if s not in seen:
            seen.add(s)
            out.append(s)
    return out[:max_starts]


def run_probe(n, ms, time_per_seed, max_cycles_per_seed, L_min, L_max):
    """Run Case B probe for one (n, ms). Return list of hits + stats."""
    hits = []
    stats = {
        "ms": list(ms),
        "seeds_tried": 0,
        "cycles_found": 0,
        "seeds_with_cycles": 0,
        "partial_hits": 0,       # had some but not all 3 conditions
        "full_hits": 0,          # all 3 conditions
        "time_spent": 0.0,
    }
    t0 = time.time()

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
                            # Seed: distinct v, s1, s2 in Fin m_p
                            seed_det = {
                                (p, l, s1, r): v,
                                (p, l, s2, r): v,
                                (p, l, v,  r): v,
                            }
                            stats["seeds_tried"] += 1

                            any_cycle = False
                            saw_partial = False
                            starts = enumerate_starts(ms, n, p, l, s1, r,
                                                       max_starts=3)
                            budget = time_per_seed / max(1, len(starts))
                            for s_cfg in starts:
                                cycles = dfs_seeded(
                                    ms, n, seed_det, s_cfg,
                                    L_min=L_min, L_max=L_max,
                                    time_budget=budget,
                                    max_cycles=max_cycles_per_seed,
                                )
                                for cycle, movers, det in cycles:
                                    any_cycle = True
                                    stats["cycles_found"] += 1
                                    rc = check_case_b(cycle, det, p, l, r,
                                                       v, s1, s2, n)
                                    if rc["case_b_hit"]:
                                        stats["full_hits"] += 1
                                        hits.append({
                                            "n": n,
                                            "ms": list(ms),
                                            "p": p, "l": l, "r": r,
                                            "v": v, "s1": s1, "s2": s2,
                                            "cycle": [list(c) for c in cycle],
                                            "movers": movers,
                                            "det": {
                                                str(k): val
                                                for k, val in det.items()
                                            },
                                            "start": list(s_cfg),
                                            "rc": rc,
                                        })
                                    elif (rc["fires_s1"] or rc["fires_s2"]
                                          or rc["stays_v"]):
                                        saw_partial = True
                            if any_cycle:
                                stats["seeds_with_cycles"] += 1
                            if saw_partial and not any(
                                h["p"] == p and h["l"] == l and h["r"] == r
                                and h["v"] == v and h["s1"] == s1 and h["s2"] == s2
                                for h in hits
                            ):
                                stats["partial_hits"] += 1

    stats["time_spent"] = time.time() - t0
    return hits, stats


# --- sweep plan ---
SWEEP_PLANS = [
    # (n, [ms...], time_per_seed (s), max_cycles_per_seed, L_min, L_max)
    (5, [(2,2,3,3,3), (2,3,3,3,3), (2,2,2,3,4)], 1.0, 3,  6, 18),
    (6, [(2,2,3,3,3,3), (2,2,2,3,3,3), (2,3,3,3,3,3)], 1.5, 3,  7, 20),
    (7, [(2,2,3,3,3,3,3), (2,2,2,3,3,3,3)], 2.0, 3,  8, 22),
]


def main():
    print("=" * 72)
    print("Case B vacuity probe — f-injectivity-on-cycles")
    print("=" * 72)
    all_hits = []
    all_stats = []
    t0 = time.time()
    time_cap_s = 45 * 60  # hard cap at 45 min

    for n, ms_list, tps, mcps, L_min, L_max in SWEEP_PLANS:
        for ms in ms_list:
            if time.time() - t0 > time_cap_s:
                print(f"  [wall-time cap {time_cap_s}s reached, stopping]")
                break
            print(f"\n-- n={n}  ms={ms}  tps={tps}s  mcps={mcps} "
                  f"L∈[{L_min}, {L_max}]", flush=True)
            hits, stats = run_probe(n, ms, tps, mcps, L_min, L_max)
            all_hits.extend(hits)
            stats["n"] = n
            all_stats.append(stats)
            print(f"   seeds={stats['seeds_tried']} "
                  f"cycles={stats['cycles_found']} "
                  f"seeds_w_cycles={stats['seeds_with_cycles']} "
                  f"partial_hits={stats['partial_hits']} "
                  f"FULL_HITS={stats['full_hits']} "
                  f"dt={stats['time_spent']:.1f}s", flush=True)
        if time.time() - t0 > time_cap_s:
            break

    # summary
    print("\n" + "=" * 72)
    print("SUMMARY")
    print("=" * 72)
    by_n = defaultdict(lambda: {"seeds": 0, "cycles": 0, "partial": 0, "full": 0})
    for s in all_stats:
        by_n[s["n"]]["seeds"]   += s["seeds_tried"]
        by_n[s["n"]]["cycles"]  += s["cycles_found"]
        by_n[s["n"]]["partial"] += s["partial_hits"]
        by_n[s["n"]]["full"]    += s["full_hits"]
    print(f"  {'n':>3} {'seeds':>7} {'cycles':>8} "
          f"{'partial':>8} {'FULL_HITS':>10}")
    for n in sorted(by_n):
        d = by_n[n]
        print(f"  {n:>3} {d['seeds']:>7} {d['cycles']:>8} "
              f"{d['partial']:>8} {d['full']:>10}")

    grand_full = sum(d["full"] for d in by_n.values())
    print(f"\n  GRAND TOTAL full Case B hits: {grand_full}")
    print(f"  Elapsed: {time.time() - t0:.1f}s")

    # verdict
    print("\n" + "=" * 72)
    if grand_full == 0:
        print("VERDICT: 0 Case B hits across broad constructive seed sweep.")
        print("  Case B is structurally VACUOUS in fair simple cycles.")
        print("  Strong evidence that sourceTriple_injective + fixed-point")
        print("  property rules out Case B implicitly.")
    else:
        print(f"VERDICT: {grand_full} Case B witnesses found. Case B is REAL.")
        print("  Sample witness(es) preserved for analytical dissection.")
    print("=" * 72)

    # dump
    out_dir = os.path.join(_HERE, "sk_phase0_out")
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, "case_b_vacuity.json")
    with open(out_path, "w") as f:
        json.dump({
            "grand_full_hits": grand_full,
            "by_n": {str(n): d for n, d in by_n.items()},
            "stats_per_ms": all_stats,
            "hits": all_hits,
        }, f, indent=2, default=str)
    print(f"\n  wrote {out_path}")


if __name__ == "__main__":
    main()
