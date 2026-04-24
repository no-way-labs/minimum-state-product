#!/usr/bin/env python3
"""Phase 2.1 tier-1 feasibility probe — per-config β match count.

For each cycle, compute for each c ∈ C:
    match(c) = #{positions p : c's local triple at p (c[p-1],c[p],c[p+1])
                equals the target triple of some det move entry at p}

Σβ = Σ_c match(c), so Σβ/|C| = Σβ/L = avg match.

If max_{c,cycle} match(c) ≤ 2 uniformly over 1190-cycle sweep:
  → tier 1 (Σβ ≤ 2L) provable via per-config bound.
If max is 3 or 4 sometimes:
  → tier 2 (Σβ ≤ 2.5L or 3L) — per-config hotspot, averaging helps.
If max grows with n:
  → tier 3, native_decide carve-out stays.

GO for tier-1 proof attempt iff max ≤ 2 uniformly.
"""
from __future__ import annotations
from collections import Counter, defaultdict
import importlib.util, json, os, sys

sys.setrecursionlimit(100000)
_HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location(
    "probe_c", os.path.join(_HERE, "probe_sk_hamming1_chain_closure_2026-04-17.py"))
probe_c = importlib.util.module_from_spec(spec); spec.loader.exec_module(probe_c)

enumerate_cycles_multistart = probe_c.enumerate_cycles_multistart


def per_config_match(cycle, det, n):
    """Return match counts per cycle config.

    For each c ∈ C and each position p: c contributes iff there exists an
    entry (p, a, b, d) → e with (a, e, d) = (c[p-1], c[p], c[p+1]) AND e ≠ b
    (move, not stay).

    Build a set of target triples per position from det entries that are moves.
    Then test each c at each p against that set.
    """
    tgt_by_p = defaultdict(set)  # p → set of (a, e, d)
    for key, e in det.items():
        (p, a, b, d) = key
        if e == b:  # skip stay entries
            continue
        tgt_by_p[p].add((a, e, d))
    matches = []
    for c in cycle:
        m = 0
        for p in range(n):
            tri = (c[(p - 1) % n], c[p], c[(p + 1) % n])
            if tri in tgt_by_p.get(p, ()):
                m += 1
        matches.append(m)
    return matches


SWEEP_PLANS = [
    (5, [(2,2,2,2,3), (2,2,2,3,3), (2,2,3,3,3)], 10, 20, 60),
    (6, [(2,2,2,3,3,3), (2,2,3,2,3,3), (2,2,3,3,3,3), (2,3,2,3,2,3)], 12, 22, 80),
    (7, [(2,2,2,3,3,3,3), (2,2,3,2,3,3,3), (2,2,3,3,2,3,3)], 14, 24, 90),
    (8, [(2,2,2,3,3,3,3,3), (2,2,3,2,3,3,3,3)], 16, 26, 120),
    (9, [(2,2,2,3,3,3,3,3,3)], 18, 28, 180),
]


def run():
    by_n = {}
    for (n, mss, L_min, L_max, max_cycles) in SWEEP_PLANS:
        by_n[n] = {
            "max_match": 0, "num_cycles": 0,
            "match_hist": Counter(),
            "example_high": None,  # (match, c, cycle, ms) for max
        }
        for ms in mss:
            cycles = enumerate_cycles_multistart(ms, n, L_min=L_min, L_max=L_max,
                                                  time_budget=60, max_cycles=max_cycles)
            for (cycle, movers, det) in cycles:
                matches = per_config_match(cycle, det, n)
                m_max = max(matches)
                by_n[n]["num_cycles"] += 1
                by_n[n]["match_hist"].update(matches)
                if m_max > by_n[n]["max_match"]:
                    by_n[n]["max_match"] = m_max
                    argmax = matches.index(m_max)
                    by_n[n]["example_high"] = {
                        "match": m_max, "c": list(cycle[argmax]),
                        "ms": list(ms), "L": len(movers),
                    }

    print("\n" + "=" * 70)
    print("PER-CONFIG β-MATCH SWEEP (1190 cycles)")
    print("=" * 70)
    print(f"  {'n':>3} {'#cycles':>8} {'max match':>10} {'match histogram':>40}")
    overall_max = 0
    for n in sorted(by_n):
        d = by_n[n]
        hist_str = " ".join(f"{k}:{d['match_hist'][k]}"
                            for k in sorted(d['match_hist']))
        print(f"  {n:>3} {d['num_cycles']:>8} {d['max_match']:>10}  {hist_str}")
        overall_max = max(overall_max, d["max_match"])
        if d["example_high"]:
            ex = d["example_high"]
            print(f"       high-match example: match={ex['match']}  "
                  f"c={ex['c']}  ms={ex['ms']}  L={ex['L']}")

    print(f"\n  Overall max per-config match across all cycles/n: {overall_max}")
    print()
    if overall_max <= 2:
        print("  VERDICT: tier-1 (Σβ ≤ 2L) feasibility — GO for paper proof attempt")
    elif overall_max <= 3:
        print("  VERDICT: tier-1 dead; tier-2 (Σβ ≤ 2.5L or 3L) may still work")
    else:
        print(f"  VERDICT: per-config hotspot hits {overall_max} — tier 3 (keep carve-out)")

    outdir = os.path.join(_HERE, "sk_phase0_out")
    os.makedirs(outdir, exist_ok=True)
    out = {str(n): {
        "num_cycles": d["num_cycles"], "max_match": d["max_match"],
        "match_hist": dict(d["match_hist"]),
        "example_high": d["example_high"],
    } for n, d in by_n.items()}
    out["overall_max"] = overall_max
    with open(os.path.join(outdir, "beta_perconfig.json"), "w") as f:
        json.dump(out, f, indent=2)
    print(f"\n  wrote sk_phase0_out/beta_perconfig.json")


if __name__ == "__main__":
    run()
