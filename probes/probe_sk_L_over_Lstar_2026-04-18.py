#!/usr/bin/env python3
"""Phase 2.1 budget probe — L / L* ratio (per-source entries vs distinct targets).

For each fair simple cycle:
    L  = # firing steps (= # distinct source triples by 2b)
    L* = # distinct target triples (p, (l, v, r)) image of firings under f

L/L* measures f-non-injectivity collapse on middle at fixed (l, r).
- L/L* = 1  → f injective on cycle-active middles; Path 2 budget survives.
- L/L* ≥ 2 → f collides; refactor needs combined source×target object.

Budget at n=5: slab = 4, need slab > 6·(L/L*), so L/L* < 2/3 → INFEASIBLE if L/L* ≥ 1.
    Already fails whenever L/L* ≥ 1, so n=5 is Option C regardless.
Budget at n=6: slab = 8, need slab > 7·(L/L*), i.e., L/L* < 8/7 ≈ 1.14 → need near-1.
Budget at n=7: slab = 16, L/L* < 16/8 = 2 → comfortable if near 1.

So the decisive threshold is n=6: max L/L* < 8/7.
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


def L_and_Lstar(cycle, det, n):
    """Return (L, L*, sharing_histogram).

    L = # move entries in det (= firings, = cycle length for fair cycles).
    L* = # distinct target triples (p, (l, v, r)) over move entries.
    Also returns histogram of (# sources sharing each target).
    """
    sources_by_target = defaultdict(list)  # (p, l, v, r) -> [sources s]
    L = 0
    for key, e in det.items():
        (p, l, s, r) = key
        if e == s:  # stay entry, skip
            continue
        L += 1
        sources_by_target[(p, l, e, r)].append(s)
    Lstar = len(sources_by_target)
    hist = Counter(len(ss) for ss in sources_by_target.values())
    return L, Lstar, hist


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
            "num_cycles": 0,
            "max_ratio": 0.0,
            "max_ratio_example": None,
            "max_sharing": 0,
            "sharing_hist_total": Counter(),
            "ratio_hist_bucket": Counter(),  # rounded to .05
            "ratios": [],
        }
        for ms in mss:
            cycles = enumerate_cycles_multistart(ms, n, L_min=L_min, L_max=L_max,
                                                  time_budget=60,
                                                  max_cycles=max_cycles)
            for (cycle, movers, det) in cycles:
                L, Lstar, hist = L_and_Lstar(cycle, det, n)
                ratio = L / Lstar if Lstar > 0 else 0.0
                d = by_n[n]
                d["num_cycles"] += 1
                d["ratios"].append(ratio)
                d["sharing_hist_total"].update(hist)
                bucket = round(ratio * 20) / 20
                d["ratio_hist_bucket"][bucket] += 1
                max_share = max(hist.keys()) if hist else 0
                if max_share > d["max_sharing"]:
                    d["max_sharing"] = max_share
                if ratio > d["max_ratio"]:
                    d["max_ratio"] = ratio
                    d["max_ratio_example"] = {
                        "L": L, "Lstar": Lstar, "ratio": ratio,
                        "ms": list(ms), "max_sharing": max_share,
                    }

    print("\n" + "=" * 70)
    print("L / L* RATIO SWEEP (per-source entries vs distinct targets)")
    print("=" * 70)
    print(f"  {'n':>3} {'#cycles':>8} {'max L/L*':>10} {'max sharing':>12}"
          f" {'mean L/L*':>10}")
    for n in sorted(by_n):
        d = by_n[n]
        mean = sum(d["ratios"]) / len(d["ratios"]) if d["ratios"] else 0.0
        print(f"  {n:>3} {d['num_cycles']:>8} {d['max_ratio']:>10.4f}"
              f" {d['max_sharing']:>12} {mean:>10.4f}")

    print()
    print("Budget check (slab = 2^(n-3), need slab > (n+1)·(L/L*)):")
    for n in sorted(by_n):
        d = by_n[n]
        slab = 2 ** (n - 3)
        max_ratio = d["max_ratio"]
        needed = (n + 1) * max_ratio
        ok = slab > needed
        print(f"  n={n}  slab={slab:>3}  (n+1)·(max L/L*)={needed:>7.3f}"
              f"   {'OK' if ok else 'FAIL'}")

    print()
    print("Sharing histograms (per-target source count, aggregated across cycles):")
    for n in sorted(by_n):
        d = by_n[n]
        hist_str = " ".join(f"{k}:{d['sharing_hist_total'][k]}"
                            for k in sorted(d['sharing_hist_total']))
        print(f"  n={n}: {hist_str}")

    outdir = os.path.join(_HERE, "sk_phase0_out")
    os.makedirs(outdir, exist_ok=True)
    out = {str(n): {
        "num_cycles": d["num_cycles"],
        "max_ratio": d["max_ratio"],
        "max_ratio_example": d["max_ratio_example"],
        "max_sharing": d["max_sharing"],
        "sharing_hist": dict(d["sharing_hist_total"]),
        "ratio_hist": {str(k): v for k, v in sorted(d["ratio_hist_bucket"].items())},
    } for n, d in by_n.items()}
    with open(os.path.join(outdir, "L_over_Lstar.json"), "w") as f:
        json.dump(out, f, indent=2)
    print(f"\n  wrote sk_phase0_out/L_over_Lstar.json")


if __name__ == "__main__":
    run()
