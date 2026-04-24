#!/usr/bin/env python3
"""Phase 2.1 paper check — measure the (b) margin empirically.

SlabCounting (b) claims: Σ_{entries} (α + β) ≤ (n+1)·L, where
  α_k = |S_src(k) ∩ C|,
  β_k = |S_tgt(k) ∩ C|,
and the doc asserts Σ α = L exactly, Σ β ≤ n·L.

For each of our 5 dumps (n=5,6,7,8,9), compute α_k, β_k, and Σ(α+β)
directly. Compare to L, n·L, (n+1)·L, and to 2^(n-3)·L (the size needed
to force an unblocked entry).

GO (for Phase 2.1): observed margin is enormous (Σ(α+β) ≪ (n+1)·L).
If tight, flag for re-examination.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from itertools import product as iproduct
import importlib.util, json, os, sys, time

sys.setrecursionlimit(100000)
_HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location(
    "probe_c", os.path.join(_HERE, "probe_sk_hamming1_chain_closure_2026-04-17.py"))
probe_c = importlib.util.module_from_spec(spec); spec.loader.exec_module(probe_c)

enumerate_cycles_multistart = probe_c.enumerate_cycles_multistart


def value_ranges(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n):
            V[i].add(c[i])
    return [sorted(s) for s in V]


def vc_configs(V):
    return list(iproduct(*V))


def slab_counts(cycle, movers, det, n):
    """For each det move entry (key, value) with value != key.b, compute
       α = |S_src ∩ C|, β = |S_tgt ∩ C|, slab_size = |S_src| = |S_tgt|.

       S_src = {c ∈ VC : c[p-1]=a, c[p]=b, c[p+1]=d} where key=(p,a,b,d).
       S_tgt = {c ∈ VC : c[p-1]=a, c[p]=e, c[p+1]=d} where value=e.
    """
    V = value_ranges(cycle, n)
    # |S| = ∏_{i ∉ {p-1,p,p+1}} |V_i|
    V_sizes = [len(v) for v in V]
    cycle_set = set(cycle)
    entries = []
    for key, e in det.items():
        (p, a, b, d) = key
        if e == b:
            continue  # stay, not a move
        # α: cycle configs with triple (a,b,d) at p (wrap p-1, p+1)
        alpha = sum(1 for c in cycle if c[(p-1) % n] == a and c[p] == b and c[(p+1) % n] == d)
        beta  = sum(1 for c in cycle if c[(p-1) % n] == a and c[p] == e and c[(p+1) % n] == d)
        # slab size: product of |V_i| for i not in {p-1, p, p+1}
        excl = {(p-1) % n, p, (p+1) % n}
        slab = 1
        for i in range(n):
            if i not in excl:
                slab *= V_sizes[i]
        entries.append({
            "key": key, "value": e, "alpha": alpha, "beta": beta,
            "slab_size": slab, "blocked": (alpha + beta) >= slab,
        })
    return entries


def do_case(label, n, ms, L_min, L_max):
    prod = 1
    for m in ms: prod *= m
    print(f"\n=== {label}: n={n} ms={ms} product={prod} ===", flush=True)
    cycles = enumerate_cycles_multistart(ms, n, L_min=L_min, L_max=L_max,
                                          time_budget=30, max_cycles=3)
    if not cycles:
        print("  NO CYCLES FOUND"); return None
    cycle, movers, det = cycles[0]
    L = len(movers)
    print(f"  picked 1 cycle with L={L}")
    entries = slab_counts(cycle, movers, det, n)
    E = len(entries)
    sum_alpha = sum(e["alpha"] for e in entries)
    sum_beta  = sum(e["beta"]  for e in entries)
    sum_ab    = sum_alpha + sum_beta
    min_slab  = min(e["slab_size"] for e in entries)
    max_slab  = max(e["slab_size"] for e in entries)
    budget_claim = (n + 1) * L
    need       = (2 ** (n - 3))
    blocked_k  = sum(1 for e in entries if e["blocked"])
    print(f"  # move entries E={E}  (stay entries excluded)")
    print(f"  Σ α = {sum_alpha}  (doc claim: = L = {L})  "
          f"{'OK' if sum_alpha == L else 'MISMATCH'}")
    print(f"  Σ β = {sum_beta}  (doc claim: ≤ n·L = {n*L})  "
          f"ratio Σβ/(n·L) = {sum_beta/(n*L):.4f}")
    print(f"  Σ(α+β) = {sum_ab}  (bound: (n+1)·L = {budget_claim})  "
          f"ratio = {sum_ab/budget_claim:.4f}")
    print(f"  slab size: min={min_slab} max={max_slab}  (need > n+1 = {n+1}, "
          f"specifically ≥ 2^(n-3) = {need})")
    print(f"  blocked entries: {blocked_k}/{E}  "
          f"(theorem says: if n≥6 and slab ≥ 2^(n-3), not all blocked)")
    # Per-entry distribution
    ab_hist = Counter((e["alpha"], e["beta"]) for e in entries)
    print(f"  (α,β) histogram: {dict(ab_hist.most_common(8))}")
    return {
        "label": label, "n": n, "ms": list(ms), "L": L, "E": E,
        "sum_alpha": sum_alpha, "sum_beta": sum_beta, "sum_ab": sum_ab,
        "budget_claim_np1_L": budget_claim,
        "ratio_to_budget": sum_ab / budget_claim,
        "sum_alpha_equals_L": sum_alpha == L,
        "min_slab": min_slab, "max_slab": max_slab,
        "need_2_to_n_minus_3": need,
        "blocked_entries": blocked_k,
        "ab_histogram": {f"({a},{b})": c for (a, b), c in ab_hist.most_common(20)},
    }


CASES = [
    ("A_n5", 5, (2, 2, 2, 2, 3), 10, 14),
    ("E_n6_3bin", 6, (2, 2, 2, 3, 3, 3), 14, 18),
    ("B_n7_3bin", 7, (2, 2, 2, 3, 3, 3, 3), 16, 19),
    ("C_n8_3bin", 8, (2, 2, 2, 3, 3, 3, 3, 3), 18, 24),
    ("D_n9_3bin", 9, (2, 2, 2, 3, 3, 3, 3, 3, 3), 20, 26),
]

# Additional broader sweep: multiple cycles per (n, ms), multiple ms per n.
SWEEP_PLANS = [
    (5, [(2,2,2,2,3), (2,2,2,3,3), (2,2,3,3,3)], 10, 20, 60),
    (6, [(2,2,2,3,3,3), (2,2,3,2,3,3), (2,2,3,3,3,3), (2,3,2,3,2,3)], 12, 22, 80),
    (7, [(2,2,2,3,3,3,3), (2,2,3,2,3,3,3), (2,2,3,3,2,3,3)], 14, 24, 90),
    (8, [(2,2,2,3,3,3,3,3), (2,2,3,2,3,3,3,3)], 16, 26, 120),
    (9, [(2,2,2,3,3,3,3,3,3)], 18, 28, 180),
]


def sweep():
    """Broad sweep: many cycles per (n, ms), multiple ms per n."""
    by_n = {}
    for (n, mss, L_min, L_max, max_cycles) in SWEEP_PLANS:
        by_n.setdefault(n, {"records": [], "max_avg_ab": 0, "max_avg_beta": 0})
        for ms in mss:
            prod = 1
            for m in ms: prod *= m
            cycles = enumerate_cycles_multistart(ms, n, L_min=L_min, L_max=L_max,
                                                  time_budget=60, max_cycles=max_cycles)
            for (cycle, movers, det) in cycles:
                L = len(movers)
                entries = slab_counts(cycle, movers, det, n)
                sum_a = sum(e["alpha"] for e in entries)
                sum_b = sum(e["beta"]  for e in entries)
                sum_ab = sum_a + sum_b
                avg_ab = sum_ab / L
                avg_b = sum_b / L
                min_slab = min(e["slab_size"] for e in entries)
                by_n[n]["records"].append({
                    "ms": list(ms), "L": L, "Σα": sum_a, "Σβ": sum_b,
                    "avg_ab": avg_ab, "avg_β": avg_b, "min_slab": min_slab,
                    "Σα_eq_L": sum_a == L,
                })
                by_n[n]["max_avg_ab"] = max(by_n[n]["max_avg_ab"], avg_ab)
                by_n[n]["max_avg_beta"] = max(by_n[n]["max_avg_beta"], avg_b)
    print("\n" + "=" * 70)
    print("BROAD SWEEP — Σα+β avg vs L constancy")
    print("=" * 70)
    print(f"  {'n':>3} {'#cycles':>8} {'Σα=L?':>6} "
          f"{'max Σβ/L':>10} {'max Σ(α+β)/L':>14} {'min slab':>10}")
    all_alpha_ok = True
    for n in sorted(by_n):
        recs = by_n[n]["records"]
        all_ok = all(r["Σα_eq_L"] for r in recs)
        if not all_ok: all_alpha_ok = False
        max_b = by_n[n]["max_avg_beta"]
        max_ab = by_n[n]["max_avg_ab"]
        min_s = min(r["min_slab"] for r in recs) if recs else 0
        print(f"  {n:>3} {len(recs):>8} {str(all_ok):>6} "
              f"{max_b:>10.4f} {max_ab:>14.4f} {min_s:>10}")
    print(f"\n  Σα = L always? {all_alpha_ok}")
    max_avg_ab_overall = max(by_n[n]["max_avg_ab"] for n in by_n)
    print(f"  Max empirical Σ(α+β)/L across all sweep records: {max_avg_ab_overall:.4f}")
    print(f"  Needed for weaker (b) = c·L: c = ceil({max_avg_ab_overall:.4f}) = {int(max_avg_ab_overall) + 1}")
    return by_n


def main():
    out = []
    for (label, n, ms, L_min, L_max) in CASES:
        r = do_case(label, n, ms, L_min, L_max)
        if r is not None: out.append(r)

    print("\n" + "=" * 60)
    print("SLAB MARGIN REPORT (5-case snapshot)")
    print("=" * 60)
    print(f"  {'label':<12} {'n':>3} {'L':>3} {'E':>4} "
          f"{'Σα':>5} {'Σβ':>5} {'Σα+β':>6} {'(n+1)L':>7} {'ratio':>7} "
          f"{'Σα=L?':>6}")
    for r in out:
        print(f"  {r['label']:<12} {r['n']:>3} {r['L']:>3} {r['E']:>4} "
              f"{r['sum_alpha']:>5} {r['sum_beta']:>5} {r['sum_ab']:>6} "
              f"{r['budget_claim_np1_L']:>7} {r['ratio_to_budget']:>7.4f} "
              f"{str(r['sum_alpha_equals_L']):>6}")

    by_n = sweep()

    outdir = os.path.join(_HERE, "sk_phase0_out")
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "slab_margin.json"), "w") as f:
        json.dump({"snapshot": out, "sweep_by_n": {str(n): v for n, v in by_n.items()}},
                   f, indent=2)
    print(f"\n  wrote sk_phase0_out/slab_margin.json")


if __name__ == "__main__":
    main()
