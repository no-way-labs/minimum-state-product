#!/usr/bin/env python3
"""Probe B1 — n=5 iteration rescue for Hamming-1-peel construction.

Construction: pick step j and position q ∉ E_j := {p_{j-1}, p_j-1, p_j, p_j+1, p_{j+1}}
(indices mod n). At n≥6, |E_j| ≤ 5 < n so some q exists.
At n=5, |E_j| can equal 5 (all of Z/5) for some j — construction fails at that j.

Question: does iterating j close the construction? I.e., for every good cycle,
does SOME j have |E_j| ≤ 4?

Enumerate all sub-sharp n=5 valid multisets (product < 96), enumerate good cycles,
compute firing sequence (p_0, ..., p_{L-1}) = `movers`, and report
min_cycle max_j (5 - |E_j|) — positive iff iteration rescues the cycle.
"""
from __future__ import annotations
import importlib.util, json, os, sys
from collections import Counter
from itertools import product as iproduct
from math import prod

sys.setrecursionlimit(100000)

_HERE = os.path.dirname(os.path.abspath(__file__))
_A_PATH = os.path.join(_HERE, "probe_sk_hamming1_empty_discriminator_2026-04-17.py")
_spec = importlib.util.spec_from_file_location("probe_a", _A_PATH)
probe_a = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(probe_a)

enumerate_cycles_multistart = probe_a.enumerate_cycles_multistart
m_n_sharp = probe_a.m_n_sharp


N = 5
M5 = m_n_sharp(N)  # 32


def all_sub_sharp_multisets(n, max_state=6):
    """Enumerate all ms = (m_0,...,m_{n-1}) with each m_i in [2..max_state],
    product(ms) < M_n. We allow per-position modulus variation (canonical LB form).
    To be conservative we enumerate all tuples with min ≥ 2 (fairness) and
    product(ms) < M_n. We deduplicate by sorted tuple (multiset) but also report
    as-is since cycle enumeration is position-sensitive.
    """
    Mn = m_n_sharp(n)
    out = []
    for t in iproduct(range(2, max_state + 1), repeat=n):
        if prod(t) >= Mn:
            continue
        if min(t) < 2:
            continue
        out.append(t)
    return out


def excl_set_size(movers, j, n):
    """Return |E_j| where E_j = {p_{j-1}, p_j-1, p_j, p_j+1, p_{j+1}} mod n."""
    L = len(movers)
    p_prev = movers[(j - 1) % L]
    p_j = movers[j % L]
    p_next = movers[(j + 1) % L]
    E = {p_prev, (p_j - 1) % n, p_j, (p_j + 1) % n, p_next}
    return len(E)


def analyse_cycle(movers, n):
    """For firing sequence `movers` length L, compute for each j:
      excl_j = |E_j| (up to 5)
    Return (min_excl, max_excl, all_sizes, any_excl_le_4).
    """
    L = len(movers)
    sizes = [excl_set_size(movers, j, n) for j in range(L)]
    return {
        'L': L,
        'movers': list(movers),
        'sizes': sizes,
        'min_excl': min(sizes),
        'max_excl': max(sizes),
        'any_le_4': any(s <= 4 for s in sizes),
        'count_le_4': sum(1 for s in sizes if s <= 4),
    }


def run():
    n = N
    multisets_all = all_sub_sharp_multisets(n, max_state=6)
    # Also enumerate the canonical sorted multisets to ensure coverage
    canonical_mss = set(tuple(sorted(t)) for t in multisets_all)
    print(f"n={n}  M_n={M5}  #position-tuples={len(multisets_all)}  "
          f"#canonical_multisets={len(canonical_mss)}", flush=True)

    # L range: fair cycles at n=5 must have L ≥ n = 5 (each position fires
    # at least once). Upper bound from known enumerations: L ≤ 20 is more
    # than sufficient; we cap at 22 to be safe.
    L_min = 5
    L_max = 22
    time_budget_per = 8.0
    max_cycles_per = 200

    total_ms_with_cycles = 0
    total_cycles = 0
    records = []  # per-cycle records
    cycles_all_fail = []  # cycles with all j having |E_j|=5
    cycles_min_excl_eq_5 = []  # should be empty if iteration works
    by_ms_counter = Counter()

    for ms in multisets_all:
        cycles = enumerate_cycles_multistart(
            ms, n, L_min=L_min, L_max=L_max,
            time_budget=time_budget_per, max_cycles=max_cycles_per)
        if not cycles:
            continue
        total_ms_with_cycles += 1
        by_ms_counter[tuple(sorted(ms))] += len(cycles)
        for (cycle, movers, det) in cycles:
            total_cycles += 1
            rec = analyse_cycle(movers, n)
            rec['ms'] = list(ms)
            records.append(rec)
            if not rec['any_le_4']:
                cycles_all_fail.append(rec)
            if rec['min_excl'] == 5:
                # min over j = 5 means every j has |E_j| = 5 (all distinct)
                cycles_min_excl_eq_5.append(rec)

    print(f"\n  ms with at least one cycle: {total_ms_with_cycles}")
    print(f"  total cycles enumerated: {total_cycles}")
    # verdict
    n_rescue = sum(1 for r in records if r['any_le_4'])
    n_fail = len(records) - n_rescue
    print(f"\n  cycles where SOME j has |E_j| ≤ 4 (iteration rescues): "
          f"{n_rescue}/{total_cycles}")
    print(f"  cycles where ALL j have |E_j| = 5 (iteration FAILS): {n_fail}")

    if records:
        dist_count_le_4 = Counter(r['count_le_4'] for r in records)
        dist_min_excl = Counter(r['min_excl'] for r in records)
        print(f"\n  count(|E_j|≤4 over j) distribution: {dict(sorted(dist_count_le_4.items()))}")
        print(f"  min |E_j| over j distribution:       {dict(sorted(dist_min_excl.items()))}")

    # Per-ms summary (canonical)
    print("\n  per canonical multiset:")
    by_canon = {}
    for r in records:
        key = tuple(sorted(r['ms']))
        by_canon.setdefault(key, []).append(r)
    for k in sorted(by_canon):
        rs = by_canon[k]
        n_rescue_k = sum(1 for r in rs if r['any_le_4'])
        print(f"    ms={k}  cycles={len(rs)}  rescued={n_rescue_k}/{len(rs)}  "
              f"min_count_le_4={min(r['count_le_4'] for r in rs)}  "
              f"max_count_le_4={max(r['count_le_4'] for r in rs)}")

    # Report first few failure witnesses (if any)
    if cycles_all_fail:
        print("\n  !!! FAILURE WITNESSES (first 5):")
        for r in cycles_all_fail[:5]:
            print(f"    ms={r['ms']}  L={r['L']}  movers={r['movers']}  sizes={r['sizes']}")

    # Verdict
    print("\n" + "=" * 70)
    if not records:
        print("  INCONCLUSIVE: no cycles enumerated.")
    elif not cycles_all_fail:
        print("  GREEN: every n=5 good cycle has some j with |E_j| ≤ 4.")
        print("  => Iteration over j closes the Hamming-1-peel construction at n=5.")
    else:
        frac = len(cycles_all_fail) / total_cycles
        if frac < 0.05:
            print(f"  YELLOW: {len(cycles_all_fail)}/{total_cycles} cycles have all j fail.")
            print("  => Partial iteration helps but a carve-out is still needed.")
        else:
            print(f"  RED: {len(cycles_all_fail)}/{total_cycles} cycles have all j fail.")
            print("  => Iteration does not rescue; carve-out is inescapable.")
    print("=" * 70)

    # Persist JSON
    outdir = os.path.join(_HERE, "sk_phase0_out")
    os.makedirs(outdir, exist_ok=True)
    summary = {
        "n": n,
        "M_n": M5,
        "num_position_tuples_checked": len(multisets_all),
        "num_canonical_multisets_checked": len(canonical_mss),
        "num_ms_with_cycles": total_ms_with_cycles,
        "total_cycles": total_cycles,
        "cycles_rescued_by_iteration": n_rescue,
        "cycles_all_j_fail": n_fail,
        "count_le_4_distribution": {str(k): v for k, v in sorted(dist_count_le_4.items())}
            if records else {},
        "min_excl_distribution": {str(k): v for k, v in sorted(dist_min_excl.items())}
            if records else {},
        "failure_witnesses_first_5": [
            {"ms": r["ms"], "L": r["L"], "movers": r["movers"], "sizes": r["sizes"]}
            for r in cycles_all_fail[:5]
        ],
        "verdict": ("GREEN" if records and not cycles_all_fail
                    else ("INCONCLUSIVE" if not records
                          else ("YELLOW" if len(cycles_all_fail) / total_cycles < 0.05
                                else "RED"))),
    }
    with open(os.path.join(outdir, "b1_n5_iteration.json"), "w") as f:
        json.dump(summary, f, indent=2)
    print(f"\n  wrote sk_phase0_out/b1_n5_iteration.json")


if __name__ == "__main__":
    run()
