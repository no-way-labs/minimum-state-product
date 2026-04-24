#!/usr/bin/env python3
"""Session 1 de-risk probe — per sk_audit_optiona.md §1.

Outcome A confirmed (audit memo 2026-04-18). Now de-risk the Hamming-1 peel
closure before investing Lean sessions on Lemma A/B.

P1. Extend peel(N_1(C) ∩ VC-NG) nonemptiness to n ∈ {11, 12}.
    - Prior verification: n=5..8, 100% nonempty (hamming1 discovery doc).
    - Success = every fair cycle tested has nonempty peel.
    - Failure at any C = catalogue; rethink scope.
P2. Boundary stress — multisets with product close to M_n at n ∈ {8, 9}.
    - Reason: 5,548-multiset survey undersampled the boundary.
    - Success = peel nonempty at all near-boundary fair cycles.

Reuses cycle enum + peel from probe_sk_hamming1_empty_discriminator_2026-04-17.
Budget: time-bounded per (ms), few cycles each. n=11/12 is exploratory —
even one record per ms is informative if peel is nonempty.
"""
from itertools import product as iproduct
from collections import defaultdict
import importlib.util, os, sys, time, json
sys.setrecursionlimit(200000)

_HERE = os.path.dirname(os.path.abspath(__file__))
_A = os.path.join(_HERE, "probe_sk_hamming1_empty_discriminator_2026-04-17.py")
spa = importlib.util.spec_from_file_location("probe_a", _A)
pa = importlib.util.module_from_spec(spa); spa.loader.exec_module(pa)


def m_n_sharp(n):
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def enumerate_all_ms(n, max_product, min_product=0):
    """All nondecreasing tuples of length n with m_i ≥ 2 and product in
    [min_product, max_product)."""
    out = []

    def rec(i, prefix, prod, lo):
        if i == n:
            if min_product <= prod < max_product:
                out.append(tuple(prefix))
            return
        for m in range(lo, max_product + 1):
            new_prod = prod * m
            min_rem = 2 ** (n - i - 1)
            if new_prod * min_rem >= max_product:
                break
            prefix.append(m)
            rec(i + 1, prefix, new_prod, m)
            prefix.pop()

    rec(0, [], 1, 2)
    return out


def analyse_cycle(ms, n, cycle, det):
    N1, adj, peel_set, provenance, V, move_entries, cycle_set = pa.build_N1_and_peel(
        ms, n, cycle, det)
    return {
        'n': n, 'ms': list(ms), 'L': len(cycle),
        'prod': 1 if not ms else __import__('math').prod(ms),
        'N1': len(N1), 'peel': len(peel_set),
        'nonempty': len(peel_set) > 0,
    }


def run_p1(log):
    print("\n" + "=" * 72)
    print("P1 — extend Hamming-1 peel nonemptiness to n = 11, 12")
    print("=" * 72)
    # At n=11 M_11=78732, at n=12 M_12=236196. Pick a small set of
    # interesting multisets; emphasise ternary-heavy (where Clouds bites).
    plan = [
        # (n, [ms...], L_min, L_max, tb_per_ms, max_cycles)
        (11, [
            (2,2,2,3,3,3,3,3,3,3,3),    # prod=17496
            (2,2,3,3,3,3,3,3,3,3,3),    # prod=26244
            (2,3,3,3,3,3,3,3,3,3,3),    # prod=39366
        ], 24, 26, 40.0, 2),
        (12, [
            (2,2,2,3,3,3,3,3,3,3,3,3),  # prod=52488
            (2,2,3,3,3,3,3,3,3,3,3,3),  # prod=78732
            (2,3,3,3,3,3,3,3,3,3,3,3),  # prod=118098
        ], 26, 28, 60.0, 2),
    ]
    records = []
    for n, ms_list, L_min, L_max, tb, max_c in plan:
        Mn = m_n_sharp(n)
        print(f"\n--- n={n}  M_n={Mn} ---", flush=True)
        for ms in ms_list:
            import math
            prod = math.prod(ms)
            if prod >= Mn:
                print(f"  skip ms={ms} prod={prod} ≥ M_n", flush=True)
                continue
            t0 = time.time()
            cycles = pa.enumerate_cycles_multistart(
                ms, n, L_min=L_min, L_max=L_max,
                time_budget=tb, max_cycles=max_c)
            dt = time.time() - t0
            print(f"  ms={ms} prod={prod}  cycles={len(cycles)}  {dt:.1f}s",
                  flush=True)
            for cycle, movers, det in cycles:
                r = analyse_cycle(ms, n, cycle, det)
                records.append(r)
                flag = "NONEMPTY" if r['nonempty'] else "*** EMPTY ***"
                print(f"    L={r['L']}  N1={r['N1']}  peel={r['peel']}  {flag}",
                      flush=True)
    # summary
    print(f"\n  P1 summary: records={len(records)} "
          f"nonempty={sum(1 for r in records if r['nonempty'])}/{len(records)}")
    log['p1'] = records


def run_p2(log):
    print("\n" + "=" * 72)
    print("P2 — boundary stress at n=8 and n=9")
    print("=" * 72)
    # The plan specifies strict ranges; empty ranges still informative.
    plan = [
        # (n, lo, hi, L_min, L_max, tb, max_c)
        (8, 2500, 2591, 17, 20, 15.0, 3),
        (9, 8500, 8747, 19, 22, 20.0, 3),
    ]
    records = []
    for n, lo, hi, L_min, L_max, tb, max_c in plan:
        ms_list = enumerate_all_ms(n, hi + 1, min_product=lo)
        print(f"\n--- n={n}  product in [{lo}, {hi}]  {len(ms_list)} multisets ---",
              flush=True)
        # If empty, broaden to the top 8 sub-M_n products.
        if not ms_list:
            Mn = m_n_sharp(n)
            all_sub = enumerate_all_ms(n, Mn, min_product=0)
            all_sub.sort(key=lambda t: -__import__('math').prod(t))
            ms_list = all_sub[:8]
            print(f"  range empty — falling back to top {len(ms_list)} sub-M_n ms",
                  flush=True)
        for ms in ms_list:
            import math
            prod = math.prod(ms)
            t0 = time.time()
            cycles = pa.enumerate_cycles_multistart(
                ms, n, L_min=L_min, L_max=L_max,
                time_budget=tb, max_cycles=max_c)
            dt = time.time() - t0
            print(f"  ms={ms} prod={prod}  cycles={len(cycles)}  {dt:.1f}s",
                  flush=True)
            for cycle, movers, det in cycles:
                r = analyse_cycle(ms, n, cycle, det)
                records.append(r)
                flag = "NONEMPTY" if r['nonempty'] else "*** EMPTY ***"
                print(f"    L={r['L']}  N1={r['N1']}  peel={r['peel']}  {flag}",
                      flush=True)
    print(f"\n  P2 summary: records={len(records)} "
          f"nonempty={sum(1 for r in records if r['nonempty'])}/{len(records)}")
    log['p2'] = records


def main():
    print("=" * 72)
    print("Session 1 de-risk probe — 2026-04-18")
    print("=" * 72)
    log = {}
    t0 = time.time()
    run_p1(log)
    run_p2(log)
    dt = time.time() - t0

    print("\n" + "=" * 72)
    print(f"TOTAL: {dt:.0f}s")
    print("=" * 72)
    # Final verdict
    all_records = log.get('p1', []) + log.get('p2', [])
    empties = [r for r in all_records if not r['nonempty']]
    print(f"records total: {len(all_records)}")
    print(f"nonempty:      {len(all_records) - len(empties)}")
    print(f"empty:         {len(empties)}")
    if empties:
        print("\n*** EMPTY CASES (counterexamples) ***")
        for r in empties:
            print(f"  n={r['n']}  ms={r['ms']}  L={r['L']}  prod={r['prod']}")
    else:
        print("\nALL PEEL NONEMPTY — de-risk green light for Outcome A path.")

    # JSON dump
    outdir = os.path.join(_HERE, "sk_session1_out")
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "records.json"), "w") as f:
        json.dump(log, f, indent=2, default=str)


if __name__ == "__main__":
    main()
