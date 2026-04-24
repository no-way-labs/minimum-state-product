#!/usr/bin/env python3
"""Ternary-dense peel probe at n=11 — 2026-04-18.

Session 1 (2026-04-18) de-risk at n ∈ {11, 12} TLE'd on all mixed-shape
boundary multisets. Only extreme-singleton shapes (one big entry, rest
binary) produced cycles. This is a probe-scaling limit, not a refutation.

This probe closes the coverage gap:
  - Narrow L window: L_min = L_max = 2n = 22 (minimum fair cycle; most
    rigid, fewest paths — enumerator does not explore longer L bands).
  - Longer per-multiset budget: 240s each (vs Session 1's 40-60s).
  - Targeted ternary-dense ms at n=11 (sub-M_11 = 78732 = 4·3^9).

Goal: produce ≥ 1 cycle at ≥ 2 of the targeted multisets, verify
peel(N_1(C) ∩ VC-NG) nonempty. Any single empty peel = counterexample.

Reuses cycle enum + peel from probe_sk_hamming1_empty_discriminator_2026-04-17.
"""
import importlib.util, os, sys, time, json, math
sys.setrecursionlimit(300000)

_HERE = os.path.dirname(os.path.abspath(__file__))
_A = os.path.join(_HERE, "probe_sk_hamming1_empty_discriminator_2026-04-17.py")
spa = importlib.util.spec_from_file_location("probe_a", _A)
pa = importlib.util.module_from_spec(spa)
spa.loader.exec_module(pa)


def m_n_sharp(n):
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def analyse_cycle(ms, n, cycle, det):
    N1, adj, peel_set, provenance, V, move_entries, cycle_set = \
        pa.build_N1_and_peel(ms, n, cycle, det)
    return {
        'n': n, 'ms': list(ms), 'L': len(cycle),
        'prod': math.prod(ms),
        'N1': len(N1), 'peel': len(peel_set),
        'nonempty': len(peel_set) > 0,
    }


def run():
    n = 11
    Mn = m_n_sharp(n)  # 78732

    # Ternary-dense sub-M_n multisets at n=11.
    # Closest-to-boundary first (hardest structurally).
    targets = [
        # (ms, label)
        ((2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3), "3bin_8ter"),     # prod 52488
        ((2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3), "4bin_7ter"),     # prod 34992
        ((2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3), "5bin_6ter"),     # prod 23328
    ]

    # Tight L window = 2n = 22.
    L_min, L_max = 22, 22
    tb_per_ms = 240.0
    max_cycles = 3

    print("=" * 72)
    print(f"Ternary-dense peel probe at n={n}  M_n={Mn}")
    print(f"L=[{L_min},{L_max}]  tb={tb_per_ms}s/ms  max_cycles={max_cycles}")
    print("=" * 72, flush=True)

    results = []
    t0 = time.time()

    for ms, label in targets:
        prod = math.prod(ms)
        print(f"\n--- {label}  ms={ms}  prod={prod}  (sub-M_n by {Mn - prod}) ---",
              flush=True)
        t_ms = time.time()
        cycles = pa.enumerate_cycles_multistart(
            ms, n, L_min=L_min, L_max=L_max,
            time_budget=tb_per_ms, max_cycles=max_cycles)
        dt = time.time() - t_ms
        print(f"  cycles found: {len(cycles)}  walltime: {dt:.1f}s",
              flush=True)

        for cycle, movers, det in cycles:
            r = analyse_cycle(ms, n, cycle, det)
            r['label'] = label
            results.append(r)
            flag = "NONEMPTY" if r['nonempty'] else "*** EMPTY ***"
            print(f"    L={r['L']}  N1={r['N1']}  peel={r['peel']}  {flag}",
                  flush=True)

    dt_total = time.time() - t0
    print("\n" + "=" * 72)
    print(f"TOTAL walltime: {dt_total:.0f}s")
    print(f"records: {len(results)}")

    empties = [r for r in results if not r['nonempty']]
    non = [r for r in results if r['nonempty']]
    print(f"nonempty: {len(non)}")
    print(f"empty:    {len(empties)}")

    by_label = {}
    for r in results:
        by_label.setdefault(r['label'], []).append(r)
    for label, rs in by_label.items():
        ne = sum(1 for r in rs if r['nonempty'])
        print(f"  {label}: {ne}/{len(rs)} nonempty")

    if empties:
        print("\n*** EMPTY CASES (counterexamples) ***")
        for r in empties:
            print(f"  ms={r['ms']}  L={r['L']}  N1={r['N1']}")
    elif non:
        print("\nAll records nonempty. Coverage extended to n=11 ternary-dense.")
    else:
        print("\nNo cycles found on any target. Enumerator gap persists.")

    # Dump records
    outdir = os.path.join(_HERE, "sk_ternary_dense_n11_out")
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "records.json"), "w") as f:
        json.dump(results, f, indent=2, default=str)


if __name__ == "__main__":
    run()
