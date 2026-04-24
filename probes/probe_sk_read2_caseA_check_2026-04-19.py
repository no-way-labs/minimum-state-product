#!/usr/bin/env python3
"""Case-A LB vs actual f check (2026-04-19, session 1 ansatz verification).

For each sub-threshold good cycle (L≥2n) enumerated on the adversarial
and stride-stage multisets, compute:

  A_refined := Σ_k Σ_{q ∉ {p_k-1, p_k, p_k+1}} μ_q
             = L · Σ_q μ_q − Σ_k (μ_{p_k-1} + μ_{p_k} + μ_{p_k+1})

This is the Case-A edge count (before C-collision correction).
Actual edges `f = E_size` may exceed `A_refined` (Case B contributes)
or fall short by the C-collision count.

Tripwire: if `actual_f < A_refined − 2*L` on any record, Case-A
derivation overcounts beyond the loose collision bound. Reformulate.

Also track `sinks_frac = sinks / T_size` to feed the session-2 `g`
upper bound analysis.
"""

import importlib.util
import json
import os
import sys
import time
from collections import defaultdict
from itertools import product as iproduct

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "r4_scaffold",
    os.path.join(HERE, "probe_sk_closed_form_extraction_2026-04-19.py"),
)
_scaffold = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_scaffold)
enumerate_all_cycles = _scaffold.enumerate_all_cycles
m_n_sharp = _scaffold.m_n_sharp
analyze_k1 = _scaffold.analyze_k1
value_sets = _scaffold.value_sets


def case_a_metrics(ms, n, cycle, movers, det):
    """Compute Case-A LB parameters on top of analyze_k1."""
    L = len(movers)
    V = value_sets(cycle, n)
    mu = [len(V[i]) - 1 for i in range(n)]
    Sigma_mu = sum(mu)

    A_refined = 0
    for k in range(L):
        p = movers[k]
        # coords ∉ {p-1, p, p+1} mod n
        excluded = {(p - 1) % n, p % n, (p + 1) % n}
        for q in range(n):
            if q in excluded:
                continue
            A_refined += mu[q]
    # Alternatively: L*Sigma_mu - sum over k of (mu[p-1]+mu[p]+mu[p+1])
    return {
        'mu': mu,
        'Sigma_mu': Sigma_mu,
        'A_refined': A_refined,
        'A_uniform_approx': L * (n - 3) * Sigma_mu // n if n > 0 else 0,
    }


# Reuse adversarial set + add a spot-check of stage-1 multisets
ADVERSARIAL = [
    (7, (2, 2, 2, 2, 2, 2, 3)),
    (7, (2, 2, 2, 2, 2, 3, 3)),
    (7, (2, 2, 2, 3, 2, 2, 3)),
    (7, (2, 2, 2, 2, 3, 3, 3)),
    (7, (2, 3, 2, 3, 2, 3, 2)),
    (8, (2, 2, 2, 2, 2, 2, 2, 3)),
    (8, (2, 2, 2, 2, 2, 2, 3, 3)),
    (8, (2, 2, 2, 3, 2, 2, 2, 3)),
    (8, (2, 2, 2, 2, 3, 3, 3, 3)),
    (8, (2, 2, 2, 3, 3, 3, 3, 3)),
    (8, (2, 2, 2, 2, 3, 3, 3, 4)),
    (8, (2, 2, 3, 2, 2, 3, 2, 4)),
    # Small spot-checks at n=5, 6
    (5, (2, 2, 3, 3, 3)),
    (5, (2, 3, 3, 3, 3)),
    (6, (2, 2, 2, 3, 3, 3)),
    (6, (2, 2, 3, 3, 3, 3)),
    (6, (2, 3, 3, 3, 3, 3)),
]


def main():
    print("=" * 78)
    print("Case-A LB vs actual f probe (2026-04-19)")
    print("=" * 78)

    rows = []
    for (n, ms) in ADVERSARIAL:
        t0 = time.time()
        cycles = enumerate_all_cycles(ms, n, L_max=24,
                                      time_budget=60.0, max_cycles=20)
        for cycle, movers, det in cycles:
            L = len(movers)
            if L < 2 * n:
                continue
            r = analyze_k1(ms, n, cycle, movers, det)
            if r is None:
                continue
            m = case_a_metrics(ms, n, cycle, movers, det)
            r.update(m)
            r['A_over_f'] = r['A_refined'] - r['E_size']  # positive = LB overshoots
            r['margin_over_1'] = r['margin'] - 1
            rows.append(r)
        dt = time.time() - t0

    print(f"  Collected {len(rows)} records in total", flush=True)

    # Diagnostics
    overshoots = [r for r in rows if r['A_refined'] > r['E_size']]
    big_overshoots = [r for r in rows if r['A_refined'] - r['E_size'] > 2 * r['L']]

    print(f"\n  A_refined > E_size: {len(overshoots)}/{len(rows)} records")
    print(f"  A_refined > E_size + 2L (loose tripwire): {len(big_overshoots)}/{len(rows)}")

    if big_overshoots:
        print(f"\n  *** BIG OVERSHOOTS (T-Ans-2 fire) ***")
        for r in big_overshoots[:5]:
            print(f"    n={r['n']} ms={r['ms']} L={r['L']} "
                  f"A_ref={r['A_refined']} E={r['E_size']} "
                  f"diff={r['A_refined'] - r['E_size']} 2L={2*r['L']}")
    elif overshoots:
        print(f"\n  Case-A overshoots actual f by up to "
              f"{max(r['A_refined'] - r['E_size'] for r in overshoots)} "
              f"(within 2L slack; acceptable for collision correction)")

    # Per-n summary
    by_n = defaultdict(list)
    for r in rows:
        by_n[r['n']].append(r)
    print("\n  Per-n summary:")
    print(f"    n | recs | Sigma_mu range | L range | A_refined range | "
          f"E_size range | margin range | sinks/T mean")
    for n, rs in sorted(by_n.items()):
        smu = [r['Sigma_mu'] for r in rs]
        Ls = [r['L'] for r in rs]
        As = [r['A_refined'] for r in rs]
        Es = [r['E_size'] for r in rs]
        margins = [r['margin'] for r in rs]
        sink_fracs = [r['sinks'] / r['T_size'] if r['T_size'] > 0 else 0
                      for r in rs]
        print(f"    {n} | {len(rs):4d} | {min(smu)}..{max(smu):5d}    | "
              f"{min(Ls)}..{max(Ls):3d}  | {min(As)}..{max(As):5d}   | "
              f"{min(Es)}..{max(Es):5d}  | {min(margins)}..{max(margins):3d}  "
              f"| {sum(sink_fracs)/len(sink_fracs):.2%}")

    # Sink-fraction distribution — session 2 relevance
    all_sink_fracs = [r['sinks'] / r['T_size'] for r in rows if r['T_size'] > 0]
    if all_sink_fracs:
        sorted_sf = sorted(all_sink_fracs)
        print(f"\n  Sink fraction percentiles:")
        for p in [0, 10, 25, 50, 75, 90, 100]:
            idx = min(len(sorted_sf) - 1, int(p / 100 * len(sorted_sf)))
            print(f"    p{p:3d}: {sorted_sf[idx]:.3f}")

    out_dir = os.path.normpath(
        os.path.join(HERE, '..', 'lean', 'docs', 'sk', 'sk_phase0_out')
    )
    out_path = os.path.join(
        out_dir, 'r4_read2_caseA_check_2026-04-19.json'
    )
    with open(out_path, 'w') as f:
        json.dump(rows, f)
    print(f"\n  Wrote {out_path}")

    sys.exit(1 if big_overshoots else 0)


if __name__ == "__main__":
    main()
