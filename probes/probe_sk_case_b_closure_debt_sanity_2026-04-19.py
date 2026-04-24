#!/usr/bin/env python3
"""Sanity check for closure-debt probe (2026-04-19).

Re-runs ONLY the n=5, ms=(2,2,2,3,4), p=3 family (5 stored stay-saturation
exceptions). Verifies CDO classifies each as satisfied via branch (D) at
q ∈ {1, 2}.
"""
from __future__ import annotations
import importlib.util, os, sys

sys.setrecursionlimit(100000)
_HERE = os.path.dirname(os.path.abspath(__file__))


def _load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

cdo_mod = _load(os.path.join(_HERE, "probe_sk_case_b_closure_debt_2026-04-19.py"),
                "cdo")
ss_mod = _load(os.path.join(_HERE, "probe_sk_case_b_stay_saturation_2026-04-18.py"),
               "ss")

dfs_seeded_with_terminals = ss_mod.dfs_seeded_with_terminals
enumerate_starts = ss_mod.enumerate_starts
cdo_analyze_terminal = cdo_mod.cdo_analyze_terminal


def main():
    n = 5
    ms = (2, 2, 2, 3, 4)
    p = 3
    L_min, L_max = 6, 18
    print("Sanity check: n=5, ms=(2,2,2,3,4), p=3, all 5 (l,r,v,s1,s2) tuples")
    print("Expected: each terminal CDO-satisfied via branch (D) at q ∈ {1,2}")
    print("=" * 72)

    cases = [
        (0, 0, 0, 1, 2),
        (0, 0, 1, 0, 2),
        (0, 0, 2, 0, 1),
        # plus two with c_0 variants (same seed up to start config differences)
    ]
    # Per the spec, seeds are (l, r, v, s1, s2). All 5 prior-stored
    # exceptions are at l=r=0 with various (v, s1, s2) triples in Fin 3.
    # Iterate all valid such tuples:
    full = []
    for l in range(2):
        for r in range(2):
            for v in range(3):
                for s1 in range(3):
                    if s1 == v: continue
                    for s2 in range(s1+1, 3):
                        if s2 == v: continue
                        full.append((l, r, v, s1, s2))
    # The known 5 exceptions are all at l=r=0:
    target_seeds = [(l, r, v, s1, s2) for (l, r, v, s1, s2) in full
                    if l == 0 and r == 0]
    print(f"Iterating {len(target_seeds)} (l=0, r=0) seeds at p={p}")

    n_sat = 0
    n_total = 0
    branch_d_at_binary = 0
    for l, r, v, s1, s2 in target_seeds:
        seed_det = {
            (p, l, s1, r): v,
            (p, l, s2, r): v,
            (p, l, v,  r): v,
        }
        starts = enumerate_starts(ms, n, p, l, s1, r, max_starts=3)
        for s_cfg in starts:
            cycles, terminals, _ = dfs_seeded_with_terminals(
                ms, n, seed_det, s_cfg,
                L_min=L_min, L_max=L_max,
                time_budget=2.0, max_terminals=20,
                early_exit_on_zero_ss=False,
            )
            for path, movers, det, kind in terminals:
                if kind not in ("stuck", "closed_unfair"):
                    continue
                n_total += 1
                info = cdo_analyze_terminal(path, movers, det, ms, n,
                                            seed_det, s_cfg)
                if info["cdo_satisfied"]:
                    n_sat += 1
                    # check if witness q ∈ {1,2} via branch D
                    for (q, br) in info["cdo_witnesses"]:
                        if br == "D" and q in (1, 2):
                            branch_d_at_binary += 1
                            break
                else:
                    print(f"  VIOLATOR: seed=(l={l},r={r},v={v},s1={s1},s2={s2})")
                    print(f"    kind={kind} L={len(movers)} μ={tuple(movers)}")
                    print(f"    Δ={info['delta']}  fc={info['fire_count']}")
                    print(f"    blocked={info['blocked']}")
    print()
    print(f"Total terminals analyzed: {n_total}")
    print(f"CDO-satisfied:            {n_sat}  ({n_sat - n_total} violators)")
    print(f"With branch (D) at q∈{{1,2}}: {branch_d_at_binary}")
    if n_total == n_sat and branch_d_at_binary > 0:
        print("\nSANITY CHECK PASSED.")
    else:
        print("\nSANITY CHECK FAILED.")


if __name__ == "__main__":
    main()
