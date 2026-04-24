#!/usr/bin/env python3
"""Check: at L = 2n+2 specifically, is |peel(N_1(C) ∩ VC-NG)| = 2^(n-1) uniformly?

Across n ∈ {5, 6, 7, 8}, multiple 3-binary sub-M_n multisets. L=2n+2 only.
"""
from __future__ import annotations
from collections import Counter
import importlib.util, os, sys, time

_HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location(
    "probe_c", os.path.join(_HERE, "probe_sk_hamming1_chain_closure_2026-04-17.py"))
probe_c = importlib.util.module_from_spec(spec); spec.loader.exec_module(probe_c)

enumerate_cycles_multistart = probe_c.enumerate_cycles_multistart
build_N1_and_peel = probe_c.build_N1_and_peel
m_n_sharp = probe_c.m_n_sharp


def run():
    plans = [
        (5, [(2,2,2,3,3), (2,2,3,2,3), (2,2,3,3,2)]),
        (6, [(2,2,2,3,3,3), (2,2,3,2,3,3), (2,2,2,2,3,3)]),
        (7, [(2,2,2,3,3,3,3), (2,2,3,2,3,3,3), (2,2,2,2,3,3,3)]),
        (8, [(2,2,2,3,3,3,3,3), (2,2,3,2,3,3,3,3), (2,2,2,2,3,3,3,3)]),
    ]
    rows = []
    for n, mss in plans:
        target_L = 2 * n + 2
        two_pow = 2 ** (n - 1)
        print(f"\nn={n} target L={target_L} 2^(n-1)={two_pow}", flush=True)
        for ms in mss:
            prod = 1
            for m in ms: prod *= m
            if prod >= m_n_sharp(n):
                continue
            cycles = enumerate_cycles_multistart(ms, n,
                L_min=target_L, L_max=target_L + 3, time_budget=30, max_cycles=40)
            for idx, (cycle, movers, det) in enumerate(cycles):
                L = len(movers)
                if L != target_L:
                    continue
                _, _, peel_set, _, _, _, _ = build_N1_and_peel(ms, n, cycle, det)
                rows.append((n, tuple(ms), L, len(peel_set), two_pow))
            ms_peel = [r[3] for r in rows if r[0] == n and r[1] == tuple(ms)]
            hit = sum(1 for s in ms_peel if s == two_pow)
            print(f"  ms={ms} prod={prod}  cycles_found={len(ms_peel)}  "
                  f"|peel|={sorted(set(ms_peel))[:8]}  "
                  f"== 2^(n-1): {hit}/{len(ms_peel)}")

    print("\n--- overall ---")
    by_n = {}
    for r in rows:
        by_n.setdefault(r[0], []).append(r)
    for n, rs in sorted(by_n.items()):
        two_pow = 2 ** (n - 1)
        match = sum(1 for r in rs if r[3] == two_pow)
        print(f"  n={n}  L={2*n+2}  {match}/{len(rs)} cycles have |peel|={two_pow}")


if __name__ == "__main__":
    run()
