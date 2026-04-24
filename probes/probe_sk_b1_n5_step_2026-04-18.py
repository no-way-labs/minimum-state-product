#!/usr/bin/env python3
"""Check: at n=5, are all firing-sequence consecutive-step offsets (p_{j+1}-p_j) mod 5
in {1, 4} (i.e., ±1)?"""
import importlib.util, os
from collections import Counter
_HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location(
    'probe_a', os.path.join(_HERE, 'probe_sk_hamming1_empty_discriminator_2026-04-17.py'))
pa = importlib.util.module_from_spec(spec); spec.loader.exec_module(pa)

from math import prod
from itertools import product as iproduct

Mn = 96
N = 5
multisets = [t for t in iproduct(range(2,6), repeat=N)
             if prod(t) < Mn and min(t) >= 2]

global_offsets = Counter()
all_cycles = 0
for ms in multisets:
    cycles = pa.enumerate_cycles_multistart(
        ms, N, L_min=5, L_max=22, time_budget=4.0, max_cycles=150)
    for (cyc, movers, det) in cycles:
        L = len(movers)
        all_cycles += 1
        for j in range(L):
            d = (movers[(j+1) % L] - movers[j]) % N
            global_offsets[d] += 1
print(f"total cycles: {all_cycles}")
print(f"offset (p_{{j+1}} - p_j) mod 5 distribution: {dict(sorted(global_offsets.items()))}")
total_offsets = sum(global_offsets.values())
pm1 = global_offsets.get(1, 0) + global_offsets.get(N-1, 0)
zero = global_offsets.get(0, 0)
nonlocal_ = total_offsets - pm1 - zero
print(f"  fraction ±1 (sweep step):    {pm1}/{total_offsets} = {pm1/total_offsets:.4f}")
print(f"  fraction 0 (stutter):        {zero}/{total_offsets} = {zero/total_offsets:.4f}")
print(f"  fraction other (non-local):  {nonlocal_}/{total_offsets} = {nonlocal_/total_offsets:.4f}")

# Now confirm that for every j the triple p_{j-1}, p_j, p_{j+1} lives in
# a window of diameter ≤ 2 on Z/5 (i.e., 3 consecutive positions) — this is
# the structural explanation for |E_j| ≤ 3.
from collections import Counter
diam_counter = Counter()
total_triples = 0
for ms in multisets:
    cycles = pa.enumerate_cycles_multistart(
        ms, N, L_min=5, L_max=22, time_budget=4.0, max_cycles=150)
    for (cyc, movers, det) in cycles:
        L = len(movers)
        for j in range(L):
            a = movers[(j-1) % L]; b = movers[j]; c = movers[(j+1) % L]
            # min window covering {a,b,c} on Z/5 cyclic
            pts = {a, b, c}
            if len(pts) == 1:
                diam = 0
            else:
                # try every rotation
                best = N + 1
                for start in range(N):
                    offs = sorted(((x - start) % N) for x in pts)
                    w = offs[-1]  # window width
                    if w < best:
                        best = w
                diam = best
            diam_counter[diam] += 1
            total_triples += 1
print(f"\nTriple-window diameter (p_{{j-1}}, p_j, p_{{j+1}}) distribution: {dict(sorted(diam_counter.items()))}")
print(f"  max window size: {max(diam_counter.keys())}  (diameter ≤ 2 means within 3 consecutive positions)")
