#!/usr/bin/env python3
"""Spot-check: find the j where min_excl = 3 to understand the structure."""
import importlib.util, os
_HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location(
    'probe_a', os.path.join(_HERE, 'probe_sk_hamming1_empty_discriminator_2026-04-17.py'))
pa = importlib.util.module_from_spec(spec); spec.loader.exec_module(pa)

# Look at two different ms for variety
for ms in [(2,2,2,2,2), (2,2,2,3,3), (2,2,2,2,5)]:
    print(f"\n=== ms={ms} ===")
    cycles = pa.enumerate_cycles_multistart(
        ms, 5, L_min=5, L_max=22, time_budget=6.0, max_cycles=20)
    for ci, (cyc, movers, det) in enumerate(cycles[:5]):
        L = len(movers)
        sizes = []
        for j in range(L):
            p_prev = movers[(j-1)%L]; p_j = movers[j%L]; p_next = movers[(j+1)%L]
            E = {p_prev, (p_j-1)%5, p_j, (p_j+1)%5, p_next}
            sizes.append(len(E))
        # find first j with size==3
        js = [j for j,s in enumerate(sizes) if s == 3]
        print(f"  L={L} sizes={sizes} #j_with_3={len(js)}")
        if js:
            j = js[0]
            p_prev = movers[(j-1)%L]; p_j = movers[j%L]; p_next = movers[(j+1)%L]
            print(f"    at j={j}: p_prev={p_prev} p_j={p_j} p_next={p_next}  "
                  f"movers[j-2..j+2]={movers[(j-2)%L], movers[(j-1)%L], p_j, movers[(j+1)%L], movers[(j+2)%L]}")
