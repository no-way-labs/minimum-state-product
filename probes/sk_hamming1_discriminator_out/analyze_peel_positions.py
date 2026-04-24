#!/usr/bin/env python3
"""Follow-up: for each good cycle in the prior run, enumerate ALL single-flip
representations of peel elements (not just the lex-first survivor). This tests
whether the n-2 position is special, or just an artifact of lex ordering."""
import sys, os, importlib.util, json
from collections import defaultdict, Counter

here = os.path.dirname(os.path.abspath(__file__))
probe_path = os.path.join(os.path.dirname(here),
                          'probe_sk_hamming1_empty_discriminator_2026-04-17.py')
spec = importlib.util.spec_from_file_location('probe', probe_path)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

plans = [
    (5, 10.0, 4, 13, [(2,2,2,3,3)]),
    (6, 15.0, 4, 15, [(2,2,2,3,3,3), (2,2,3,2,3,3)]),
    (7, 30.0, 3, 17, [(2,2,2,3,3,3,3), (2,2,3,2,3,3,3)]),
    (8, 45.0, 3, 19, [(2,2,2,3,3,3,3,3), (2,2,3,2,3,3,3,3)]),
    (9, 90.0, 2, 22, [(2,2,2,2,3,3,3,3,3)]),
]

full_q_counts = Counter()   # (n, q) across all peel configs and all their provenance
cycles_summary = []

for n, tb, mc, L_max, ms_list in plans:
    for ms in ms_list:
        cycles = m.enumerate_cycles_multistart(ms, n, L_min=2*n+2, L_max=L_max,
                                                time_budget=tb, max_cycles=mc)
        for cycle, movers, det in cycles:
            L = len(movers)
            N1, adj, peel_set, provenance, V, move_entries, cycle_set = m.build_N1_and_peel(
                ms, n, cycle, det)
            # For each peel config, ALL its (q, v, i) provenance
            this_q = Counter()
            for c in peel_set:
                for (q, v, i) in provenance[c]:
                    this_q[q] += 1
                    full_q_counts[(n, q)] += 1
            # For each peel config, take the UNIQUE set of q positions
            per_c_qs = {c: tuple(sorted({q for (q, v, i) in provenance[c]}))
                        for c in peel_set}
            # How many distinct q's appear among peel configs?
            all_qs = set()
            for c in peel_set:
                for (q, v, i) in provenance[c]:
                    all_qs.add(q)
            cycles_summary.append({
                'n': n, 'ms': list(ms), 'L': L,
                'peel_size': len(peel_set),
                'q_in_peel_provenance': sorted(all_qs),
                'q_distrib': dict(sorted(this_q.items())),
                # Sample: for fixed cycle idx i=0 and each position q, does flipping to
                # EACH v ∈ V[q] \ {c_0[q]} land in peel?
            })
            # Describe the cycle's ms and starting config
print('=== peel provenance distribution (q position) per cycle ===')
for s in cycles_summary:
    print(f"  n={s['n']} ms={s['ms']} L={s['L']} |peel|={s['peel_size']} "
          f"q_set={s['q_in_peel_provenance']}")
print()
print('=== aggregate (n, q) provenance counts ===')
# normalize by total counts per n
by_n = defaultdict(Counter)
for (n, q), c in full_q_counts.items():
    by_n[n][q] = c
for n in sorted(by_n):
    total = sum(by_n[n].values())
    dist = {q: f"{100*c/total:.1f}%" for q, c in sorted(by_n[n].items())}
    print(f"  n={n}  total prov={total}  per-q: {dist}")
