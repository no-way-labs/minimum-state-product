#!/usr/bin/env python3
"""ε sub-session: separation-lemma empirical discriminator (2026-04-19).

Shape (3) claim: for any fair simple sub-threshold good cycle `C`, every
non-adjacent pair of cycle configs has Hamming distance ≥ 2. If this
holds uniformly across 340 records, separation lemma is live and the
analytical proof (simplicity + unique-priv + fairness → min non-adj
Ham ≥ 2) is the ε-bound path.

Shape (2) sanity check: count of Ham-1 pairs in C is `≤ L` iff no
non-adjacent Ham-1 pair exists — SAME condition as shape (3). So one
probe answers both.

Also counts `|collision_pairs|` per record = (step k, q ∉ N[p_k]) with
`c_k^{q,v} ∈ C \ {c_k}` — the quantity ε directly bounds. If
separation holds, collision_pairs count equals 0 because a Case-A
perturbation outside the firing neighborhood can only land on c_k
itself (Hamming 0) — and perturbations with v ≠ c_k[q] exclude that.
Wait, that's subtle: collision means c̃ = c* for some c* ≠ c_k, which
requires Ham(c_k, c*) ≤ 1. If c_k and c* are non-adjacent (more than
1 step apart on C) and separation holds, Ham ≥ 2, contradiction. So
any collision c_k ↔ c* is with an ADJACENT c_{k±1} — but adjacent c*
differ from c_k only at position p_k or p_{k-1}, which are IN the
firing neighborhood of p_k. Case A excludes q in that neighborhood.
Therefore separation ≥ 2 on non-adjacent pairs ⇒ collision_pairs = 0
⇒ ε = 0.

Hence: if separation holds, ε IS zero, not merely ≤ 0.03. The
empirical 0.03 ε is whatever else is being absorbed into the fit
(slight under-counting due to off-tube endpoints).

Run time: < 10s on existing records. Re-enumerates cycles.
"""

import importlib.util
import json
import os
import sys
import time
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "r4_scaffold",
    os.path.join(HERE, "probe_sk_closed_form_extraction_2026-04-19.py"),
)
_scaffold = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_scaffold)
enumerate_all_cycles = _scaffold.enumerate_all_cycles


def hamming(a, b):
    return sum(1 for i in range(len(a)) if a[i] != b[i])


def analyze_separation(ms, n, cycle, movers):
    L = len(movers)
    # Pairwise Ham distance for all non-identity pairs
    min_non_adj = float('inf')
    ham1_count = 0
    # Cycle-adjacent pairs: (i, i+1) for i in 0..L-1 (cyclically)
    adj_pairs = set()
    for i in range(L):
        adj_pairs.add((min(i, (i + 1) % L), max(i, (i + 1) % L)))

    ham1_non_adj = []  # non-adjacent pairs at Ham 1
    min_non_adj_pair = None
    for i in range(L):
        for j in range(i + 1, L):
            h = hamming(cycle[i], cycle[j])
            if h == 1:
                ham1_count += 1
                is_adj = (i, j) in adj_pairs
                if not is_adj:
                    ham1_non_adj.append((i, j))
            if (i, j) not in adj_pairs:
                if h < min_non_adj:
                    min_non_adj = h
                    min_non_adj_pair = (i, j, h)
    if min_non_adj == float('inf'):
        min_non_adj = None
    return {
        'L': L,
        'ham1_count': ham1_count,
        'ham1_non_adj_count': len(ham1_non_adj),
        'min_non_adj_ham': min_non_adj,
        'ham1_non_adj_pairs': ham1_non_adj[:5],  # sample
        'min_non_adj_pair': min_non_adj_pair,
    }


TARGETS = [
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
    (5, (2, 2, 3, 3, 3)),
    (5, (2, 3, 3, 3, 3)),
    (6, (2, 2, 2, 3, 3, 3)),
    (6, (2, 2, 3, 3, 3, 3)),
    (6, (2, 3, 3, 3, 3, 3)),
]


def main():
    print("=" * 78)
    print("ε sub-session: separation-lemma empirical discriminator (2026-04-19)")
    print("=" * 78)

    rows = []
    t0 = time.time()
    for (n, ms) in TARGETS:
        cycles = enumerate_all_cycles(ms, n, L_max=24,
                                      time_budget=60.0, max_cycles=20)
        for cycle, movers, det in cycles:
            L = len(movers)
            if L < 2 * n:
                continue
            r = analyze_separation(ms, n, cycle, movers)
            r['n'] = n
            r['ms'] = list(ms)
            r['Ham1_vs_L'] = (r['ham1_count'], L)
            rows.append(r)
    print(f"  Collected {len(rows)} cycles in {time.time()-t0:.1f}s\n")

    # Separation check
    print("  Shape (3) — min non-adjacent Hamming distance:")
    by_n = defaultdict(list)
    for r in rows:
        by_n[r['n']].append(r)
    for n in sorted(by_n):
        rs = by_n[n]
        mins = [r['min_non_adj_ham'] for r in rs if r['min_non_adj_ham'] is not None]
        if not mins:
            continue
        print(f"    n={n}: {len(rs)} cycles, min_non_adj_ham values: "
              f"min={min(mins)}, max={max(mins)}, "
              f"#cycles_with_min_1={sum(1 for m in mins if m == 1)}")

    # Ham-1 pair vs L check (shape 2)
    print("\n  Shape (2) — |Ham-1 pairs in C| vs L:")
    for n in sorted(by_n):
        rs = by_n[n]
        diffs = [r['ham1_count'] - r['L'] for r in rs]  # should be 0 if sep holds
        print(f"    n={n}: {len(rs)} cycles, "
              f"Ham-1_count − L range: min={min(diffs)}, max={max(diffs)}, "
              f"#violations={sum(1 for d in diffs if d > 0)}")

    # Global verdict
    violations = [r for r in rows
                  if r['min_non_adj_ham'] is not None and r['min_non_adj_ham'] < 2]
    if violations:
        print(f"\n  *** SHAPE (3) FAILS: {len(violations)} cycles have "
              f"non-adjacent Ham-1 pair ***")
        for v in violations[:5]:
            print(f"    n={v['n']} ms={v['ms']} L={v['L']} "
                  f"non-adj Ham-1 pairs: {v['ham1_non_adj_pairs']}")
        print(f"\n  Shape (3) separation lemma DEAD. "
              f"Fall back to shape (2) analytical bound.")
    else:
        print(f"\n  *** SHAPE (3) HOLDS UNIFORMLY across {len(rows)} cycles ***")
        print(f"  Every non-adjacent cycle pair has Hamming distance ≥ 2.")
        print(f"  Consequence: ε = 0 exactly (no Case-A C-collisions).")
        print(f"  Analytical target: prove separation ≥ 2 from simplicity")
        print(f"  + fairness + unique-priv for any sub-threshold good cycle.")

    out_dir = os.path.normpath(
        os.path.join(HERE, '..', 'lean', 'docs', 'sk', 'sk_phase0_out')
    )
    out_path = os.path.join(
        out_dir, 'r4_epsilon_separation_2026-04-19.json'
    )
    with open(out_path, 'w') as f:
        # strip non-serializable
        dumpable = [{k: v for k, v in r.items()
                     if k != 'min_non_adj_pair'} for r in rows]
        json.dump(dumpable, f)
    print(f"\n  Wrote {out_path}")

    sys.exit(0 if not violations else 1)


if __name__ == "__main__":
    main()
