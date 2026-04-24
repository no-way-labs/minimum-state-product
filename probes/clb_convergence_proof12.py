#!/usr/bin/env python3
"""
CONVERGENCE PROOF — Part 12: Interior Rank Transfer
=====================================================

KEY INSIGHT FROM PART 11:
- Interior of each boundary partition (c[0], c[n-1]) forms a DAG
- Boundary transitions always cross partitions (never same)
- Boundary graph has cycles BUT the full graph is a DAG
- Therefore: interior rank progression prevents boundary cycles

This script computes:
1. Interior rank of each config in its boundary partition
2. For each boundary transition c → c', how interior rank changes
   (c and c' are in DIFFERENT partitions, so ranks are in different DAGs)
3. Whether a "transfer function" φ: interior_rank_old → interior_rank_new
   is always strictly decreasing

If the interior rank ALWAYS decreases on boundary transitions,
combined with the interior DAG property, the full graph is a DAG.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, deque, Counter
import numpy as np

def compute_interior_ranks(n):
    """Compute interior DAG rank for each config within its boundary partition."""
    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    # Partition by boundary
    partitions = defaultdict(list)
    for c in bad_list:
        partitions[(c[0], c[n-1])].append(c)

    # Compute interior rank for each partition
    interior_rank = {}  # config -> rank within its partition's interior DAG

    for (b0, bn), configs in partitions.items():
        config_set = set(configs)
        adj = {c: [] for c in configs}
        for c in configs:
            for i in range(1, n-1):  # interior only
                L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c); lst[i] = new_S; succ = tuple(lst)
                    if succ in config_set:
                        adj[c].append(succ)

        # Topological sort
        in_deg = {c: 0 for c in configs}
        for c in configs:
            for s in adj[c]:
                in_deg[s] += 1
        q = deque(c for c in configs if in_deg[c] == 0)
        topo = []
        while q:
            c = q.popleft()
            topo.append(c)
            for s in adj[c]:
                in_deg[s] -= 1
                if in_deg[s] == 0:
                    q.append(s)

        rank = {}
        for c in reversed(topo):
            rank[c] = max((rank[s] + 1 for s in adj[c]), default=0)

        for c in configs:
            interior_rank[c] = rank[c]

    return interior_rank, bad_list, bad_set, ms, fs, good_set, partitions

def analyze_boundary_transfer(n):
    """
    For each boundary transition c → c', compute:
    - interior_rank(c) in partition of c
    - interior_rank(c') in partition of c'
    - Whether the rank always decreases, increases, or varies
    """
    print(f"\nBOUNDARY TRANSFER ANALYSIS (n={n})")
    print("=" * 70)

    interior_rank, bad_list, bad_set, ms, fs, good_set, partitions = compute_interior_ranks(n)

    # Also compute full DAG rank for comparison
    adj_full = {c: [] for c in bad_list}
    for c in bad_list:
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    adj_full[c].append((succ, i))

    in_deg = {c: 0 for c in bad_list}
    for c in bad_list:
        for s, _ in adj_full[c]:
            in_deg[s] += 1
    q = deque(c for c in bad_list if in_deg[c] == 0)
    topo = []
    while q:
        c = q.popleft()
        topo.append(c)
        for s, _ in adj_full[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)
    full_rank = {}
    for c in reversed(topo):
        full_rank[c] = max((full_rank[s] + 1 for s, _ in adj_full[c]), default=0)

    # Analyze boundary transitions
    print("  Boundary transition interior rank transfer:")
    print(f"  {'Type':>15s} {'n':>4s} {'ΔI_rank range':>15s} {'ΔI mean':>10s} "
          f"{'Always dec':>10s} {'ΔFull range':>15s}")
    print("  " + "-" * 75)

    trans_types = defaultdict(list)

    for c in bad_list:
        for i in [0, n-1]:
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    bfrom = (c[0], c[n-1])
                    bto = (succ[0], succ[n-1])
                    ir_from = interior_rank[c]
                    ir_to = interior_rank[succ]
                    fr_from = full_rank[c]
                    fr_to = full_rank[succ]
                    key = (bfrom, bto, 'P0' if i == 0 else f'P{n-1}')
                    trans_types[key].append((ir_from, ir_to, fr_from, fr_to, c, succ))

    for key in sorted(trans_types.keys()):
        bfrom, bto, pos = key
        items = trans_types[key]
        di = [ir_to - ir_from for ir_from, ir_to, _, _, _, _ in items]
        df = [fr_to - fr_from for _, _, fr_from, fr_to, _, _ in items]
        always_dec = all(d < 0 for d in di)
        print(f"  {bfrom}→{bto} {pos:>3s} {len(items):>4d} "
              f"[{min(di):+d},{max(di):+d}]{'':<6s} {np.mean(di):>+10.2f} "
              f"{'✓' if always_dec else '✗':>10s} "
              f"[{min(df):+d},{max(df):+d}]")

        # Show violations (interior rank doesn't decrease)
        if not always_dec:
            violations = [(ir_from, ir_to, c, succ) for ir_from, ir_to, _, _, c, succ in items
                         if ir_to >= ir_from]
            print(f"    VIOLATIONS ({len(violations)}):")
            for ir_from, ir_to, c, succ in violations[:5]:
                print(f"      {c} (I_rank={ir_from}) → {succ} (I_rank={ir_to}), "
                      f"Δ={ir_to-ir_from:+d}, full_rank: {full_rank[c]}→{full_rank[succ]}")

def test_interior_rank_as_potential(n):
    """
    Test: φ(c) = interior_rank(c) within partition (c[0], c[n-1]).

    For interior transitions: φ strictly decreases (by definition).
    For boundary transitions: φ may increase or decrease.

    If φ always decreases on boundary transitions too, then φ is a
    valid potential for the full graph → proof complete.
    """
    print(f"\nINTERIOR RANK AS FULL POTENTIAL (n={n})")
    print("=" * 70)

    interior_rank, bad_list, bad_set, ms, fs, good_set, _ = compute_interior_ranks(n)

    total = 0
    violations = 0
    by_type = defaultdict(lambda: [0, 0])  # type -> [total, violations]

    for c in bad_list:
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    total += 1
                    ir_c = interior_rank[c]
                    ir_s = interior_rank[succ]
                    is_boundary = (i == 0 or i == n-1)

                    ttype = 'boundary' if is_boundary else 'interior'
                    by_type[ttype][0] += 1

                    if ir_s >= ir_c:
                        violations += 1
                        by_type[ttype][1] += 1

    print(f"  Total violations: {violations}/{total} ({100*violations/total:.1f}%)")
    for ttype in ['interior', 'boundary']:
        t, v = by_type[ttype]
        if t > 0:
            print(f"    {ttype}: {v}/{t} ({100*v/t:.1f}%)")

def test_lexicographic_boundary_interior(n):
    """
    Test the LEX potential: (boundary_level, interior_rank)

    Define boundary_level(c) based on boundary state (c[0], c[n-1]).
    If there's a consistent ordering of boundary states that makes
    boundary_level decrease on boundary transitions, then combined
    with the interior DAG, we get a full DAG.

    We know the boundary graph has cycles, so no fixed level works.
    BUT: what if the level depends on the full config?
    """
    print(f"\nLEXICOGRAPHIC POTENTIAL TESTS (n={n})")
    print("=" * 70)

    interior_rank, bad_list, bad_set, ms, fs, good_set, _ = compute_interior_ranks(n)

    # Compute full rank
    adj_full = {c: [] for c in bad_list}
    for c in bad_list:
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    adj_full[c].append((succ, i))

    in_deg = {c: 0 for c in bad_list}
    for c in bad_list:
        for s, _ in adj_full[c]:
            in_deg[s] += 1
    q = deque(c for c in bad_list if in_deg[c] == 0)
    topo = []
    while q:
        c = q.popleft()
        topo.append(c)
        for s, _ in adj_full[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)
    full_rank = {}
    for c in reversed(topo):
        full_rank[c] = max((full_rank[s] + 1 for s, _ in adj_full[c]), default=0)

    # Try: φ = (interior_rank, c[0]+c[n-1])
    # Or: φ = (c[0]+c[n-1], interior_rank)
    # Or: φ = (interior_rank + k * boundary_level)

    tests = [
        ("I_rank alone", lambda c: (interior_rank[c],)),
        ("(I_rank, sum_boundary)", lambda c: (interior_rank[c], c[0]+c[n-1])),
        ("(sum_boundary, I_rank)", lambda c: (c[0]+c[n-1], interior_rank[c])),
        ("(-sum_boundary, I_rank)", lambda c: (-(c[0]+c[n-1]), interior_rank[c])),
        ("I_rank + 10*boundary",
         lambda c: (interior_rank[c] + 10 * (c[0]+c[n-1]),)),
        ("I_rank - 5*boundary",
         lambda c: (interior_rank[c] - 5 * (c[0]+c[n-1]),)),
    ]

    for name, phi in tests:
        violations = 0
        total = 0
        for c in bad_list:
            phi_c = phi(c)
            for s, i in adj_full[c]:
                phi_s = phi(s)
                total += 1
                if phi_s >= phi_c:
                    violations += 1
        pct = 100 * violations / total if total > 0 else 0
        print(f"  {name:>30s}: {violations}/{total} violations ({pct:.1f}%)")

    # Try: φ(c) = I_rank + α * (c[0] + c[n-1]) for various α
    print(f"\n  Sweep α in I_rank + α * boundary:")
    best_alpha = None
    best_viol = float('inf')
    for alpha_10 in range(-100, 101, 5):
        alpha = alpha_10 / 10.0
        violations = 0
        total = 0
        for c in bad_list:
            phi_c = interior_rank[c] + alpha * (c[0] + c[n-1])
            for s, i in adj_full[c]:
                phi_s = interior_rank[s] + alpha * (s[0] + s[n-1])
                total += 1
                if phi_s >= phi_c:
                    violations += 1
        if violations < best_viol:
            best_viol = violations
            best_alpha = alpha
    pct = 100 * best_viol / total if total > 0 else 0
    print(f"  Best α={best_alpha:.1f}: {best_viol}/{total} violations ({pct:.1f}%)")

    # Try with position-specific boundary terms
    print(f"\n  Sweep I_rank + α*c[0] + β*c[{n-1}]:")
    best_ab = None
    best_viol = float('inf')
    for a10 in range(-100, 101, 10):
        for b10 in range(-100, 101, 10):
            a, b = a10/10, b10/10
            violations = 0
            total = 0
            for c in bad_list:
                phi_c = interior_rank[c] + a * c[0] + b * c[n-1]
                for s, i in adj_full[c]:
                    phi_s = interior_rank[s] + a * s[0] + b * s[n-1]
                    total += 1
                    if phi_s >= phi_c:
                        violations += 1
            if violations < best_viol:
                best_viol = violations
                best_ab = (a, b)
    pct = 100 * best_viol / total if total > 0 else 0
    print(f"  Best α={best_ab[0]:.1f}, β={best_ab[1]:.1f}: "
          f"{best_viol}/{total} violations ({pct:.1f}%)")

def analyze_boundary_transfer_structure(n):
    """
    For each boundary transition type, analyze how the INTERIOR STATE
    maps between partitions.

    The interior state c[1]..c[n-2] is preserved (only c[0] or c[n-1] changes).
    But the interior RANK changes because the DAG structure is different.

    Question: Is the change in interior rank predictable from local features?
    """
    print(f"\nBOUNDARY TRANSFER STRUCTURE (n={n})")
    print("=" * 70)

    interior_rank, bad_list, bad_set, ms, fs, good_set, partitions = compute_interior_ranks(n)

    # For T_bot firing: c[0] changes. Interior = c[1..n-2].
    # The interior rank changes because c[0] affects which transitions
    # are available at position 1 (T_low sees c[0] as left neighbor).
    # Specifically: T_low with L=0 vs L=1 have different transitions.

    # What exactly changes at position 1 when c[0] toggles?
    print("  Position 1 (T_low) transition changes when c[0] toggles:")
    for S in range(3):
        for R in range(3):
            out_L0 = T_low[(0, S, R)]
            out_L1 = T_low[(1, S, R)]
            if out_L0 != out_L1:
                priv0 = out_L0 != S
                priv1 = out_L1 != S
                print(f"    (L=?,{S},{R}): L=0→{out_L0}{'*' if priv0 else ' '}, "
                      f"L=1→{out_L1}{'*' if priv1 else ' '}")

    # For T_top firing: c[n-1] changes. Interior = c[1..n-2].
    # This affects position n-2 (T_high sees c[n-1] as right neighbor).
    print(f"\n  Position {n-2} (T_high) transition changes when c[{n-1}] toggles:")
    for L in range(3):
        for S in range(3):
            out_R0 = T_high[(L, S, 0)]
            out_R1 = T_high[(L, S, 1)]
            if out_R0 != out_R1:
                priv0 = out_R0 != S
                priv1 = out_R1 != S
                print(f"    ({L},{S},R=?): R=0→{out_R0}{'*' if priv0 else ' '}, "
                      f"R=1→{out_R1}{'*' if priv1 else ' '}")

    # Count: how many interior positions change their settled status
    # when a boundary toggles?
    print(f"\n  Interior settled changes on boundary toggle:")
    for btype in ['P0', f'P{n-1}']:
        settled_changes = Counter()
        for c in bad_list:
            i = 0 if btype == 'P0' else n-1
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    # Count interior settled status changes
                    n_changed = 0
                    for j in range(1, n-1):
                        Lj = c[(j-1)%n]; Sj = c[j]; Rj = c[(j+1)%n]
                        was_settled = (fs[j](Lj, Sj, Rj) == Sj)
                        Lj2 = succ[(j-1)%n]; Sj2 = succ[j]; Rj2 = succ[(j+1)%n]
                        is_settled = (fs[j](Lj2, Sj2, Rj2) == Sj2)
                        if was_settled != is_settled:
                            n_changed += 1
                    settled_changes[n_changed] += 1

        print(f"    {btype}: {dict(sorted(settled_changes.items()))}")

def test_normalized_interior_rank(n):
    """
    Try normalizing interior rank by partition depth.

    If r_int(c) is interior rank in partition P and D(P) is the depth,
    test whether r_int(c) / D(P) is a valid potential.
    """
    print(f"\nNORMALIZED INTERIOR RANK TEST (n={n})")
    print("=" * 70)

    interior_rank, bad_list, bad_set, ms, fs, good_set, partitions = compute_interior_ranks(n)

    # Compute partition depths
    part_depth = {}
    for (b0, bn), configs in partitions.items():
        if configs:
            part_depth[(b0, bn)] = max(interior_rank[c] for c in configs)

    print(f"  Partition depths: {part_depth}")

    # Build full adjacency
    adj_full = {c: [] for c in bad_list}
    for c in bad_list:
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    adj_full[c].append((succ, i))

    # Test normalized rank
    def norm_rank(c):
        p = (c[0], c[n-1])
        d = part_depth[p]
        return interior_rank[c] / d if d > 0 else 0

    violations = 0
    total = 0
    for c in bad_list:
        nr_c = norm_rank(c)
        for s, i in adj_full[c]:
            nr_s = norm_rank(s)
            total += 1
            if nr_s >= nr_c:
                violations += 1

    pct = 100 * violations / total if total > 0 else 0
    print(f"  Normalized I_rank: {violations}/{total} violations ({pct:.1f}%)")

    # Try: φ = interior_rank + K * max_partition_depth where K depends on partition
    # Idea: give a "bonus" to configs in partitions with larger interior DAGs
    # So transitions TO larger partitions get penalized

    for K in [0, 1, 2, 5, 10, -1, -2, -5]:
        violations = 0
        total = 0
        for c in bad_list:
            p = (c[0], c[n-1])
            phi_c = interior_rank[c] + K * part_depth[p]
            for s, i in adj_full[c]:
                p2 = (s[0], s[n-1])
                phi_s = interior_rank[s] + K * part_depth[p2]
                total += 1
                if phi_s >= phi_c:
                    violations += 1
        pct = 100 * violations / total if total > 0 else 0
        print(f"  I_rank + {K:+d}*D(partition): {violations}/{total} violations ({pct:.1f}%)")

def main():
    for n in [5, 6, 7]:
        print("\n" + "=" * 70)
        print(f"ANALYSIS FOR n={n}")
        print("=" * 70)

        analyze_boundary_transfer(n)
        test_interior_rank_as_potential(n)
        test_lexicographic_boundary_interior(n)
        analyze_boundary_transfer_structure(n)
        test_normalized_interior_rank(n)

if __name__ == "__main__":
    main()
