#!/usr/bin/env python3
"""
Verify the counterexample matches the exact Lean formalization.

System: n=4, ms=(3,3,3,3), CW sweep with stay-fill.
Check all Lean-formalized properties:
  1. GoodCycle exists (configs, nonempty, unique_privileged, closed, distinct, fair)
  2. converges = WellFounded(badStep)
  3. BUT: liveness fails (dead configs exist)
"""

from itertools import product as iproduct

def build_counterexample():
    n = 4
    ms = [3, 3, 3, 3]
    fs = [{} for _ in range(n)]

    # Build CW sweep good cycle
    c = [0, 0, 0, 0]
    cycle_configs = []
    cycle_movers = []

    for t in range(12):
        p = t % n
        config = tuple(c)
        cycle_configs.append(config)
        cycle_movers.append(p)
        L = c[(p-1) % n]
        S = c[p]
        R = c[(p+1) % n]
        fs[p][(L, S, R)] = (S + 1) % ms[p]
        c[p] = (c[p] + 1) % ms[p]

    assert tuple(c) == cycle_configs[0], "Cycle doesn't close!"

    # Fill free entries with stay
    for p in range(n):
        for L in range(ms[(p-1)%n]):
            for S in range(ms[p]):
                for R in range(ms[(p+1)%n]):
                    if (L,S,R) not in fs[p]:
                        fs[p][(L,S,R)] = S

    return n, ms, fs, cycle_configs, cycle_movers


def check_lean_properties():
    n, ms, fs, gc_configs, gc_movers = build_counterexample()
    gc_set = set(gc_configs)
    all_configs = list(iproduct(*(range(m) for m in ms)))
    L_gc = len(gc_configs)

    print("="*60)
    print("LEAN FORMALIZATION PROPERTY CHECK")
    print("="*60)

    # 1. nonempty
    print(f"\n1. nonempty: {L_gc > 0} (length={L_gc})")

    # 2. unique_privileged: for every config in gc, exactly one privileged proc
    all_ok = True
    for config in gc_configs:
        priv = []
        for i in range(n):
            Li = config[(i-1)%n]
            S = config[i]
            R = config[(i+1)%n]
            if fs[i][(Li, S, R)] != S:
                priv.append(i)
        if len(priv) != 1:
            print(f"  FAIL: {config} has {len(priv)} privileged: {priv}")
            all_ok = False
    print(f"2. unique_privileged: {all_ok}")

    # 3. closed: each step leads to the next config in the cycle
    all_ok = True
    for k in range(L_gc):
        config = gc_configs[k]
        next_config = gc_configs[(k+1) % L_gc]
        p = gc_movers[k]
        Li = config[(p-1)%n]
        S = config[p]
        R = config[(p+1)%n]
        new_s = fs[p][(Li, S, R)]
        moved = list(config)
        moved[p] = new_s
        moved = tuple(moved)
        if moved != next_config:
            print(f"  FAIL at k={k}: expected {next_config}, got {moved}")
            all_ok = False
    print(f"3. closed: {all_ok}")

    # 4. distinct: all configs pairwise distinct
    print(f"4. distinct: {len(set(gc_configs)) == L_gc}")

    # 5. fair: every processor fires at least once
    movers_seen = set(gc_movers)
    print(f"5. fair: {movers_seen == set(range(n))} (movers: {sorted(movers_seen)})")

    # 6. converges = WellFounded(badStep)
    # badStep c' c = c not in gc AND c' not in gc AND step c c'
    # We need to show: no infinite chain c_0, c_1, c_2, ... with badStep c_{i+1} c_i
    # Equivalently: the bad transition graph (restricted to bad configs) is acyclic

    bad_configs = [c for c in all_configs if c not in gc_set]
    bad_set = set(bad_configs)

    # Build bad transition graph
    bad_edges = {}
    for c in bad_configs:
        succs = set()
        for i in range(n):
            Li = c[(i-1)%n]
            S = c[i]
            R = c[(i+1)%n]
            if fs[i][(Li, S, R)] != S:
                moved = list(c)
                moved[i] = fs[i][(Li, S, R)]
                c2 = tuple(moved)
                if c2 in bad_set:
                    succs.add(c2)
        bad_edges[c] = succs

    # Check acyclicity via topological sort
    in_degree = {c: 0 for c in bad_configs}
    for c in bad_configs:
        for c2 in bad_edges[c]:
            in_degree[c2] += 1

    queue = [c for c in bad_configs if in_degree[c] == 0]
    processed = 0
    while queue:
        c = queue.pop()
        processed += 1
        for c2 in bad_edges[c]:
            in_degree[c2] -= 1
            if in_degree[c2] == 0:
                queue.append(c2)

    acyclic = (processed == len(bad_configs))
    print(f"6. converges (bad graph acyclic): {acyclic}")
    print(f"   Bad configs: {len(bad_configs)}, processed: {processed}")
    if not acyclic:
        print(f"   {len(bad_configs) - processed} configs in cycles")

    # 7. Liveness check (NOT in Lean formalization)
    dead = []
    for c in all_configs:
        priv = []
        for i in range(n):
            Li = c[(i-1)%n]
            S = c[i]
            R = c[(i+1)%n]
            if fs[i][(Li, S, R)] != S:
                priv.append(i)
        if len(priv) == 0:
            dead.append(c)

    print(f"\n--- LIVENESS (not in Lean formalization) ---")
    print(f"7. Dead configs (0 privileged): {len(dead)}")
    print(f"   Liveness holds: {len(dead) == 0}")
    if dead:
        print(f"   Non-good fixed points (first 10):")
        for c in dead[:10]:
            in_gc = c in gc_set
            print(f"     {c} {'(in gc)' if in_gc else '(NOT in gc)'}")

    # Why dead configs are vacuously well-founded
    print(f"\n--- WHY COUNTEREXAMPLE WORKS ---")
    print(f"Dead configs have 0 privileged procs → no outgoing step edges")
    print(f"→ no outgoing badStep edges → vacuously Acc")
    print(f"→ WellFounded(badStep) holds trivially for dead configs")
    print(f"→ converges=True despite liveness=False")

    # Count: how many bad configs have outgoing edges to bad configs?
    bad_with_bad_succs = sum(1 for c in bad_configs if bad_edges[c])
    bad_with_no_succs = sum(1 for c in bad_configs if not bad_edges[c])
    print(f"\nBad config analysis:")
    print(f"  Total bad: {len(bad_configs)}")
    print(f"  Dead (0 priv): {len(dead)}")
    print(f"  With bad successors: {bad_with_bad_succs}")
    print(f"  Without bad successors: {bad_with_no_succs}")
    print(f"  → all bad chains terminate (at dead configs or good configs)")

check_lean_properties()
