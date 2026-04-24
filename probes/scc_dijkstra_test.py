#!/usr/bin/env python3
"""scc_dijkstra_test.py — How does Dijkstra's Solution 3 escape the same 3 SCCs?

Key finding: The 3 bad SCCs of [252, 168, 72] exist even for the all-ternary
3^9 = 19683 system with the uniform sweep cycle. But Dijkstra's Solution 3
WORKS at 3^9. So how does it escape?

Answer hypothesis: Dijkstra's Sol 3 does NOT use a uniform sweep cycle.
Its good cycle must be fundamentally different.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import Counter

# Import the verifier
from verifier import verify_dijkstra_solution3


def construct_sweep_cycle(ms, n, nb_vals):
    config = [0] * n
    cycle = [tuple(config)]
    for proc in range(n):
        config = list(cycle[-1])
        new_val = nb_vals.get(proc, 1) if ms[proc] > 2 else 1
        if ms[proc] == 2:
            new_val = 1
        if config[proc] == new_val:
            return None
        config[proc] = new_val
        cycle.append(tuple(config))
    for proc in range(n):
        config = list(cycle[-1])
        if config[proc] == 0:
            return None
        config[proc] = 0
        cycle.append(tuple(config))
    if cycle[-1] == cycle[0]:
        cycle = cycle[:-1]
    return cycle


def check_cycle_consistency(cycle_configs, n, ms):
    L = len(cycle_configs)
    required = {}
    for idx in range(L):
        c = cycle_configs[idx]
        c_next = cycle_configs[(idx + 1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return False, {}
        mover = diffs[0]
        Li = c[(mover - 1) % n]; Si = c[mover]; Ri = c[(mover + 1) % n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            return False, {}
        required[key] = S_new
        for i in range(n):
            if i != mover:
                Li = c[(i - 1) % n]; Si = c[i]; Ri = c[(i + 1) % n]
                key = (i, Li, Si, Ri)
                if key in required and required[key] != Si:
                    return False, {}
                required[key] = Si
    return True, required


def find_sccs(forced_succs):
    """Iterative Tarjan SCC."""
    index_counter = [0]
    stack = []
    on_stack = set()
    index_map = {}
    lowlink = {}
    sccs = []

    def strongconnect_iter(v):
        work = [(v, 0)]
        index_map[v] = lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)
        while work:
            node, si = work[-1]
            succs = forced_succs.get(node, [])
            if si < len(succs):
                work[-1] = (node, si + 1)
                w = succs[si]
                if w not in index_map:
                    index_map[w] = lowlink[w] = index_counter[0]
                    index_counter[0] += 1
                    stack.append(w)
                    on_stack.add(w)
                    work.append((w, 0))
                elif w in on_stack:
                    lowlink[node] = min(lowlink[node], index_map[w])
            else:
                if lowlink[node] == index_map[node]:
                    scc = []
                    while True:
                        w = stack.pop()
                        on_stack.discard(w)
                        scc.append(w)
                        if w == node:
                            break
                    if len(scc) > 1 or (len(scc) == 1 and node in forced_succs.get(node, [])):
                        sccs.append(scc)
                work.pop()
                if work:
                    parent = work[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[node])

    for v in forced_succs:
        if v not in index_map:
            strongconnect_iter(v)

    return sccs


def dijkstra_sol3_transition(config, n, K=3):
    """Dijkstra's Solution 3: P_i is privileged if s_i ≠ s_{i-1}.
    Move: s_i := s_{i-1}.
    For P_0: privileged if s_0 ≠ s_{n-1} + 1 mod K.
    Move: s_0 := s_{n-1} + 1 mod K.
    """
    privileged = []
    for i in range(n):
        if i == 0:
            if config[0] != (config[n-1] + 1) % K:
                privileged.append(i)
        else:
            if config[i] != config[i-1]:
                privileged.append(i)
    return privileged


def build_dijkstra_good_cycle(n, K=3):
    """Build the legitimate cycle for Dijkstra's Solution 3.
    Legitimate configs: exactly one token (one privilege).
    Token at P_0: s_0 ≠ (s_{n-1} + 1) mod K and s_i = s_{i-1} for all i > 0.
    So s_1 = s_0, s_2 = s_1 = s_0, ..., s_{n-1} = s_0.
    And s_0 ≠ (s_0 + 1) mod K, i.e., -1 ≢ 1 mod K, which is K ≠ 2.
    So for K=3: config is (v, v, v, ..., v) and v ≠ (v+1)%3.
    Wait, that's v ≠ v+1 mod 3, which is always true for K≥2.
    So token at P_0: all same value v, (v, v, ..., v), for any v.

    Token at P_i (i>0): s_i ≠ s_{i-1}, but s_j = s_{j-1} for all j ≠ 0, j ≠ i.
    And s_0 = (s_{n-1} + 1) mod K.
    """
    # Actually, let's just enumerate all configs with exactly one privilege
    all_configs = list(cartesian(*(range(K) for _ in range(n))))
    legitimate = []
    for c in all_configs:
        priv = dijkstra_sol3_transition(c, n, K)
        if len(priv) == 1:
            legitimate.append(c)

    print(f"  Legitimate configs (1 privilege): {len(legitimate)}")

    # Build the transition graph on legitimate configs
    # When P_i moves, it changes according to the rule
    transitions = {}
    for c in legitimate:
        priv = dijkstra_sol3_transition(c, n, K)
        mover = priv[0]
        new_c = list(c)
        if mover == 0:
            new_c[0] = (c[n-1] + 1) % K
        else:
            new_c[mover] = c[mover - 1]
        new_c = tuple(new_c)
        transitions[c] = (new_c, mover)

    # Find cycle(s) starting from (0,0,...,0)
    start = (0,) * n
    path = [start]
    seen = {start: 0}
    c = start
    while True:
        next_c, mover = transitions[c]
        if next_c in seen:
            cycle_start = seen[next_c]
            cycle = path[cycle_start:]
            break
        seen[next_c] = len(path)
        path.append(next_c)
        c = next_c

    print(f"  Good cycle length: {len(cycle)}")

    # Extract movers
    movers = []
    for idx in range(len(cycle)):
        c_cur = cycle[idx]
        c_nxt = cycle[(idx + 1) % len(cycle)]
        diffs = [j for j in range(n) if c_cur[j] != c_nxt[j]]
        movers.append(diffs[0])

    return cycle, movers


def main():
    n = 9
    K = 3
    print("=" * 70)
    print("DIJKSTRA'S SOLUTION 3 vs SCC OBSTRUCTION")
    print("=" * 70)

    # Step 1: Build Dijkstra's good cycle
    print("\n--- Dijkstra's Solution 3 Good Cycle ---")
    cycle, movers = build_dijkstra_good_cycle(n, K)
    print(f"  Movers (first 30): {movers[:30]}")
    mover_counts = Counter(movers)
    print(f"  Mover distribution: {dict(sorted(mover_counts.items()))}")

    # Is this a uniform sweep?
    is_sweep = True
    for i in range(len(movers)):
        if movers[i] != i % n:
            is_sweep = False
            break
    print(f"  Is uniform sweep [0,1,...,n-1,...]: {is_sweep}")

    # Check cycle consistency and get determined entries
    ms = [K] * n
    ok, det = check_cycle_consistency(cycle, n, ms)
    print(f"  Cycle consistent: {ok}")
    print(f"  Determined entries: {len(det)}")
    n_forcing = sum(1 for (i, L, S, R), v in det.items() if v != S)
    total_possible = sum(ms[(i-1)%n] * ms[i] * ms[(i+1)%n] for i in range(n))
    print(f"  Forcing entries: {n_forcing}")
    print(f"  Total possible LRT tuples: {total_possible}")
    print(f"  Coverage: {100*len(det)/total_possible:.1f}%")

    # Step 2: Check SCCs with Dijkstra's determined entries
    print("\n--- SCC Analysis with Dijkstra's det ---")
    good_set = set(cycle)
    all_configs = list(cartesian(*(range(K) for _ in range(n))))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    forced_succs = {}
    for c in non_good:
        succs = []
        for i in range(n):
            L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
            key = (i, L, S, R)
            if key in det and det[key] != S:
                new_c = list(c)
                new_c[i] = det[key]
                new_c = tuple(new_c)
                if new_c in non_good_set:
                    succs.append(new_c)
        if succs:
            forced_succs[c] = succs

    sccs = find_sccs(forced_succs)
    sizes = sorted([len(s) for s in sccs], reverse=True)
    total_scc = sum(sizes)
    print(f"  SCCs: {len(sccs)}, sizes={sizes}, total={total_scc}")

    if total_scc == 0:
        print("  *** DIJKSTRA'S CYCLE HAS NO BAD SCCs! ***")
        print("  Its determined entries avoid trapping any configs.")
    else:
        print(f"  BAD SCCs exist: {sizes}")

    # Step 3: Compare determined entries
    print("\n--- Comparing determined entries ---")
    # Get sweep det for same ms
    sweep_cycle = construct_sweep_cycle(ms, n, {i: 1 for i in range(n)})
    ok_sweep, det_sweep = check_cycle_consistency(sweep_cycle, n, ms)

    # Entries in Dijkstra but not sweep, and vice versa
    dij_keys = set(det.keys())
    sweep_keys = set(det_sweep.keys())
    shared = dij_keys & sweep_keys
    only_dij = dij_keys - sweep_keys
    only_sweep = sweep_keys - dij_keys

    print(f"  Dijkstra det: {len(dij_keys)} entries")
    print(f"  Sweep det: {len(sweep_keys)} entries")
    print(f"  Shared: {len(shared)}")
    print(f"  Only Dijkstra: {len(only_dij)}")
    print(f"  Only sweep: {len(only_sweep)}")

    # Among shared entries, how many agree?
    agree = sum(1 for k in shared if det[k] == det_sweep[k])
    disagree = len(shared) - agree
    print(f"  Shared entries that agree: {agree}")
    print(f"  Shared entries that disagree: {disagree}")

    # Show disagreements
    if disagree > 0:
        print(f"\n  Disagreeing entries (first 10):")
        count = 0
        for k in sorted(shared):
            if det[k] != det_sweep[k]:
                print(f"    {k}: Dijkstra→{det[k]}, Sweep→{det_sweep[k]}")
                count += 1
                if count >= 10:
                    break

    # Step 4: Which specific determined entries of the sweep create the SCC traps?
    print("\n--- Which sweep entries create the traps? ---")
    # For the 492 SCC configs, which forcing entries keep them trapped?
    scc_ref_configs = set()
    sweep_all_configs = list(cartesian(*(range(K) for _ in range(n))))
    sweep_good = set(sweep_cycle)
    sweep_nongood = [c for c in sweep_all_configs if c not in sweep_good]
    sweep_nongood_set = set(sweep_nongood)
    sweep_fs = {}
    for c in sweep_nongood:
        succs = []
        for i in range(n):
            L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
            key = (i, L, S, R)
            if key in det_sweep and det_sweep[key] != S:
                new_c = list(c)
                new_c[i] = det_sweep[key]
                new_c = tuple(new_c)
                if new_c in sweep_nongood_set:
                    succs.append(new_c)
        if succs:
            sweep_fs[c] = succs
    sweep_sccs = find_sccs(sweep_fs)
    for scc in sweep_sccs:
        scc_ref_configs.update(scc)

    # Find which det entries are used within the SCCs
    trap_entries = set()
    for c in scc_ref_configs:
        for i in range(n):
            L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
            key = (i, L, S, R)
            if key in det_sweep and det_sweep[key] != S:
                new_c = list(c)
                new_c[i] = det_sweep[key]
                if tuple(new_c) in scc_ref_configs:
                    trap_entries.add(key)

    print(f"  Det entries creating internal SCC transitions: {len(trap_entries)}")
    for entry in sorted(trap_entries):
        i, L, S, R = entry
        print(f"    P{i}: ({L},{S},{R}) → {det_sweep[entry]}")

    # Does Dijkstra disagree on these entries?
    print(f"\n  Do Dijkstra entries disagree on trap entries?")
    for entry in sorted(trap_entries):
        if entry in det:
            if det[entry] != det_sweep[entry]:
                print(f"    {entry}: Dijkstra→{det[entry]}, Sweep→{det_sweep[entry]} *** DISAGREE ***")
            else:
                print(f"    {entry}: both→{det[entry]}")
        else:
            print(f"    {entry}: not determined by Dijkstra (FREE)")


if __name__ == "__main__":
    main()
