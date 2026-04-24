#!/usr/bin/env python3
"""scc_correct_sol3.py — Test the CORRECT Dijkstra Sol 3 under the SCC screen.

The verifier uses a different rule than I initially coded.
Check: does the correct Sol 3's good cycle create bad SCCs in the forced graph?
"""

from itertools import product as cartesian
from collections import Counter


def f_bottom(L, S, R):
    if (S + 1) % 3 == R:
        return (S - 1) % 3
    return S


def f_top(L, S, R):
    if L == R and (L + 1) % 3 != S:
        return (L + 1) % 3
    return S


def f_middle(L, S, R):
    if (S + 1) % 3 == L:
        return L
    if (S + 1) % 3 == R:
        return R
    return S


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


def main():
    n = 9
    K = 3
    print("=" * 70)
    print(f"CORRECT DIJKSTRA SOL 3 — SCC SCREEN TEST")
    print("=" * 70)

    # Build rule functions
    fs = [f_bottom] + [f_middle] * (n - 2) + [f_top]

    # Find all configs and their privileges
    all_configs = list(cartesian(*(range(K) for _ in range(n))))
    print(f"Total configs: {len(all_configs)}")

    # Find legitimate configs (exactly 1 privilege)
    legit = []
    for c in all_configs:
        privs = []
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            if fs[i](L, S, R) != S:
                privs.append(i)
        if len(privs) == 1:
            legit.append(c)

    legit_set = set(legit)
    print(f"Legitimate (1 privilege): {len(legit)}")

    # Build the good cycle by following single-privilege transitions
    start = legit[0]
    cycle = [start]
    c = start
    seen_cyc = {start}
    while True:
        privs = []
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            if fs[i](L, S, R) != S:
                privs.append(i)
        assert len(privs) == 1
        mover = privs[0]
        new_c = list(c)
        new_c[mover] = fs[mover](c[(mover-1)%n], c[mover], c[(mover+1)%n])
        new_c = tuple(new_c)
        if new_c in seen_cyc:
            break
        cycle.append(new_c)
        seen_cyc.add(new_c)
        c = new_c

    print(f"Good cycle length: {len(cycle)}")

    # Check: do all legitimate configs appear in the cycle?
    cycle_set = set(cycle)
    missing = legit_set - cycle_set
    extra = cycle_set - legit_set
    print(f"Cycle configs in legit: {len(cycle_set & legit_set)}/{len(cycle)}")
    print(f"Legit configs not in cycle: {len(missing)}")

    # If multiple cycles exist among legit configs, find them
    if missing:
        remaining = list(missing)
        all_cycles = [cycle]
        while remaining:
            start2 = remaining[0]
            cyc2 = [start2]
            c = start2
            seen2 = {start2}
            while True:
                privs = []
                for i in range(n):
                    L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
                    if fs[i](L, S, R) != S:
                        privs.append(i)
                mover = privs[0]
                new_c = list(c)
                new_c[mover] = fs[mover](c[(mover-1)%n], c[mover], c[(mover+1)%n])
                new_c = tuple(new_c)
                if new_c in seen2:
                    break
                cyc2.append(new_c)
                seen2.add(new_c)
                c = new_c
            all_cycles.append(cyc2)
            remaining = [x for x in remaining if x not in set(cyc2)]

        print(f"Number of legitimate cycles: {len(all_cycles)}")
        for ci, cyc in enumerate(all_cycles):
            print(f"  Cycle {ci+1}: length {len(cyc)}")

    # Extract movers from the cycle
    movers = []
    for idx in range(len(cycle)):
        c_cur = cycle[idx]
        c_nxt = cycle[(idx + 1) % len(cycle)]
        diffs = [j for j in range(n) if c_cur[j] != c_nxt[j]]
        movers.append(diffs[0])
    print(f"Movers: {movers}")

    # Extract determined entries from ALL legitimate configs (using the complete rule)
    # Actually, we need to use the good cycle's determined entries
    det = {}
    for idx in range(len(cycle)):
        c_cur = cycle[idx]
        c_nxt = cycle[(idx + 1) % len(cycle)]
        diffs = [j for j in range(n) if c_cur[j] != c_nxt[j]]
        mover = diffs[0]
        for i in range(n):
            L = c_cur[(i-1) % n]; S = c_cur[i]; R = c_cur[(i+1) % n]
            if i == mover:
                det[(i, L, S, R)] = c_nxt[i]
            else:
                det[(i, L, S, R)] = S

    n_forcing = sum(1 for (i, L, S, R), v in det.items() if v != S)
    total_possible = n * K * K * K  # each proc has K^3 possible (L,S,R)
    print(f"\nDetermined entries: {len(det)}/{total_possible} ({100*len(det)/total_possible:.1f}%)")
    print(f"Forcing entries: {n_forcing}")

    # Build forced-successor graph among non-good configs
    good_set = set(cycle)
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    forced_succs = {}
    for c in non_good:
        succs = []
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
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
    print(f"\nSCCs in forced graph: {len(sccs)}, sizes={sizes[:10]}, total={total_scc}")

    if total_scc == 0:
        print("\n*** SOL 3 GOOD CYCLE HAS NO BAD SCCs! ***")
        print("The SCC screen passes. Dijkstra Sol 3's cycle is 'clean'.")
        print("This confirms the SCC screen is sound for the correct Sol 3.")
    else:
        print(f"\nSOL 3 STILL has bad SCCs: {sizes[:10]}")

        # Check the SCC configs
        scc_configs = set()
        for scc in sccs:
            scc_configs.update(scc)

        max_vals = [max(c[i] for c in scc_configs) for i in range(n)]
        print(f"Max values in SCC configs: {max_vals}")

        # Compare with sweep SCCs
        print(f"\n--- Comparison with uniform sweep SCCs ---")
        # Build sweep cycle for ms=(3,...,3)
        sweep_config = [0] * n
        sweep_cycle = [tuple(sweep_config)]
        for proc in range(n):
            sweep_config = list(sweep_cycle[-1])
            sweep_config[proc] = 1
            sweep_cycle.append(tuple(sweep_config))
        for proc in range(n):
            sweep_config = list(sweep_cycle[-1])
            sweep_config[proc] = 0
            sweep_cycle.append(tuple(sweep_config))
        if sweep_cycle[-1] == sweep_cycle[0]:
            sweep_cycle = sweep_cycle[:-1]

        sweep_det = {}
        for idx in range(len(sweep_cycle)):
            c_cur = sweep_cycle[idx]
            c_nxt = sweep_cycle[(idx + 1) % len(sweep_cycle)]
            diffs = [j for j in range(n) if c_cur[j] != c_nxt[j]]
            mover = diffs[0]
            for i in range(n):
                L = c_cur[(i-1) % n]; S = c_cur[i]; R = c_cur[(i+1) % n]
                if i == mover:
                    sweep_det[(i, L, S, R)] = c_nxt[i]
                else:
                    sweep_det[(i, L, S, R)] = S

        sweep_good = set(sweep_cycle)
        sweep_nongood = [c for c in all_configs if c not in sweep_good]
        sweep_nongood_set = set(sweep_nongood)

        sweep_fs = {}
        for c in sweep_nongood:
            succs = []
            for i in range(n):
                L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
                key = (i, L, S, R)
                if key in sweep_det and sweep_det[key] != S:
                    new_c = list(c)
                    new_c[i] = sweep_det[key]
                    new_c = tuple(new_c)
                    if new_c in sweep_nongood_set:
                        succs.append(new_c)
            if succs:
                sweep_fs[c] = succs

        sweep_sccs = find_sccs(sweep_fs)
        sweep_sizes = sorted([len(s) for s in sweep_sccs], reverse=True)
        print(f"Sweep SCCs: {len(sweep_sccs)}, sizes={sweep_sizes}")

        # Overlap between Sol 3 SCC configs and sweep SCC configs
        sweep_scc_configs = set()
        for scc in sweep_sccs:
            sweep_scc_configs.update(scc)
        overlap = scc_configs & sweep_scc_configs
        print(f"Sol3 SCC configs: {len(scc_configs)}")
        print(f"Sweep SCC configs: {len(sweep_scc_configs)}")
        print(f"Overlap: {len(overlap)}")

    # Now check the COMPLETE transition graph
    print(f"\n--- Complete transition graph (correct Sol 3 rules) ---")
    non_legit = [c for c in all_configs if c not in legit_set]
    non_legit_set = set(non_legit)

    complete_fs = {}
    for c in non_legit:
        succs = []
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            new_val = fs[i](L, S, R)
            if new_val != S:
                new_c = list(c)
                new_c[i] = new_val
                new_c = tuple(new_c)
                if new_c in non_legit_set:
                    succs.append(new_c)
        if succs:
            complete_fs[c] = succs

    complete_sccs = find_sccs(complete_fs)
    complete_sizes = sorted([len(s) for s in complete_sccs], reverse=True)
    print(f"SCCs in complete graph: {len(complete_sccs)}, sizes={complete_sizes[:10]}, total={sum(complete_sizes)}")

    if sum(complete_sizes) == 0:
        print("*** COMPLETE GRAPH HAS NO SCCS — CONVERGENCE CONFIRMED ***")
    else:
        print(f"Complete graph has {sum(complete_sizes)} configs in SCCs")
        # Check escape moves
        for si, scc in enumerate(complete_sccs[:5]):
            scc_set = set(scc)
            n_escape = sum(1 for c in scc
                          if any(tuple(list(c)[:j] + [fs[j](c[(j-1)%n], c[j], c[(j+1)%n])] + list(c)[j+1:])
                                 not in scc_set and fs[j](c[(j-1)%n], c[j], c[(j+1)%n]) != c[j]
                                 for j in range(n)))
            print(f"  SCC #{si+1} ({len(scc)}): {n_escape}/{len(scc)} have escape")


if __name__ == "__main__":
    main()
