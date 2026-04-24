#!/usr/bin/env python3
"""CIC Exploration 9d: SCC lifting proof — why binary 6-cycle always lifts.

The gap: At n=6, no single ternary fiber supports all 6 binary edges.
The SCC uses cross-fiber ternary transitions. WHY does this always work?

Key insight to prove: P1's 2 ternary-independent edges create a
"backbone" that connects configs at P1=0 to P1=1 and back. The
remaining edges (P0, P2, ternary) provide enough connectivity to
close the cycle among non-good configs.

APPROACH:
1. Count forced edges per binary state pair
2. Show: for each P1 edge, ≥1 ternary fiber is non-good on both sides
3. Show: the forced graph has minimum out-degree ≥ 1 on a large set
4. Prove: the forced subgraph on non-good configs has a directed cycle
"""

from itertools import product as iproduct
from collections import defaultdict, Counter
import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))


def enumerate_cycles(ms, n, max_cycles=200, max_time=60.0, max_path_len=None):
    if max_path_len is None:
        max_path_len = 10 * n
    t0 = time.time()
    P = 1
    for m in ms:
        P *= m
    if P > 500:
        return []
    all_configs = list(iproduct(*[range(m) for m in ms]))
    cycles = []
    for start_idx in range(min(len(all_configs), P)):
        if time.time() - t0 > max_time:
            break
        start = all_configs[start_idx]
        stack = [(start, [start], {}, [])]
        nodes = 0
        while stack and nodes < 500000:
            if time.time() - t0 > max_time:
                break
            nodes += 1
            config, path, det, movers = stack.pop()
            for p in range(n):
                for new_val in range(ms[p]):
                    if new_val == config[p]:
                        continue
                    if movers:
                        last = movers[-1]
                        diff = min(abs(p - last), n - abs(p - last))
                        if diff > 1:
                            continue
                    new_det = dict(det)
                    consistent = True
                    L = config[(p - 1) % n]
                    S = config[p]
                    R = config[(p + 1) % n]
                    key_m = (p, L, S, R)
                    if key_m in new_det:
                        if new_det[key_m] != new_val:
                            consistent = False
                    else:
                        new_det[key_m] = new_val
                    if consistent:
                        for i in range(n):
                            if i == p:
                                continue
                            Li = config[(i - 1) % n]
                            Si = config[i]
                            Ri = config[(i + 1) % n]
                            key_i = (i, Li, Si, Ri)
                            if key_i in new_det:
                                if new_det[key_i] != Si:
                                    consistent = False
                                    break
                            else:
                                new_det[key_i] = Si
                    if not consistent:
                        continue
                    new_config = list(config)
                    new_config[p] = new_val
                    new_config = tuple(new_config)
                    if new_config == start and len(path) >= n:
                        me_ok = True
                        for idx in range(len(path)):
                            c = path[idx]
                            priv = []
                            for i in range(n):
                                Li = c[(i - 1) % n]
                                Si = c[i]
                                Ri = c[(i + 1) % n]
                                ki = (i, Li, Si, Ri)
                                if ki in new_det and new_det[ki] != Si:
                                    priv.append(i)
                            if len(priv) != 1:
                                me_ok = False
                                break
                        if me_ok:
                            cycle_tup = tuple(path)
                            if cycle_tup not in [tuple(c) for c, _, _ in cycles]:
                                cycles.append((path, movers + [p], new_det))
                                if len(cycles) >= max_cycles:
                                    return cycles
                        continue
                    if new_config not in set(path) and len(path) < max_path_len:
                        stack.append((new_config, path + [new_config],
                                      new_det, movers + [p]))
    return cycles


def classify_entries(cycle, movers, det, n):
    mover_entries = set()
    nonmover_entries = set()
    for step in range(len(cycle)):
        p = movers[step]
        c = cycle[step]
        for i in range(n):
            Li = c[(i - 1) % n]
            Si = c[i]
            Ri = c[(i + 1) % n]
            key = (i, Li, Si, Ri)
            if i == p:
                mover_entries.add(key)
            else:
                nonmover_entries.add(key)
    return mover_entries, nonmover_entries


# ============================================================
# PART 1: P1 EDGES ARE TERNARY-INDEPENDENT — count non-good configs
# ============================================================
print("=" * 70)
print("PART 1: P1 edges — ternary-independent forced transitions")
print("=" * 70)
print()

for n, ms in [(5, (2,2,2,3,3)), (6, (2,2,2,3,3,3)), (7, (2,2,2,3,3,3,3))]:
    P = 1
    for m in ms:
        P *= m
    if P > 500:
        # Can't enumerate at n=7, just compute bounds
        ternary_prod = 3 ** (n - 3)
        p1_forced_total = 2 * ternary_prod  # 2 contexts × 2 binary states
        # But only S matching the mover direction
        p1_forced_per_dir = ternary_prod  # all ternary fibers at that binary state
        print(f"n={n}, ms={list(ms)}, P={P}, ternary_prod={ternary_prod}")
        print(f"  P1 UP forces {p1_forced_per_dir} configs (binary (0,0,1,...))")
        print(f"  P1 DOWN forces {p1_forced_per_dir} configs (binary (1,1,0,...))")
        print(f"  Total P1 forced = {2*p1_forced_per_dir} = P/{P//(2*p1_forced_per_dir)}")
        print(f"  Good configs ≤ 3n-2 = {3*n-2} << ternary_prod = {ternary_prod}")
        print(f"  Non-good at P1 UP ≥ {p1_forced_per_dir} - {3*n-2} = {p1_forced_per_dir - (3*n-2)}")
        print()
        continue

    cycles = enumerate_cycles(ms, n, max_cycles=20, max_time=30.0)
    full = [(c, m, d) for c, m, d in cycles if set(m) == set(range(n))]
    if not full:
        continue

    cycle, movers, det = full[0][:3]
    good_set = set(cycle)
    L = len(cycle)
    mover_entries, _ = classify_entries(cycle, movers, det, n)

    # P1 mover entries
    p1_entries = [(key, det[key]) for key in mover_entries if key[0] == 1]
    print(f"n={n}, ms={list(ms)}, P={P}, L={L}")
    print(f"  P1 mover entries: {len(p1_entries)}")
    for key, out in p1_entries:
        _, Lv, Sv, Rv = key
        direction = "UP" if out > Sv else "DOWN"
        # Count non-good configs matching this entry
        match_total = 0
        match_nongood = 0
        for c in iproduct(*[range(m) for m in ms]):
            if c[0] == Lv and c[1] == Sv and c[2] == Rv:
                match_total += 1
                if c not in good_set:
                    match_nongood += 1
        print(f"    ({Lv},{Sv},{Rv})→{out} [{direction}]: "
              f"{match_total} total, {match_nongood} non-good "
              f"({100*match_nongood/match_total:.0f}%)")

    # After P1 fires, how many results are non-good?
    print(f"  After P1 fires:")
    for key, out in p1_entries:
        _, Lv, Sv, Rv = key
        direction = "UP" if out > Sv else "DOWN"
        results_nongood = 0
        results_good = 0
        for c in iproduct(*[range(m) for m in ms]):
            if c[0] == Lv and c[1] == Sv and c[2] == Rv and c not in good_set:
                nc = list(c)
                nc[1] = out
                nc = tuple(nc)
                if nc not in good_set:
                    results_nongood += 1
                else:
                    results_good += 1
        total = results_nongood + results_good
        print(f"    {direction}: {results_nongood}/{total} stay non-good "
              f"({100*results_nongood/total:.0f}%)")
    print()


# ============================================================
# PART 2: AFTER P1 FIRES — what forced transitions are available?
# ============================================================
print("=" * 70)
print("PART 2: After P1 fires — which procs have forced transitions?")
print("=" * 70)
print()

for n, ms in [(5, (2,2,2,3,3)), (6, (2,2,2,3,3,3))]:
    P = 1
    for m in ms:
        P *= m

    cycles = enumerate_cycles(ms, n, max_cycles=10, max_time=30.0)
    full = [(c, m, d) for c, m, d in cycles if set(m) == set(range(n))]
    if not full:
        continue

    cycle, movers, det = full[0][:3]
    good_set = set(cycle)
    L = len(cycle)
    mover_entries, _ = classify_entries(cycle, movers, det, n)

    print(f"n={n}, ms={list(ms)}, P={P}, L={L}")

    # After P1 UP: config (0,1,1,t) — what forced transitions?
    p1_up_key = None
    for key in mover_entries:
        if key[0] == 1 and det[key] > key[2]:  # UP
            p1_up_key = key
            break

    if p1_up_key is None:
        continue

    _, Lv, Sv, Rv = p1_up_key
    out = det[p1_up_key]

    # Result configs: (Lv, out, Rv, t3, ..., t_{n-1})
    result_configs = []
    for c in iproduct(*[range(m) for m in ms]):
        if c[0] == Lv and c[1] == out and c[2] == Rv and c not in good_set:
            result_configs.append(c)

    print(f"\n  After P1 UP at ({Lv},{Sv},{Rv})→{out}:")
    print(f"  {len(result_configs)} non-good result configs (binary={Lv},{out},{Rv})")

    # For each result config, which procs have forced transitions?
    forced_procs = Counter()
    chain_next_binary = Counter()
    for c in result_configs:
        forced = []
        for p in range(n):
            Lp = c[(p - 1) % n]
            Sp = c[p]
            Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                forced.append(p)
                forced_procs[p] += 1

                # What's the binary state after this proc fires?
                nc = list(c)
                nc[p] = det[key]
                nc = tuple(nc)
                new_bin = (nc[0], nc[1], nc[2])
                chain_next_binary[new_bin] += 1

        if not forced and len(result_configs) < 20:
            ternary = tuple(c[j] for j in range(3, n))
            print(f"    NO forced at {c}: ternary={ternary}")

    print(f"  Forced proc counts: {dict(sorted(forced_procs.items()))}")
    print(f"  Next binary state: {dict(sorted(chain_next_binary.items()))}")

    # The key transition: P1 UP result (0,1,1) → P2 fires → (0,1,0)
    p2_from_p1up = 0
    p0_from_p1up = 0
    ternary_from_p1up = 0
    for c in result_configs:
        # Check P2
        Lp = c[1]  # P1 value
        Sp = c[2]  # P2 value
        Rp = c[3]  # P3 value
        key = (2, Lp, Sp, Rp)
        if key in det and det[key] != Sp:
            p2_from_p1up += 1
            continue
        # Check P0
        Lp = c[(n-1)]  # P_{n-1} value
        Sp = c[0]  # P0 value
        Rp = c[1]  # P1 value
        key = (0, Lp, Sp, Rp)
        if key in det and det[key] != Sp:
            p0_from_p1up += 1
            continue
        # Check ternary procs
        for p in range(3, n):
            Lp = c[(p-1) % n]
            Sp = c[p]
            Rp = c[(p+1) % n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                ternary_from_p1up += 1
                break

    total = p2_from_p1up + p0_from_p1up + ternary_from_p1up
    none = len(result_configs) - total
    print(f"\n  Chain from P1 UP results ({len(result_configs)} configs):")
    print(f"    → P2 fires: {p2_from_p1up} ({100*p2_from_p1up/len(result_configs):.0f}%)")
    print(f"    → P0 fires: {p0_from_p1up} ({100*p0_from_p1up/len(result_configs):.0f}%)")
    print(f"    → Ternary fires: {ternary_from_p1up} ({100*ternary_from_p1up/len(result_configs):.0f}%)")
    print(f"    → None: {none} ({100*none/len(result_configs):.0f}%)")
    print()


# ============================================================
# PART 3: MINIMUM OUT-DEGREE IN FORCED GRAPH
# ============================================================
print("=" * 70)
print("PART 3: Minimum out-degree in forced non-good graph")
print("=" * 70)
print()

for n, ms in [(5, (2,2,2,3,3)), (6, (2,2,2,3,3,3))]:
    P = 1
    for m in ms:
        P *= m

    cycles = enumerate_cycles(ms, n, max_cycles=10, max_time=30.0)
    full = [(c, m, d) for c, m, d in cycles if set(m) == set(range(n))]
    if not full:
        continue

    cycle, movers, det = full[0][:3]
    good_set = set(cycle)
    L = len(cycle)
    mover_entries, _ = classify_entries(cycle, movers, det, n)

    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    # Compute out-degree for each non-good config
    out_degrees = []
    out_to_nongood = []
    for c in non_good:
        out_deg = 0
        out_ng = 0
        for p in range(n):
            Lp = c[(p - 1) % n]
            Sp = c[p]
            Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                nc = list(c)
                nc[p] = det[key]
                nc = tuple(nc)
                out_deg += 1
                if nc in non_good_set:
                    out_ng += 1
        out_degrees.append(out_deg)
        out_to_nongood.append(out_ng)

    out_dist = Counter(out_degrees)
    ong_dist = Counter(out_to_nongood)

    print(f"n={n}, ms={list(ms)}, P={P}, L={L}, non-good={len(non_good)}")
    print(f"  Out-degree distribution (all forced edges):")
    for d in sorted(out_dist.keys()):
        print(f"    degree {d}: {out_dist[d]} configs "
              f"({100*out_dist[d]/len(non_good):.0f}%)")

    print(f"  Out-degree to non-good (edges staying in non-good set):")
    for d in sorted(ong_dist.keys()):
        print(f"    degree {d}: {ong_dist[d]} configs "
              f"({100*ong_dist[d]/len(non_good):.0f}%)")

    # Configs with out-degree 0 to non-good: these are "sinks"
    sinks = [non_good[i] for i in range(len(non_good)) if out_to_nongood[i] == 0]
    print(f"\n  Sinks (out-degree 0 to non-good): {len(sinks)}")
    if sinks:
        # Check: do these sinks have ANY forced transitions (possibly to good)?
        for c in sinks[:5]:
            any_forced = False
            for p in range(n):
                Lp = c[(p - 1) % n]
                Sp = c[p]
                Rp = c[(p + 1) % n]
                key = (p, Lp, Sp, Rp)
                if key in det and det[key] != Sp:
                    nc = list(c)
                    nc[p] = det[key]
                    nc = tuple(nc)
                    dest = "GOOD" if nc in good_set else "NON-GOOD"
                    print(f"    {c}: P{p} fires → {nc} ({dest})")
                    any_forced = True
            if not any_forced:
                print(f"    {c}: NO forced transitions (all free/nonmover)")
    print()


# ============================================================
# PART 4: ADVERSARY STRATEGY — can adversary stay in non-good?
# ============================================================
print("=" * 70)
print("PART 4: Adversary strategy — longest non-good chain")
print("=" * 70)
print()

for n, ms in [(5, (2,2,2,3,3)), (6, (2,2,2,3,3,3))]:
    P = 1
    for m in ms:
        P *= m

    cycles = enumerate_cycles(ms, n, max_cycles=5, max_time=30.0)
    full = [(c, m, d) for c, m, d in cycles if set(m) == set(range(n))]
    if not full:
        continue

    for ci, (cycle, movers, det) in enumerate(full[:2]):
        good_set = set(cycle)
        L = len(cycle)

        all_configs = list(iproduct(*[range(m) for m in ms]))
        non_good = [c for c in all_configs if c not in good_set]
        non_good_set = set(non_good)

        # Build adjacency: non-good → non-good transitions
        adj = defaultdict(set)
        for c in non_good:
            for p in range(n):
                Lp = c[(p - 1) % n]
                Sp = c[p]
                Rp = c[(p + 1) % n]
                key = (p, Lp, Sp, Rp)
                if key in det and det[key] != Sp:
                    nc = list(c)
                    nc[p] = det[key]
                    nc = tuple(nc)
                    if nc in non_good_set:
                        adj[c].add(nc)

        # Find SCCs
        idx_counter = [0]
        tstack = []
        on_stack = set()
        lowlink = {}
        index_map = {}
        sccs = []
        def sc(v):
            index_map[v] = idx_counter[0]
            lowlink[v] = idx_counter[0]
            idx_counter[0] += 1
            tstack.append(v)
            on_stack.add(v)
            for w in adj.get(v, set()):
                if w not in index_map:
                    sc(w)
                    lowlink[v] = min(lowlink[v], lowlink[w])
                elif w in on_stack:
                    lowlink[v] = min(lowlink[v], index_map[w])
            if lowlink[v] == index_map[v]:
                scc = []
                while True:
                    w = tstack.pop()
                    on_stack.discard(w)
                    scc.append(w)
                    if w == v:
                        break
                if len(scc) > 1:
                    sccs.append(scc)
        sys.setrecursionlimit(10000)
        for v in non_good:
            if v not in index_map:
                sc(v)

        if sccs:
            max_scc = max(len(s) for s in sccs)
            total_scc = sum(len(s) for s in sccs)
            print(f"n={n}, cycle {ci}: L={L}, non-good={len(non_good)}, "
                  f"SCCs={len(sccs)}, max={max_scc}, total={total_scc}")

            # The adversary can stay FOREVER in the SCC
            # Show a shortest cycle within the SCC
            scc0 = sccs[0]
            scc0_set = set(scc0)
            # BFS for shortest cycle from first node
            start = scc0[0]
            from collections import deque
            queue = deque([(start, [start])])
            visited = {start}
            shortest = None
            while queue:
                node, path = queue.popleft()
                for nb in adj.get(node, set()):
                    if nb == start and len(path) > 1:
                        shortest = path + [start]
                        break
                    if nb in scc0_set and nb not in visited:
                        visited.add(nb)
                        queue.append((nb, path + [nb]))
                if shortest:
                    break

            if shortest:
                print(f"  Shortest adversary cycle: length {len(shortest)-1}")
                # Show which procs fire in the cycle
                cycle_procs = []
                for i in range(len(shortest) - 1):
                    c = shortest[i]
                    nc = shortest[i + 1]
                    for p in range(n):
                        if c[p] != nc[p]:
                            cycle_procs.append(p)
                            break
                print(f"  Cycle procs: {cycle_procs}")
                for i in range(min(len(shortest) - 1, 8)):
                    c = shortest[i]
                    nc = shortest[i + 1]
                    p = cycle_procs[i]
                    b = (c[0], c[1], c[2])
                    nb = (nc[0], nc[1], nc[2])
                    print(f"    {c} →P{p}→ {nc}  (binary: {b}→{nb})")
        else:
            print(f"n={n}, cycle {ci}: NO SCC (unexpected)")
    print()


# ============================================================
# PART 5: THE KEY LEMMA — P1 forces enough non-good edges
# ============================================================
print("=" * 70)
print("PART 5: KEY LEMMA — P1 forces enough non-good-to-non-good edges")
print("=" * 70)
print()

print("""
ANALYTICAL ARGUMENT:

P1 fires at anti-diagonal contexts (0,1) and (1,0).

P1 UP: at config (0,0,1,t) → (0,1,1,t). Both are at the SAME ternary fiber t.

The number of ternary fibers is T = 3^(n-3).
Good configs at binary (0,0,1): at most G1 ≤ L/8 (fraction of cycle at this binary state).
Good configs at binary (0,1,1): at most G2 ≤ L/8.

P1 UP creates T-G1 non-good → something transitions.
Of these, T-G2 results are non-good.
Edges staying non-good: T - G1 - G2 + (overlap) ≥ T - 2·(L/8) = T - L/4.

For L < P/2 = 4T:
  T - L/4 > T - T = 0. So at least 1 non-good → non-good P1 edge exists!

More precisely: for L ≤ 3n-2 (empirical maximum):
  T - L/4 ≥ 3^(n-3) - (3n-2)/4
  At n=5: 9 - 13/4 ≈ 5.75 → at least 5 non-good→non-good P1 UP edges.
  At n=6: 27 - 16/4 = 23 → at least 23 non-good→non-good P1 UP edges.

Similarly for P1 DOWN.

So P1 creates ≥ 2·(T - L/4) non-good→non-good edges.
These edges map configs with P1=0 to configs with P1=1 (UP) and vice versa (DOWN).
Each edge preserves the ternary fiber.

For the CYCLE closure: we need the P1 UP results to eventually reach
configs where P1 DOWN fires, and vice versa. The binary path is:
  (0,0,1) →P1→ (0,1,1) →??→ ... →??→ (1,1,0) →P1→ (1,0,0) →??→ ... →??→ (0,0,1)

The "??" transitions involve P0, P2, and ternary processors.
""")

# Verify the counting argument
for n, ms in [(5, (2,2,2,3,3)), (6, (2,2,2,3,3,3))]:
    P = 1
    for m in ms:
        P *= m
    T = 3 ** (n - 3)

    cycles = enumerate_cycles(ms, n, max_cycles=10, max_time=30.0)
    full = [(c, m, d) for c, m, d in cycles if set(m) == set(range(n))]
    if not full:
        continue

    cycle, movers, det = full[0][:3]
    good_set = set(cycle)
    L = len(cycle)

    # Count good configs per binary state
    good_by_bin = Counter()
    for c in cycle:
        b = (c[0], c[1], c[2])
        good_by_bin[b] += 1

    print(f"n={n}, ms={list(ms)}, P={P}, L={L}, T={T}")
    print(f"  Good configs per binary state:")
    for b in sorted(good_by_bin.keys()):
        print(f"    {b}: {good_by_bin[b]}/{T} "
              f"({100*good_by_bin[b]/T:.0f}%)")

    # P1 UP: (0,0,1) → (0,1,1)
    g1 = good_by_bin.get((0, 0, 1), 0)
    g2 = good_by_bin.get((0, 1, 1), 0)
    non_good_up = T - g1 - g2  # conservative (no overlap possible)
    # Actually: count exactly
    exact_ng_up = 0
    for c in iproduct(*[range(m) for m in ms]):
        if c[0] == 0 and c[1] == 0 and c[2] == 1 and c not in good_set:
            nc = list(c)
            nc[1] = 1
            nc = tuple(nc)
            if nc not in good_set:
                exact_ng_up += 1

    print(f"  P1 UP (0,0,1)→(0,1,1): G1={g1}, G2={g2}, "
          f"bound={T-g1-g2}, exact={exact_ng_up}")

    # P1 DOWN: (1,1,0) → (1,0,0)
    g3 = good_by_bin.get((1, 1, 0), 0)
    g4 = good_by_bin.get((1, 0, 0), 0)
    exact_ng_down = 0
    for c in iproduct(*[range(m) for m in ms]):
        if c[0] == 1 and c[1] == 1 and c[2] == 0 and c not in good_set:
            nc = list(c)
            nc[1] = 0
            nc = tuple(nc)
            if nc not in good_set:
                exact_ng_down += 1

    print(f"  P1 DOWN (1,1,0)→(1,0,0): G3={g3}, G4={g4}, "
          f"bound={T-g3-g4}, exact={exact_ng_down}")
    print()


# ============================================================
# SUMMARY
# ============================================================
print("=" * 70)
print("SCC LIFTING PROOF STATUS")
print("=" * 70)
print("""
WHAT'S PROVED:
1. Anti-Diagonal P1 Lemma (ANALYTICAL): P1 fires at (0,1) and (1,0)
2. P1 creates ternary-independent edges in forced graph
3. Each P1 edge maps T-O(L) non-good configs to non-good configs
   (where T = 3^(n-3), L = cycle length)

WHAT'S NEEDED:
4. The forced graph (P1 + P0 + P2 + ternary edges) has a directed
   cycle among non-good configs.

THE GAP:
P1 alone creates 2-cycles between (0,0,1,t) and (0,1,1,t), AND between
(1,1,0,t) and (1,0,0,t), BUT not between these two pairs. P1 does NOT
connect the UP half ((0,0,1)↔(0,1,1)) to the DOWN half ((1,1,0)↔(1,0,0)).
The connection requires P0 or P2 or ternary transitions.

PROOF APPROACH for closing the gap:
The adversary at (0,1,1,t) has forced transition options:
  - P2 fires (ternary-dependent): goes to (0,1,0,t) — 6-cycle continues
  - P0 fires (ternary-dependent): goes to (1,1,1,t) — exits non-uniform
  - Ternary fires: changes fiber, stays at binary (0,1,1)
  - None: adversary chooses P1 edge (goes to good? impossible —
    P1 just fired UP, config is (0,1,1,t), P1 context is (0,1)
    which is a NONMOVER entry. So P1 doesn't fire again.)

The adversary MUST choose from P0/P2/ternary. At least one fires because
the good cycle visits all processors, determining entries at all contexts.
The chain continues through P0→P2→ternary transitions until reaching
a binary state where P1 fires again (either UP or DOWN at anti-diagonal).

The cycle closes because the binary subspace has only 8 states, and
the chain must revisit a binary state. If the ternary fiber at revisit
matches a previous visit, we have a full-space cycle. If not, the
chain continues with a new fiber at the same binary state, but T is
finite, so the chain must eventually revisit a (binary, ternary) pair.

This is a PIGEONHOLE argument on the finite state space.
""")
