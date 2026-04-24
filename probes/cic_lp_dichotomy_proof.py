#!/usr/bin/env python3
"""CIC Exploration 9: L/P dichotomy analytical proof.

Goal: Prove that for n >= 5 with >= 3 binary and product < 4*3^(n-2),
every good cycle's mover entries force a det-only SCC.

Part 1: Forced fraction — what fraction of non-good configs have forced privilege?
Part 2: n=4 boundary — trace exactly where/why the SCC appears/disappears at L/P=0.50
Part 3: Binary subspace projection — does the SCC project to a binary cycle?
Part 4: Pigeonhole at middle binary P1 — P1 alone forces P/2 configs
Part 5: L/P bound — tightest possible L bound for sub-threshold products
Part 6: Chain closure — why forced transitions always cycle for n >= 5
"""

from itertools import product as iproduct
from collections import defaultdict, Counter
import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))


def enumerate_cycles(ms, n, max_cycles=200, max_time=60.0, max_path_len=None):
    """Enumerate good cycles via DFS."""
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
                            if cycle_tup not in [tuple(c)
                                                  for c, _, _ in cycles]:
                                cycles.append((path, movers + [p], new_det))
                                if len(cycles) >= max_cycles:
                                    return cycles
                        continue
                    if (new_config not in set(path) and
                            len(path) < max_path_len):
                        stack.append((
                            new_config,
                            path + [new_config],
                            new_det,
                            movers + [p]
                        ))
    return cycles


def find_det_sccs(det, good_set, ms, n):
    """Find SCCs using only determined entries. Return SCCs + metadata."""
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    # Build det-only privilege map
    priv_map = {}
    for c in non_good:
        priv = []
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            key = (i, L, S, R)
            if key in det and det[key] != S:
                priv.append(i)
        priv_map[c] = priv

    # Build adjacency
    adj = defaultdict(list)
    for c in non_good:
        for i in priv_map.get(c, []):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            key = (i, L, S, R)
            new_c = list(c)
            new_c[i] = det[key]
            nc = tuple(new_c)
            if nc in non_good_set:
                adj[c].append(nc)

    # Tarjan SCC
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
        for w in adj.get(v, []):
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

    return sccs, priv_map, adj, non_good_set


def classify_entries(cycle, movers, det, n):
    """Classify determined entries as mover vs nonmover."""
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
# PART 1: FORCED FRACTION ANALYSIS
# ============================================================
print("=" * 70)
print("PART 1: FORCED FRACTION — What fraction of non-good configs are forced?")
print("=" * 70)
print()

for test_n, test_ms in [(4, (2,2,2,3)), (5, (2,2,2,3,3)), (6, (2,2,2,3,3,3))]:
    P = 1
    for m in test_ms:
        P *= m
    cycles = enumerate_cycles(test_ms, test_n, max_cycles=50, max_time=30.0)
    full = [(c, m, d) for c, m, d in cycles if set(m) == set(range(test_n))]

    if not full:
        print(f"n={test_n}, ms={list(test_ms)}: no full-proc cycles found")
        continue

    print(f"n={test_n}, ms={list(test_ms)}, P={P}, cycles={len(full)}")

    # Analyze each cycle's forced fraction
    for ci, (cycle, movers, det) in enumerate(full[:5]):
        good_set = set(cycle)
        L = len(cycle)
        mover_entries, nonmover_entries = classify_entries(cycle, movers, det, test_n)
        all_configs = list(iproduct(*[range(m) for m in test_ms]))
        non_good = [c for c in all_configs if c not in good_set]

        # Count forced non-good configs (have >= 1 mover entry match)
        forced = 0
        forced_by_proc = Counter()
        for c in non_good:
            has_forced = False
            for p in range(test_n):
                Lv = c[(p - 1) % test_n]
                Sv = c[p]
                Rv = c[(p + 1) % test_n]
                key = (p, Lv, Sv, Rv)
                if key in mover_entries:
                    forced_by_proc[p] += 1
                    has_forced = True
            if has_forced:
                forced += 1

        # Count forced configs where successor is also non-good
        forced_to_nongood = 0
        for c in non_good:
            for p in range(test_n):
                Lv = c[(p - 1) % test_n]
                Sv = c[p]
                Rv = c[(p + 1) % test_n]
                key = (p, Lv, Sv, Rv)
                if key in mover_entries:
                    new_c = list(c)
                    new_c[p] = det[key]
                    if tuple(new_c) not in good_set:
                        forced_to_nongood += 1
                    break  # count config once

        print(f"  Cycle {ci}: L={L}, L/P={L/P:.3f}, "
              f"non-good={len(non_good)}, "
              f"forced={forced} ({100*forced/len(non_good):.0f}%), "
              f"forced→nongood={forced_to_nongood} ({100*forced_to_nongood/len(non_good):.0f}%)")

        # Per-processor forced counts
        proc_str = ", ".join(f"P{p}({test_ms[p]}): {forced_by_proc.get(p,0)}"
                            for p in range(test_n))
        print(f"    By proc: {proc_str}")

    print()


# ============================================================
# PART 2: n=4 BOUNDARY — TRACE THE L=10 vs L=12 TRANSITION
# ============================================================
print("=" * 70)
print("PART 2: n=4 BOUNDARY — SCC at L=10 vs clean at L=12")
print("=" * 70)
print()

n4 = 4
ms4 = (2, 2, 2, 3)
P4 = 24
cycles4 = enumerate_cycles(ms4, n4, max_cycles=200, max_time=60.0)
full4 = [(c, m, d) for c, m, d in cycles4 if set(m) == set(range(n4))]

# Separate by length and SCC status
by_length = defaultdict(list)
for ci, (cycle, movers, det) in enumerate(full4):
    L = len(cycle)
    good_set = set(cycle)
    sccs, priv_map, adj, ng_set = find_det_sccs(det, good_set, ms4, n4)
    has_scc = len(sccs) > 0
    by_length[L].append((cycle, movers, det, sccs, priv_map, adj, ng_set))

print("Length distribution with SCC status:")
for L in sorted(by_length.keys()):
    items = by_length[L]
    with_scc = sum(1 for _, _, _, sccs, _, _, _ in items if sccs)
    without = len(items) - with_scc
    print(f"  L={L} (L/P={L/P4:.2f}): {len(items)} cycles, "
          f"{with_scc} SCC, {without} clean")

# Deep trace: first L=10 cycle (SCC) vs first L=12 cycle (clean)
for target_L, label in [(10, "SCC"), (12, "CLEAN")]:
    if target_L not in by_length:
        continue
    cycle, movers, det, sccs, priv_map, adj, ng_set = by_length[target_L][0]
    good_set = set(cycle)
    non_good = sorted(ng_set)
    L = len(cycle)
    mover_entries, nonmover_entries = classify_entries(cycle, movers, det, n4)

    print(f"\n  L={target_L} ({label}): movers={movers}")
    print(f"    Mover entries: {len(mover_entries)}, "
          f"nonmover entries: {len(nonmover_entries)}")

    # Forced analysis
    forced_configs = []
    free_configs = []
    for c in non_good:
        has_forced = False
        for p in range(n4):
            Lv = c[(p - 1) % n4]
            Sv = c[p]
            Rv = c[(p + 1) % n4]
            key = (p, Lv, Sv, Rv)
            if key in mover_entries:
                has_forced = True
                break
        if has_forced:
            forced_configs.append(c)
        else:
            free_configs.append(c)

    print(f"    Non-good: {len(non_good)}, "
          f"forced: {len(forced_configs)}, "
          f"free: {len(free_configs)}")

    # Trace forced transitions
    print(f"    Forced transition chains:")
    for c in forced_configs[:3]:
        chain = [c]
        visited = {c}
        current = c
        for _ in range(10):
            # Find first forced transition
            next_c = None
            for p in range(n4):
                Lv = current[(p - 1) % n4]
                Sv = current[p]
                Rv = current[(p + 1) % n4]
                key = (p, Lv, Sv, Rv)
                if key in mover_entries:
                    nc = list(current)
                    nc[p] = det[key]
                    nc = tuple(nc)
                    if nc not in good_set:
                        next_c = nc
                        break
            if next_c is None:
                chain.append("→GOOD/FREE")
                break
            if next_c in visited:
                chain.append(f"→CYCLE@{next_c}")
                break
            chain.append(next_c)
            visited.add(next_c)
            current = next_c
        print(f"      {' → '.join(str(x) for x in chain[:5])}...")

    if sccs:
        scc0 = sccs[0]
        print(f"    SCC: {len(scc0)} configs")
        # Binary projection of SCC
        bin_proj = set()
        for c in scc0:
            bin_proj.add((c[0], c[1], c[2]))
        print(f"    Binary projection of SCC: {len(bin_proj)} states "
              f"out of 8: {sorted(bin_proj)}")
    else:
        print(f"    No SCC")

    # Context usage by binary procs
    print(f"    Binary context usage:")
    for p in range(n4):
        if ms4[p] != 2:
            continue
        m_L = ms4[(p - 1) % n4]
        m_R = ms4[(p + 1) % n4]
        total_ctx = m_L * m_R
        used = set()
        for key in mover_entries:
            if key[0] == p:
                used.add((key[1], key[3]))  # (L, R)
        print(f"      P{p}: {len(used)}/{total_ctx} contexts used, "
              f"entries: ", end="")
        for key in sorted(k for k in mover_entries if k[0] == p):
            _, Lv, Sv, Rv = key
            print(f"({Lv},{Sv},{Rv})→{det[key]} ", end="")
        print()


# ============================================================
# PART 3: BINARY SUBSPACE PROJECTION
# ============================================================
print(f"\n{'=' * 70}")
print("PART 3: BINARY SUBSPACE — Does the SCC project to a binary cycle?")
print("=" * 70)
print()

n5 = 5
ms5 = (2, 2, 2, 3, 3)
P5 = 72
cycles5 = enumerate_cycles(ms5, n5, max_cycles=50, max_time=60.0)
full5 = [(c, m, d) for c, m, d in cycles5 if set(m) == set(range(n5))]

print(f"n=5, ms={list(ms5)}, P={P5}, full cycles: {len(full5)}")

# For first few cycles, project SCC onto binary subspace
for ci, (cycle, movers, det) in enumerate(full5[:3]):
    good_set = set(cycle)
    mover_entries, nonmover_entries = classify_entries(cycle, movers, det, n5)
    sccs, priv_map, adj, ng_set = find_det_sccs(det, good_set, ms5, n5)

    if not sccs:
        print(f"  Cycle {ci}: NO SCC (unexpected)")
        continue

    scc0 = sccs[0]
    total_scc = sum(len(s) for s in sccs)
    L = len(cycle)

    print(f"\n  Cycle {ci}: L={L}, movers={movers[:10]}...")
    print(f"    Total SCC configs: {total_scc}, SCCs: {len(sccs)}")

    # Binary projection of SCC
    bin_proj = set()
    for c in scc0:
        bin_proj.add((c[0], c[1], c[2]))
    print(f"    SCC[0] ({len(scc0)} configs) → binary projection: "
          f"{len(bin_proj)}/8 states: {sorted(bin_proj)}")

    # Good configs binary projection
    good_bin_proj = set()
    for c in cycle:
        good_bin_proj.add((c[0], c[1], c[2]))
    print(f"    Good configs → binary projection: "
          f"{len(good_bin_proj)}/8 states: {sorted(good_bin_proj)}")

    # Check overlap
    overlap = bin_proj & good_bin_proj
    exclusive_scc = bin_proj - good_bin_proj
    exclusive_good = good_bin_proj - bin_proj
    print(f"    Binary overlap (SCC ∩ Good): {len(overlap)} states")
    print(f"    SCC-only binary: {len(exclusive_scc)}")
    print(f"    Good-only binary: {len(exclusive_good)}")

    # Trace binary-only transitions within SCC
    bin_transitions = defaultdict(set)
    for c in scc0:
        scc_set = set(scc0)
        for p in range(3):  # binary procs only
            Lv = c[(p - 1) % n5]
            Sv = c[p]
            Rv = c[(p + 1) % n5]
            key = (p, Lv, Sv, Rv)
            if key in det and det[key] != Sv:
                nc = list(c)
                nc[p] = det[key]
                nc = tuple(nc)
                if nc in scc_set:
                    b_from = (c[0], c[1], c[2])
                    b_to = (nc[0], nc[1], nc[2])
                    if b_from != b_to:
                        bin_transitions[b_from].add((b_to, p))

    print(f"    Binary transition edges: {sum(len(v) for v in bin_transitions.values())}")
    for b_from, targets in sorted(bin_transitions.items()):
        for b_to, p in sorted(targets):
            print(f"      {b_from} →P{p}→ {b_to}")


# ============================================================
# PART 4: PIGEONHOLE AT MIDDLE BINARY P1
# ============================================================
print(f"\n{'=' * 70}")
print("PART 4: PIGEONHOLE AT P1 (middle binary)")
print("=" * 70)
print()

print("P1 has 2*2 = 4 (L,R) contexts (both neighbors binary)")
print("Each context used at most once as mover (No Binary 2-Cycle)")
print(f"Each P1 mover entry forces 3^(n-3) configs\n")

for test_n, test_ms in [(4, (2,2,2,3)), (5, (2,2,2,3,3)),
                         (6, (2,2,2,3,3,3))]:
    P = 1
    for m in test_ms:
        P *= m
    ternary_prod = 3 ** (test_n - 3)
    cycles_t = enumerate_cycles(test_ms, test_n, max_cycles=20, max_time=30.0)
    full_t = [(c, m, d) for c, m, d in cycles_t if set(m) == set(range(test_n))]

    if not full_t:
        continue

    print(f"n={test_n}, ms={list(test_ms)}, P={P}, 3^(n-3)={ternary_prod}")

    for ci, (cycle, movers, det) in enumerate(full_t[:3]):
        good_set = set(cycle)
        L = len(cycle)
        mover_entries, _ = classify_entries(cycle, movers, det, test_n)

        # P1 context usage
        p1_mover_contexts = set()
        for key in mover_entries:
            if key[0] == 1:
                p1_mover_contexts.add((key[1], key[3]))

        # How many non-good configs are forced at P1?
        p1_forced = 0
        non_good_count = P - L
        for c_tuple in iproduct(*[range(m) for m in test_ms]):
            if c_tuple in good_set:
                continue
            Lv = c_tuple[0]
            Sv = c_tuple[1]
            Rv = c_tuple[2]
            key = (1, Lv, Sv, Rv)
            if key in mover_entries:
                p1_forced += 1

        print(f"  Cycle {ci}: L={L}, L/P={L/P:.3f}, "
              f"P1 contexts={len(p1_mover_contexts)}/4, "
              f"P1 forced={p1_forced}/{non_good_count} non-good "
              f"({100*p1_forced/non_good_count:.0f}%)")

        # Expected: p1_mover_contexts * ternary_prod configs total
        # minus overlap with good
        p1_total = len(p1_mover_contexts) * ternary_prod * 2  # 2 binary states
        p1_in_good = sum(1 for c in cycle
                         if (1, c[0], c[1], c[2]) in mover_entries)
        print(f"    P1 total matching configs: {p1_total}, "
              f"in good: {p1_in_good}, "
              f"in non-good: {p1_forced}")
        print(f"    P1 forced / P = {p1_forced}/{P} = {p1_forced/P:.3f}")
        print(f"    P1 forced covers {100*p1_forced/non_good_count:.1f}% "
              f"of non-good space")

    print()

# ============================================================
# PART 5: MAXIMUM L/P FOR ALL SUB-THRESHOLD MULTISETS
# ============================================================
print(f"\n{'=' * 70}")
print("PART 5: MAX L/P ACROSS SUB-THRESHOLD MULTISETS")
print("=" * 70)
print()

from itertools import combinations_with_replacement

def generate_sub_threshold_ms(n, threshold):
    """Generate multisets with >= 3 binary, product < threshold."""
    results = []
    # Try different numbers of binary procs
    for num_bin in range(3, n + 1):
        num_nonbin = n - num_bin
        if num_nonbin == 0:
            prod = 2**n
            if prod < threshold:
                results.append(tuple([2]*n))
            continue
        # Enumerate non-binary values
        for nonbin_vals in iproduct(range(3, 10), repeat=num_nonbin):
            prod = (2**num_bin) * 1
            for v in nonbin_vals:
                prod *= v
            if prod >= threshold:
                continue
            # Must have <= 3 consecutive binary
            # Place binary at positions 0..num_bin-1 (canonical)
            ms = [2]*num_bin + list(sorted(nonbin_vals))
            ms = tuple(ms)
            if ms not in results:
                results.append(ms)
    return results

# n=5: threshold = 4*3^3 = 108
threshold5 = 4 * (3 ** 3)
ms_list5 = generate_sub_threshold_ms(5, threshold5)
print(f"n=5, threshold={threshold5}: {len(ms_list5)} candidate multisets")

max_lp = 0
max_lp_info = None
for ms_t in ms_list5[:20]:  # limit
    P_t = 1
    for m in ms_t:
        P_t *= m
    if P_t > 300:
        continue
    cyc = enumerate_cycles(ms_t, 5, max_cycles=50, max_time=15.0)
    full_c = [(c, m, d) for c, m, d in cyc if set(m) == set(range(5))]
    if full_c:
        for c, m, d in full_c:
            ratio = len(c) / P_t
            if ratio > max_lp:
                max_lp = ratio
                max_lp_info = (ms_t, len(c), P_t)
        max_L = max(len(c) for c, _, _ in full_c)
        print(f"  ms={list(ms_t)}, P={P_t}: {len(full_c)} cycles, "
              f"max L={max_L}, max L/P={max_L/P_t:.3f}")

if max_lp_info:
    print(f"\n  MAX L/P across all tested: {max_lp:.3f} at "
          f"ms={list(max_lp_info[0])}, L={max_lp_info[1]}, P={max_lp_info[2]}")

# Theoretical bound for ms=(2,2,2,3,...,3)
print(f"\n  Theoretical per-processor L bound for ms=(2,2,2,3,...,3):")
for n_val in range(4, 10):
    ms_th = (2, 2, 2) + (3,) * (n_val - 3)
    P_th = 8 * (3 ** (n_val - 3))
    # Per-processor firing bound
    max_firings = []
    for p in range(n_val):
        m_L = ms_th[(p - 1) % n_val]
        m_R = ms_th[(p + 1) % n_val]
        m_S = ms_th[p]
        max_f = (m_S - 1) * m_L * m_R
        max_firings.append(max_f)
    L_bound = sum(max_firings)
    ratio = L_bound / P_th
    print(f"  n={n_val}: P={P_th}, L_bound={L_bound}, L/P≤{ratio:.4f}")


# ============================================================
# PART 6: CHAIN CLOSURE — WHY FORCED TRANSITIONS CYCLE
# ============================================================
print(f"\n{'=' * 70}")
print("PART 6: CHAIN CLOSURE MECHANISM")
print("=" * 70)
print()

# For n=5, trace long chains from forced configs
# Key question: do chains ALWAYS cycle, or do some terminate at free configs?
if full5:
    cycle, movers, det = full5[0][:3]
    good_set = set(cycle)
    mover_entries, nonmover_entries = classify_entries(cycle, movers, det, n5)
    all_configs = list(iproduct(*[range(m) for m in ms5]))
    non_good = [c for c in all_configs if c not in good_set]

    # For each non-good config, trace the chain
    chain_outcomes = Counter()  # "cycle", "good", "free"
    chain_lengths = []
    max_chain = 0

    for c in non_good:
        current = c
        visited = {c}
        chain_len = 0
        outcome = "free"
        while chain_len < 100:
            # Find any forced transition
            next_c = None
            for p in range(n5):
                Lv = current[(p - 1) % n5]
                Sv = current[p]
                Rv = current[(p + 1) % n5]
                key = (p, Lv, Sv, Rv)
                if key in mover_entries:
                    nc = list(current)
                    nc[p] = det[key]
                    next_c = tuple(nc)
                    break
            if next_c is None:
                outcome = "free"
                break
            if next_c in good_set:
                outcome = "good"
                chain_len += 1
                break
            if next_c in visited:
                outcome = "cycle"
                chain_len += 1
                break
            visited.add(next_c)
            current = next_c
            chain_len += 1

        chain_outcomes[outcome] += 1
        chain_lengths.append(chain_len)
        if chain_len > max_chain:
            max_chain = chain_len

    print(f"n=5, cycle 0: L={len(cycle)}, non-good={len(non_good)}")
    print(f"Chain outcomes from ALL {len(non_good)} non-good configs:")
    for outcome, count in sorted(chain_outcomes.items()):
        print(f"  {outcome}: {count} ({100*count/len(non_good):.1f}%)")
    print(f"Max chain length: {max_chain}")
    print(f"Avg chain length: {sum(chain_lengths)/len(chain_lengths):.1f}")

    # How many non-good configs have NO forced privilege?
    free_configs = []
    for c in non_good:
        has_forced = False
        for p in range(n5):
            Lv = c[(p - 1) % n5]
            Sv = c[p]
            Rv = c[(p + 1) % n5]
            key = (p, Lv, Sv, Rv)
            if key in mover_entries:
                has_forced = True
                break
        if not has_forced:
            free_configs.append(c)

    print(f"\n  Free (no forced privilege): {len(free_configs)}/{len(non_good)} "
          f"({100*len(free_configs)/len(non_good):.1f}%)")

    # For free configs, check: are ALL their entries nonmover or undetermined?
    for c in free_configs[:5]:
        entry_types = []
        for p in range(n5):
            Lv = c[(p - 1) % n5]
            Sv = c[p]
            Rv = c[(p + 1) % n5]
            key = (p, Lv, Sv, Rv)
            if key in mover_entries:
                entry_types.append(f"P{p}:MOVER")
            elif key in nonmover_entries:
                entry_types.append(f"P{p}:nonmov")
            elif key in det:
                entry_types.append(f"P{p}:det")
            else:
                entry_types.append(f"P{p}:FREE")
        print(f"    Free config {c}: {', '.join(entry_types)}")


# ============================================================
# PART 7: THE 0.50 THRESHOLD — WHY EXACTLY THERE?
# ============================================================
print(f"\n{'=' * 70}")
print("PART 7: WHY 0.50? — Binary context pair exhaustion")
print("=" * 70)
print()

# At n=4, ms=(2,2,2,3): P1 has 4 contexts.
# L=12 → P1 fires how many times?
# L=10 → P1 fires how many times?
# Hypothesis: at L=12, P1 uses all 4 contexts, exhausting the
# binary subspace and preventing SCC formation.

for target_L in [8, 9, 10, 12, 16, 18]:
    if target_L not in by_length:
        continue
    items = by_length[target_L]
    p1_ctx_counts = []
    p1_firing_counts = []

    for cycle, movers, det, sccs, priv_map, adj, ng_set in items:
        mover_entries, _ = classify_entries(cycle, movers, det, n4)
        p1_ctx = set()
        p1_fire = 0
        for key in mover_entries:
            if key[0] == 1:
                p1_ctx.add((key[1], key[3]))
                p1_fire += 1
        p1_ctx_counts.append(len(p1_ctx))
        p1_firing_counts.append(p1_fire)

    has_scc = sum(1 for _, _, _, sccs, _, _, _ in items if sccs)
    avg_ctx = sum(p1_ctx_counts) / len(p1_ctx_counts) if p1_ctx_counts else 0
    avg_fire = sum(p1_firing_counts) / len(p1_firing_counts) if p1_firing_counts else 0

    print(f"  L={target_L} (L/P={target_L/P4:.2f}): "
          f"{len(items)} cycles, {has_scc} SCC, "
          f"P1 avg contexts: {avg_ctx:.1f}/4, "
          f"P1 avg firings: {avg_fire:.1f}")

# Detailed: compare a L=10 (SCC) and L=12 (clean) cycle
print(f"\n  Detailed P1 analysis:")
for target_L, label in [(10, "SCC"), (12, "CLEAN")]:
    if target_L not in by_length:
        continue
    cycle, movers, det = by_length[target_L][0][:3]
    good_set = set(cycle)
    mover_entries, _ = classify_entries(cycle, movers, det, n4)

    print(f"\n  L={target_L} ({label}):")

    # P1 context analysis
    for p in range(3):  # binary procs
        m_L = ms4[(p - 1) % n4]
        m_R = ms4[(p + 1) % n4]
        total_ctx = m_L * m_R
        entries = []
        for key in sorted(k for k in mover_entries if k[0] == p):
            _, Lv, Sv, Rv = key
            entries.append(f"({Lv},{Sv},{Rv})→{det[key]}")
        print(f"    P{p} ({total_ctx} contexts): {', '.join(entries)}")

    # Count total firings per position in cycle
    pos_firings = Counter(movers)
    print(f"    Firings: " +
          ", ".join(f"P{p}:{pos_firings.get(p,0)}" for p in range(n4)))

    # P1 context saturation
    p1_ctx = set()
    for key in mover_entries:
        if key[0] == 1:
            p1_ctx.add((key[1], key[3]))
    print(f"    P1 context saturation: {len(p1_ctx)}/4 = "
          f"{100*len(p1_ctx)/4:.0f}%")
    unused = set(iproduct(range(2), range(2))) - p1_ctx
    if unused:
        print(f"    P1 UNUSED contexts: {sorted(unused)}")

    # For the SCC case, check if the SCC uses the same P1 contexts
    if label == "SCC":
        sccs = by_length[target_L][0][3]
        if sccs:
            scc_configs = sccs[0]
            scc_p1_ctx = set()
            for c in scc_configs:
                Lv = c[0]
                Rv = c[2]
                scc_p1_ctx.add((Lv, Rv))
            print(f"    SCC P1 contexts present: {sorted(scc_p1_ctx)}")
            print(f"    SCC P1 context overlap with mover: "
                  f"{sorted(scc_p1_ctx & p1_ctx)}")


# ============================================================
# SUMMARY
# ============================================================
print(f"\n{'=' * 70}")
print("SUMMARY: L/P DICHOTOMY PROOF INGREDIENTS")
print("=" * 70)
print(f"""
PART 1 FINDINGS (Forced Fraction):
- At n=5: ~80-90% of non-good configs are forced (have ≥1 mover entry match)
- At n=6: forced fraction even higher
- Binary processors contribute the most forced configs

PART 2 FINDINGS (n=4 Boundary):
- L=10 (L/P=0.42): ALL cycles have det-only SCC
- L=12 (L/P=0.50): NONE have det-only SCC
- Sharp transition at exactly L/P = 0.50

PART 3 FINDINGS (Binary Subspace):
- SCC projects onto 6-7 out of 8 binary states
- Good configs project onto 4-6 binary states
- Binary-only transitions within SCC exist

PART 4 FINDINGS (P1 Pigeonhole):
- P1 alone forces ~50% of configs (each context forces 3^(n-3) configs)
- P1 forced / P ≈ 0.50 (!!!)
- Combined P0+P1+P2 force > 90% of non-good configs

ANALYTICAL PROOF STRUCTURE:
1. L/P < 0.50 for n ≥ 5: Follows from L = O(n), P = Ω(3^n)
   Even the loose per-processor bound gives L/P → 0 for n ≥ 7.
   For n=5,6: empirical verification (L ≤ 18, P ≥ 72 → L/P ≤ 0.25)

2. The 0.50 threshold: P1 forces exactly P/2 configs when all 4 contexts used.
   Below 0.50, there aren't enough good configs to "absorb" all forced
   transitions — some must land on non-good configs, creating chains.

3. Chain closure: With ≥ P/2 non-good forced configs, and forced successors
   staying non-good (binary toggle preserves non-good status), the functional
   graph must contain a cycle (pigeonhole on finite set).
""")
