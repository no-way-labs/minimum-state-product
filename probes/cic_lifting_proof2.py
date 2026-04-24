#!/usr/bin/env python3
"""CIC Exploration 10: SCC lifting proof — iterative sink analysis.

KEY QUESTION: Why does the binary 6-cycle always lift to a full-space SCC?

APPROACH: Iterative sink removal on the forced graph of non-good configs.
If the kernel (after full sink removal) is non-empty, then minimum out-degree >= 1,
so a directed cycle exists by finiteness.

We analyze:
1. Sinks per binary state — where do dead ends concentrate?
2. Iterative removal rounds — how fast does the kernel stabilize?
3. Kernel structure — which binary states and fibers survive?
4. P1 survival — do P1's ternary-independent edges survive in the kernel?
5. Cross-fiber connectivity — how do ternary transitions bridge fibers?
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


def build_forced_graph(ms, n, det, good_set):
    """Build forced transition graph on non-good configs."""
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    adj = defaultdict(list)  # config -> list of (target, processor)
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
                    adj[c].append((nc, p))

    return non_good, non_good_set, adj


def iterative_sink_removal(non_good, adj):
    """Remove sinks iteratively. Return kernel (nodes with out-degree >= 1)."""
    remaining = set(non_good)
    rounds = 0
    removed_per_round = []

    while True:
        sinks = set()
        for c in remaining:
            has_out = False
            for target, _ in adj.get(c, []):
                if target in remaining:
                    has_out = True
                    break
            if not has_out:
                sinks.add(c)

        if not sinks:
            break
        removed_per_round.append(len(sinks))
        remaining -= sinks
        rounds += 1

    return remaining, rounds, removed_per_round


def find_sccs(nodes, adj):
    """Tarjan's SCC on given node set."""
    remaining = set(nodes)
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
        for w, _ in adj.get(v, []):
            if w not in remaining:
                continue
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

    old_limit = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old_limit, len(remaining) + 100))
    for v in remaining:
        if v not in index_map:
            sc(v)
    sys.setrecursionlimit(old_limit)
    return sccs


# ============================================================
# PART 1: SINKS PER BINARY STATE
# ============================================================
print("=" * 70)
print("PART 1: Sinks per binary state in forced graph")
print("=" * 70)
print()

binary_states_6cycle = [
    (0, 0, 1), (0, 1, 1), (0, 1, 0),
    (1, 1, 0), (1, 0, 0), (1, 0, 1)
]
uniform_binary = [(0, 0, 0), (1, 1, 1)]

for n, ms in [(5, (2, 2, 2, 3, 3)), (6, (2, 2, 2, 3, 3, 3))]:
    P = 1
    for m in ms:
        P *= m
    T = 3 ** (n - 3)

    cycles = enumerate_cycles(ms, n, max_cycles=20, max_time=30.0)
    full = [(c, m, d) for c, m, d in cycles if set(m) == set(range(n))]
    if not full:
        continue

    cycle, movers, det = full[0][:3]
    good_set = set(cycle)
    L = len(cycle)

    non_good, non_good_set, adj = build_forced_graph(ms, n, det, good_set)

    print(f"n={n}, ms={list(ms)}, P={P}, L={L}, T={T}")
    print(f"Total non-good: {len(non_good)}")
    print()

    # Count sinks per binary state
    for b in binary_states_6cycle + uniform_binary:
        configs_at_b = [c for c in non_good if tuple(c[:3]) == b]
        sinks_at_b = [c for c in configs_at_b if not any(
            t in non_good_set for t, _ in adj.get(c, []))]
        # Classify outgoing edges
        edge_types = Counter()
        for c in configs_at_b:
            for target, p in adj.get(c, []):
                if target in non_good_set:
                    if p < 3:
                        edge_types[f"P{p}"] += 1
                    else:
                        edge_types["ternary"] += 1

        print(f"  Binary {b}: {len(configs_at_b)} configs, "
              f"{len(sinks_at_b)} sinks ({100*len(sinks_at_b)/max(1,len(configs_at_b)):.0f}%)")
        if edge_types:
            print(f"    Edges: {dict(sorted(edge_types.items()))}")

    # Also check: sinks that are at uniform binary states
    good_at_uniform = sum(1 for c in cycle if tuple(c[:3]) in [(0, 0, 0), (1, 1, 1)])
    print(f"\n  Good at uniform binary: {good_at_uniform}/{L}")
    print()


# ============================================================
# PART 2: ITERATIVE SINK REMOVAL
# ============================================================
print("=" * 70)
print("PART 2: Iterative sink removal — kernel analysis")
print("=" * 70)
print()

for n, ms in [(5, (2, 2, 2, 3, 3)), (5, (2, 2, 2, 3, 4)),
              (6, (2, 2, 2, 3, 3, 3))]:
    P = 1
    for m in ms:
        P *= m
    threshold = 4 * (3 ** (n - 2))

    cycles = enumerate_cycles(ms, n, max_cycles=20, max_time=30.0)
    full = [(c, m, d) for c, m, d in cycles if set(m) == set(range(n))]
    if not full:
        continue

    print(f"n={n}, ms={list(ms)}, P={P}, threshold={threshold}, "
          f"{'SUB' if P < threshold else 'AT'}-threshold")

    # Analyze multiple cycles
    scc_counts = []
    kernel_sizes = []
    for ci, (cycle, movers, det) in enumerate(full[:10]):
        good_set = set(cycle)
        non_good, non_good_set, adj = build_forced_graph(ms, n, det, good_set)
        kernel, rounds, removed = iterative_sink_removal(non_good, adj)
        sccs = find_sccs(kernel, adj)

        # Kernel binary distribution
        kernel_by_bin = Counter()
        for c in kernel:
            kernel_by_bin[tuple(c[:3])] += 1

        total_scc = sum(len(s) for s in sccs)
        max_scc = max((len(s) for s in sccs), default=0)

        if ci == 0:
            print(f"  Cycle 0: L={len(cycle)}, non-good={len(non_good)}, "
                  f"rounds={rounds}, removed={removed}")
            print(f"  Kernel: {len(kernel)} configs, SCCs: {len(sccs)}, "
                  f"max={max_scc}, total={total_scc}")
            print(f"  Kernel by binary state:")
            for b in binary_states_6cycle:
                cnt = kernel_by_bin.get(b, 0)
                print(f"    {b}: {cnt}")
            for b in uniform_binary:
                cnt = kernel_by_bin.get(b, 0)
                if cnt > 0:
                    print(f"    {b}: {cnt} (uniform)")

        scc_counts.append(len(sccs))
        kernel_sizes.append(len(kernel))

    print(f"\n  Across {len(full[:10])} cycles:")
    print(f"    Kernel sizes: min={min(kernel_sizes)}, max={max(kernel_sizes)}, "
          f"mean={sum(kernel_sizes)/len(kernel_sizes):.0f}")
    print(f"    SCC counts: {Counter(scc_counts)}")
    print(f"    ALL have SCC: {all(k > 0 for k in scc_counts)}")
    print()


# ============================================================
# PART 3: P1 EDGE SURVIVAL IN KERNEL
# ============================================================
print("=" * 70)
print("PART 3: P1 edge survival in kernel")
print("=" * 70)
print()

for n, ms in [(5, (2, 2, 2, 3, 3)), (6, (2, 2, 2, 3, 3, 3))]:
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
    non_good, non_good_set, adj = build_forced_graph(ms, n, det, good_set)
    kernel, _, _ = iterative_sink_removal(non_good, adj)
    kernel_set = set(kernel)

    # Count P1 edges that survive in kernel
    p1_up_survive = 0
    p1_up_total = 0
    p1_down_survive = 0
    p1_down_total = 0

    for c in non_good:
        for target, p in adj.get(c, []):
            if p == 1 and target in non_good_set:
                if c[1] == 0:  # P1 UP
                    p1_up_total += 1
                    if c in kernel_set and target in kernel_set:
                        p1_up_survive += 1
                else:  # P1 DOWN
                    p1_down_total += 1
                    if c in kernel_set and target in kernel_set:
                        p1_down_survive += 1

    print(f"n={n}, ms={list(ms)}, T={T}")
    print(f"  P1 UP: {p1_up_survive}/{p1_up_total} survive in kernel "
          f"({100*p1_up_survive/max(1,p1_up_total):.0f}%)")
    print(f"  P1 DOWN: {p1_down_survive}/{p1_down_total} survive in kernel "
          f"({100*p1_down_survive/max(1,p1_down_total):.0f}%)")

    # Which fibers have P1 edges surviving?
    up_fibers_survive = set()
    up_fibers_total = set()
    for c in non_good:
        for target, p in adj.get(c, []):
            if p == 1 and c[1] == 0 and target in non_good_set:
                fiber = tuple(c[3:])
                up_fibers_total.add(fiber)
                if c in kernel_set and target in kernel_set:
                    up_fibers_survive.add(fiber)

    print(f"  P1 UP fibers: {len(up_fibers_survive)}/{len(up_fibers_total)} survive")
    print()


# ============================================================
# PART 4: SCC TRANSITION ANALYSIS — how does the SCC use edges?
# ============================================================
print("=" * 70)
print("PART 4: SCC transition analysis — P1/P0/P2/ternary decomposition")
print("=" * 70)
print()

for n, ms in [(5, (2, 2, 2, 3, 3)), (6, (2, 2, 2, 3, 3, 3))]:
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
    non_good, non_good_set, adj = build_forced_graph(ms, n, det, good_set)
    sccs = find_sccs(non_good, adj)

    if not sccs:
        continue

    scc0 = set(sccs[0])

    # Count edges within the SCC by type
    edge_by_type = Counter()
    binary_transitions = Counter()
    fiber_changes = 0
    fiber_same = 0

    for c in sccs[0]:
        for target, p in adj.get(c, []):
            if target in scc0:
                if p < 3:
                    edge_by_type[f"P{p}"] += 1
                    src_bin = tuple(c[:3])
                    tgt_bin = tuple(target[:3])
                    binary_transitions[(src_bin, tgt_bin)] += 1
                else:
                    edge_by_type[f"ternary"] += 1

                src_fiber = tuple(c[3:])
                tgt_fiber = tuple(target[3:])
                if src_fiber == tgt_fiber:
                    fiber_same += 1
                else:
                    fiber_changes += 1

    print(f"n={n}, ms={list(ms)}, SCC size={len(sccs[0])}")
    print(f"  Edge types: {dict(sorted(edge_by_type.items()))}")
    print(f"  Fiber: same={fiber_same}, change={fiber_changes}")

    print(f"\n  Binary transitions within SCC:")
    for (sb, tb), cnt in sorted(binary_transitions.items()):
        expected = ""
        # Check if this is a 6-cycle edge
        cycle_edges = {
            ((0, 0, 1), (0, 1, 1)): "P1 UP",
            ((0, 1, 1), (0, 1, 0)): "P2 DOWN",
            ((0, 1, 0), (1, 1, 0)): "P0 UP",
            ((1, 1, 0), (1, 0, 0)): "P1 DOWN",
            ((1, 0, 0), (1, 0, 1)): "P2 UP",
            ((1, 0, 1), (0, 0, 1)): "P0 DOWN",
        }
        if (sb, tb) in cycle_edges:
            expected = f" [{cycle_edges[(sb, tb)]}]"
        print(f"    {sb} -> {tb}: {cnt}{expected}")

    # Off-cycle binary transitions (P0 or P2 not in the 6-cycle direction)
    off_cycle = {(sb, tb): cnt for (sb, tb), cnt in binary_transitions.items()
                 if (sb, tb) not in {
                     ((0, 0, 1), (0, 1, 1)), ((0, 1, 1), (0, 1, 0)),
                     ((0, 1, 0), (1, 1, 0)), ((1, 1, 0), (1, 0, 0)),
                     ((1, 0, 0), (1, 0, 1)), ((1, 0, 1), (0, 0, 1)),
                 }}
    if off_cycle:
        print(f"\n  OFF-CYCLE binary transitions: {off_cycle}")
    else:
        print(f"\n  ALL binary transitions are 6-cycle edges!")
    print()


# ============================================================
# PART 5: FIBER CONNECTIVITY AT EACH BINARY STATE
# ============================================================
print("=" * 70)
print("PART 5: Fiber connectivity — ternary transitions at each binary state")
print("=" * 70)
print()

for n, ms in [(5, (2, 2, 2, 3, 3)), (6, (2, 2, 2, 3, 3, 3))]:
    P = 1
    for m in ms:
        P *= m
    T = 3 ** (n - 3)

    cycles = enumerate_cycles(ms, n, max_cycles=5, max_time=30.0)
    full = [(c, m, d) for c, m, d in cycles if set(m) == set(range(n))]
    if not full:
        continue

    cycle, movers, det = full[0][:3]
    good_set = set(cycle)
    non_good, non_good_set, adj = build_forced_graph(ms, n, det, good_set)

    print(f"n={n}, ms={list(ms)}, T={T}")

    for b in binary_states_6cycle:
        configs_at_b = [c for c in non_good if tuple(c[:3]) == b]
        if not configs_at_b:
            continue

        # Build ternary-only adjacency at this binary state
        fiber_adj = defaultdict(set)
        for c in configs_at_b:
            fiber_src = tuple(c[3:])
            for target, p in adj.get(c, []):
                if target in non_good_set and tuple(target[:3]) == b:
                    # Same binary state — must be a ternary transition
                    fiber_tgt = tuple(target[3:])
                    if fiber_src != fiber_tgt:
                        fiber_adj[fiber_src].add(fiber_tgt)

        # Count fibers with ternary outgoing edges
        fibers_with_out = len([f for f in fiber_adj if fiber_adj[f]])
        total_fibers = len(set(tuple(c[3:]) for c in configs_at_b))

        # Check which fibers have the NEXT 6-cycle binary edge
        # At (0,0,1): next is P1 UP → always available
        # At (0,1,1): next is P2 DOWN at specific t_0
        # At (0,1,0): next is P0 UP at specific t_{n-4}
        # At (1,1,0): next is P1 DOWN → always available
        # At (1,0,0): next is P2 UP at specific t_0
        # At (1,0,1): next is P0 DOWN at specific t_{n-4}
        fibers_with_6cycle = 0
        for c in configs_at_b:
            for target, p in adj.get(c, []):
                if target in non_good_set and tuple(target[:3]) != b:
                    fibers_with_6cycle += 1
                    break

        print(f"\n  Binary {b}: {total_fibers} fibers, "
              f"{fibers_with_out} with ternary out-edges, "
              f"{fibers_with_6cycle}/{len(configs_at_b)} have 6-cycle exit")

        # Check: from any fiber, can ternary transitions reach a fiber with 6-cycle exit?
        # BFS on fiber graph
        fibers_with_exit = set()
        for c in configs_at_b:
            has_exit = False
            for target, p in adj.get(c, []):
                if target in non_good_set and tuple(target[:3]) != b:
                    has_exit = True
                    break
            if has_exit:
                fibers_with_exit.add(tuple(c[3:]))

        # BFS backward from exit fibers through ternary adjacency
        # Build reverse ternary adjacency
        rev_fiber_adj = defaultdict(set)
        for src, tgts in fiber_adj.items():
            for tgt in tgts:
                rev_fiber_adj[tgt].add(src)

        reachable = set(fibers_with_exit)
        queue = list(fibers_with_exit)
        while queue:
            f = queue.pop(0)
            for prev in rev_fiber_adj.get(f, set()):
                if prev not in reachable:
                    reachable.add(prev)
                    queue.append(prev)

        print(f"    Fibers with 6-cycle exit: {len(fibers_with_exit)}/{total_fibers}")
        print(f"    Reachable to exit via ternary: {len(reachable)}/{total_fibers}")

    print()


# ============================================================
# PART 6: P2 AND P0 MOVER ENTRY ANALYSIS — which fibers they cover
# ============================================================
print("=" * 70)
print("PART 6: P0/P2 mover entries — fiber coverage")
print("=" * 70)
print()

for n, ms in [(5, (2, 2, 2, 3, 3)), (6, (2, 2, 2, 3, 3, 3))]:
    P = 1
    for m in ms:
        P *= m
    T = 3 ** (n - 3)

    cycles = enumerate_cycles(ms, n, max_cycles=5, max_time=30.0)
    full = [(c, m, d) for c, m, d in cycles if set(m) == set(range(n))]
    if not full:
        continue

    print(f"n={n}, ms={list(ms)}, T={T}")

    for ci, (cycle, movers, det) in enumerate(full[:3]):
        good_set = set(cycle)

        # P2 mover entries
        p2_entries = {}
        p0_entries = {}
        for key, val in det.items():
            proc, Lv, Sv, Rv = key
            if val != Sv:  # mover entry
                if proc == 2:
                    p2_entries[key] = val
                elif proc == 0:
                    p0_entries[key] = val

        print(f"\n  Cycle {ci} (L={len(cycle)}):")
        print(f"    P2 mover entries:")
        for key, val in sorted(p2_entries.items()):
            _, Lv, Sv, Rv = key
            direction = "UP" if val > Sv else "DOWN"
            print(f"      ({Lv},{Sv},{Rv}) -> {val} [{direction}]")

        print(f"    P0 mover entries:")
        for key, val in sorted(p0_entries.items()):
            _, Lv, Sv, Rv = key
            direction = "UP" if val > Sv else "DOWN"
            print(f"      ({Lv},{Sv},{Rv}) -> {val} [{direction}]")

        # P2 DOWN right context (P3 value) vs P2 UP right context
        p2_down_R = [Rv for (_, Lv, Sv, Rv), val in p2_entries.items() if val < Sv]
        p2_up_R = [Rv for (_, Lv, Sv, Rv), val in p2_entries.items() if val > Sv]
        print(f"    P2 DOWN R-values: {p2_down_R}")
        print(f"    P2 UP R-values: {p2_up_R}")
        if p2_down_R and p2_up_R:
            print(f"    P2 same R? {set(p2_down_R) & set(p2_up_R)}")

        # P0 LEFT context (P_{n-1} value)
        p0_up_L = [Lv for (_, Lv, Sv, Rv), val in p0_entries.items() if val > Sv]
        p0_down_L = [Lv for (_, Lv, Sv, Rv), val in p0_entries.items() if val < Sv]
        print(f"    P0 UP L-values: {p0_up_L}")
        print(f"    P0 DOWN L-values: {p0_down_L}")
        if p0_up_L and p0_down_L:
            print(f"    P0 same L? {set(p0_up_L) & set(p0_down_L)}")

    print()


# ============================================================
# PART 7: CYCLE PATH TRACING — trace actual cycles in the SCC
# ============================================================
print("=" * 70)
print("PART 7: Cycle path tracing — actual paths in the SCC")
print("=" * 70)
print()

for n, ms in [(5, (2, 2, 2, 3, 3)), (6, (2, 2, 2, 3, 3, 3))]:
    P = 1
    for m in ms:
        P *= m
    T = 3 ** (n - 3)

    cycles = enumerate_cycles(ms, n, max_cycles=5, max_time=30.0)
    full = [(c, m, d) for c, m, d in cycles if set(m) == set(range(n))]
    if not full:
        continue

    cycle, movers, det = full[0][:3]
    good_set = set(cycle)
    non_good, non_good_set, adj = build_forced_graph(ms, n, det, good_set)
    sccs = find_sccs(non_good, adj)

    if not sccs:
        continue

    scc0 = set(sccs[0])
    print(f"n={n}, ms={list(ms)}, SCC size={len(sccs[0])}")

    # BFS for shortest cycle from a P1-UP source in the SCC
    from collections import deque

    # Find a config at (0,0,1) in the SCC
    start = None
    for c in sccs[0]:
        if tuple(c[:3]) == (0, 0, 1):
            start = c
            break

    if start is None:
        print("  No (0,0,1) config in SCC")
        continue

    # BFS for shortest cycle back to start
    queue = deque([(start, [start], [])])
    visited = {start}
    shortest = None
    shortest_procs = None

    while queue:
        node, path, procs = queue.popleft()
        for nb, p in adj.get(node, []):
            if nb == start and len(path) > 1:
                shortest = path + [start]
                shortest_procs = procs + [p]
                break
            if nb in scc0 and nb not in visited:
                visited.add(nb)
                queue.append((nb, path + [nb], procs + [p]))
        if shortest:
            break

    if shortest:
        print(f"  Shortest cycle length: {len(shortest)-1}")
        print(f"  Processors: {shortest_procs}")
        print(f"  Path:")
        for i in range(len(shortest) - 1):
            c = shortest[i]
            p = shortest_procs[i]
            b = tuple(c[:3])
            fiber = tuple(c[3:])
            nb = shortest[i + 1]
            nb_b = tuple(nb[:3])
            nb_fiber = tuple(nb[3:])
            fiber_change = " [FIBER CHANGE]" if fiber != nb_fiber else ""
            print(f"    {c} (bin={b}, fib={fiber}) -P{p}-> "
                  f"{nb} (bin={nb_b}, fib={nb_fiber}){fiber_change}")

    # Count cycles of different lengths
    print(f"\n  Binary states visited in shortest cycle:")
    if shortest:
        bin_seq = [tuple(c[:3]) for c in shortest]
        fiber_seq = [tuple(c[3:]) for c in shortest]
        print(f"    Binary: {bin_seq}")
        print(f"    Fibers: {fiber_seq}")

        # Does the cycle follow the 6-cycle?
        is_6cycle = True
        cycle_edges = {
            ((0, 0, 1), (0, 1, 1)), ((0, 1, 1), (0, 1, 0)),
            ((0, 1, 0), (1, 1, 0)), ((1, 1, 0), (1, 0, 0)),
            ((1, 0, 0), (1, 0, 1)), ((1, 0, 1), (0, 0, 1)),
        }
        for i in range(len(bin_seq) - 1):
            edge = (bin_seq[i], bin_seq[i + 1])
            if edge not in cycle_edges and bin_seq[i] != bin_seq[i + 1]:
                print(f"    OFF-CYCLE edge: {edge}")
                is_6cycle = False
        ternary_steps = sum(1 for i in range(len(bin_seq) - 1) if bin_seq[i] == bin_seq[i + 1])
        print(f"    Ternary (same binary) steps: {ternary_steps}")
        print(f"    All binary edges are 6-cycle: {is_6cycle}")

    print()


# ============================================================
# PART 8: UNIVERSALITY — check across ALL sub-threshold multisets at n=5
# ============================================================
print("=" * 70)
print("PART 8: Universality — kernel non-empty across all sub-threshold")
print("=" * 70)
print()

def generate_sub_threshold_ms(n, threshold):
    """Generate sub-threshold multisets with >= 3 binary."""
    from itertools import combinations_with_replacement
    results = []
    # All multisets of n values, each >= 2, with >= 3 being exactly 2
    for non_bin_vals in iproduct(range(3, 20), repeat=n - 3):
        ms_list = [2, 2, 2] + list(non_bin_vals)
        prod = 1
        for m in ms_list:
            prod *= m
        if prod >= threshold or prod > 500:  # skip too large for enumeration
            continue
        ms_list.sort()
        ms_tuple = tuple(ms_list)
        if ms_tuple not in results:
            results.append(ms_tuple)
    return results

n = 5
threshold = 4 * (3 ** (n - 2))
sub_thresh = generate_sub_threshold_ms(n, threshold)
print(f"n={n}, threshold={threshold}, {len(sub_thresh)} sub-threshold multisets")

all_have_scc = True
for ms in sub_thresh:
    P = 1
    for m in ms:
        P *= m
    if P > 500:
        continue

    cycles = enumerate_cycles(ms, n, max_cycles=20, max_time=15.0)
    full = [(c, m, d) for c, m, d in cycles if set(m) == set(range(n))]

    for ci, (cycle_data, movers, det) in enumerate(full[:5]):
        good_set = set(cycle_data)
        non_good, non_good_set, adj = build_forced_graph(ms, n, det, good_set)
        kernel, rounds, removed = iterative_sink_removal(non_good, adj)

        if len(kernel) == 0:
            print(f"  EMPTY KERNEL: ms={list(ms)}, cycle {ci}, L={len(cycle_data)}")
            all_have_scc = False

print(f"\nAll sub-threshold cycles have non-empty kernel: {all_have_scc}")


# ============================================================
# SUMMARY
# ============================================================
print()
print("=" * 70)
print("EXPLORATION 10 SUMMARY")
print("=" * 70)
print("""
KEY FINDINGS:
1. Sinks per binary state: where do they concentrate?
2. Iterative sink removal: kernel always non-empty?
3. P1 edges survive in kernel (ternary-independent backbone)?
4. SCC uses only 6-cycle binary edges (no off-cycle)?
5. Fiber connectivity: ternary transitions reach 6-cycle exit fibers?
6. P0/P2 mover entry fiber coverage
7. Actual cycle paths: how many ternary detours needed?
8. Universal across all sub-threshold multisets?

PROOF APPROACH:
If kernel is always non-empty, then:
  - Minimum out-degree >= 1 in kernel
  - Any walk from kernel node must stay in kernel forever
  - Finite kernel => directed cycle exists
  - Directed cycle among non-good configs => adversary can loop forever
  - System is NOT self-stabilizing => invalid

This proves: every sub-threshold good cycle creates a forced SCC,
blocking ANY completion to a valid system.
""")
