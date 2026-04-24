#!/usr/bin/env python3
"""Search for longer cycles in the large recurrent SCCs.

Key insight from previous run: no cycles of len<=8 in the 112-config SCCs.
The interior is a DAG under each boundary, and no incompatible orderings.
So the cycles must involve binary procs too, and be longer.

Strategy:
1. Find ANY cycle in the 112-config SCC using random walks
2. Analyze its structure
3. Check if the SCC is strongly connected (it should be, by definition)
4. Find the shortest cycle using BFS from each node
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import defaultdict, Counter, deque
import time
import random

from verifier import all_configs, privileged_set, apply_move, verify_system
from ra_3cb_transition import (
    build_mixed_sweep_cycle, good_targeting_completion, build_bounce_cycle,
    cyclic_orders, make_fs_from_tables
)


def tarjan_scc(nodes, succs_fn):
    index_counter = [0]
    stack = []
    on_stack = set()
    index = {}
    lowlink = {}
    sccs = []
    for start in nodes:
        if start in index:
            continue
        call_stack = [(start, iter(succs_fn(start)))]
        index[start] = lowlink[start] = index_counter[0]
        index_counter[0] += 1
        stack.append(start)
        on_stack.add(start)
        while call_stack:
            node, children = call_stack[-1]
            advanced = False
            for w in children:
                if w not in index:
                    index[w] = lowlink[w] = index_counter[0]
                    index_counter[0] += 1
                    stack.append(w)
                    on_stack.add(w)
                    call_stack.append((w, iter(succs_fn(w))))
                    advanced = True
                    break
                elif w in on_stack:
                    lowlink[node] = min(lowlink[node], index[w])
            if not advanced:
                call_stack.pop()
                if call_stack:
                    parent = call_stack[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[node])
                if lowlink[node] == index[node]:
                    scc = set()
                    while True:
                        w = stack.pop()
                        on_stack.discard(w)
                        scc.add(w)
                        if w == node:
                            break
                    sccs.append(scc)
    return sccs


def build_best_n8():
    ms = (2, 2, 2, 3, 3, 3, 3, 4)
    n = len(ms)
    best_rec = float('inf')
    best_result = None
    non_binary = [p for p, m in enumerate(ms) if m > 2]
    target_ranges = [range(1, ms[p]) for p in non_binary]
    for combo in cartesian(*target_ranges):
        targets = {p: 1 for p, m in enumerate(ms) if m == 2}
        for idx, p in enumerate(non_binary):
            targets[p] = combo[idx]
        for order in cyclic_orders(n):
            for ret_same in (True, False):
                cycle = build_mixed_sweep_cycle(ms, order, targets, ret_same)
                if cycle is None:
                    continue
                comp = good_targeting_completion(ms, cycle)
                if comp is None:
                    continue
                tables = comp['tables']
                fs = comp['fs']
                result = comp['verify']
                if result['valid']:
                    return ms, fs, tables, set(cycle), 0
                good_set = set(cycle)
                configs = list(all_configs(ms))
                bad = [c for c in configs if c not in good_set]
                bad_set = set(bad)
                bad_succs = defaultdict(list)
                for c in bad:
                    priv = privileged_set(c, fs, ms)
                    for i in priv:
                        s = apply_move(c, i, fs, ms)
                        if s in bad_set:
                            bad_succs[c].append(s)
                sccs = tarjan_scc(bad, lambda v: bad_succs.get(v, []))
                rec = sum(len(s) for s in sccs if len(s) > 1 or
                          (len(s) == 1 and next(iter(s)) in bad_succs.get(next(iter(s)), [])))
                if rec < best_rec:
                    best_rec = rec
                    best_result = (ms, fs, tables, good_set, rec)
    return best_result


def find_shortest_cycle_bfs(start, succs):
    """BFS to find shortest cycle back to start."""
    queue = deque([(start, [])])
    visited = set()

    # First expand from start without marking it visited
    for s, p in succs.get(start, []):
        if s == start:
            return [start], [p]
        queue.append((s, [(start, s, p)]))
        visited.add(s)

    while queue:
        node, path = queue.popleft()
        for s, p in succs.get(node, []):
            if s == start:
                path.append((node, s, p))
                configs = [start] + [e[1] for e in path[:-1]]
                procs = [e[2] for e in path]
                return configs, procs
            if s not in visited:
                visited.add(s)
                queue.append((s, path + [(node, s, p)]))
    return None, None


def random_walk_cycle(start, succs, max_steps=500):
    """Random walk to find a cycle back to start."""
    path = [start]
    procs = []
    current = start
    visited = {start: 0}

    for step in range(max_steps):
        neighbors = succs.get(current, [])
        if not neighbors:
            break
        s, p = random.choice(neighbors)
        procs.append(p)
        if s == start and step > 0:
            return path, procs
        if s in visited:
            # Found a cycle, but not back to start
            idx = visited[s]
            return path[idx:], procs[idx:]
        visited[s] = len(path)
        path.append(s)
        current = s

    return None, None


def main():
    ms = (2, 2, 2, 3, 3, 3, 3, 4)
    n = len(ms)
    binary_procs = {0, 1, 2}
    border_procs = {3, 7}
    interior_procs = {4, 5, 6}

    print(f"n={n}, ms={ms}")
    print("Building best system...")
    t0 = time.time()
    ms, fs, tables, good_set, rec = build_best_n8()
    print(f"Build time: {time.time()-t0:.1f}s, recurrent: {rec}")

    configs = list(all_configs(ms))
    bad = [c for c in configs if c not in good_set]
    bad_set = set(bad)

    bad_succs = defaultdict(list)
    for c in bad:
        priv = privileged_set(c, fs, ms)
        for i in priv:
            s = apply_move(c, i, fs, ms)
            if s in bad_set:
                bad_succs[c].append((s, i))

    sccs = tarjan_scc(bad, lambda v: [s for s, _ in bad_succs.get(v, [])])
    recurrent = [s for s in sccs if len(s) > 1 or
                 (len(s) == 1 and any(s2 == next(iter(s)) for s2, _ in bad_succs.get(next(iter(s)), [])))]
    recurrent.sort(key=len, reverse=True)

    # Focus on the large SCCs
    for scc_idx, scc in enumerate(recurrent):
        if len(scc) < 3:
            continue

        edges = defaultdict(list)
        for c in scc:
            for s, p in bad_succs.get(c, []):
                if s in scc:
                    edges[c].append((s, p))

        print(f"\n{'='*70}")
        print(f"SCC {scc_idx}: {len(scc)} configs")
        print(f"{'='*70}")

        # Check out-degree distribution
        out_degrees = Counter()
        for c in scc:
            out_degrees[len(edges.get(c, []))] += 1
        print(f"Out-degree distribution: {dict(sorted(out_degrees.items()))}")

        in_degree = Counter()
        for c in scc:
            for s, p in edges.get(c, []):
                in_degree[s] += 1
        in_dist = Counter(in_degree.values())
        print(f"In-degree distribution: {dict(sorted(in_dist.items()))}")

        # Find shortest cycle from several starting configs
        print(f"\nShortest cycles (BFS from 10 configs):")
        scc_list = sorted(scc)
        shortest_len = float('inf')
        shortest_cycle = None

        for start in scc_list[:20]:
            path, procs = find_shortest_cycle_bfs(start, edges)
            if path is not None:
                if len(path) < shortest_len:
                    shortest_len = len(path)
                    shortest_cycle = (path, procs)
                if len(path) <= 30:
                    proc_types = []
                    for p in procs:
                        if p in binary_procs:
                            proc_types.append(f'B{p}')
                        elif p in border_procs:
                            proc_types.append(f'R{p}')
                        else:
                            proc_types.append(f'I{p}')
                    print(f"  start={start}: len={len(path)}, procs={' '.join(proc_types)}")

        if shortest_cycle:
            path, procs = shortest_cycle
            print(f"\nSHORTEST CYCLE FOUND: length {len(path)}")
            print(f"Firing procs: {procs}")

            # Detailed trace
            for i in range(len(path)):
                c = path[i]
                p = procs[i]
                s = path[(i+1) % len(path)]
                bc = (c[3], c[7])
                ic = (c[4], c[5], c[6])
                bvc = (c[0], c[1], c[2])
                bs = (s[3], s[7])
                is_ = (s[4], s[5], s[6])
                bvs = (s[0], s[1], s[2])

                ptype = "BIN" if p in binary_procs else ("BRD" if p in border_procs else "INT")
                changes = []
                if bc != bs: changes.append(f"border:{bc}->{bs}")
                if ic != is_: changes.append(f"interior:{ic}->{is_}")
                if bvc != bvs: changes.append(f"binary:{bvc}->{bvs}")
                change_str = ', '.join(changes) if changes else "NO CHANGE??"

                print(f"  [{i:2d}] {c} --[p{p} {ptype}]--> {change_str}")

            # Classify the cycle
            border_fires = sum(1 for p in procs if p in border_procs)
            interior_fires = sum(1 for p in procs if p in interior_procs)
            binary_fires = sum(1 for p in procs if p in binary_procs)
            boundary_switches = 0
            for i in range(len(path)):
                c = path[i]
                s = path[(i+1) % len(path)]
                if (c[3], c[7]) != (s[3], s[7]):
                    boundary_switches += 1

            print(f"\n  Binary fires: {binary_fires}, Border fires: {border_fires}, "
                  f"Interior fires: {interior_fires}")
            print(f"  Boundary switches: {boundary_switches}")

        # Random walk cycles for variety
        print(f"\nRandom walk cycles (5 attempts):")
        random.seed(42)
        cycle_lengths = []
        for trial in range(5):
            start = random.choice(scc_list)
            path, procs = random_walk_cycle(start, edges, max_steps=200)
            if path is not None:
                cycle_lengths.append(len(path))
                proc_types = []
                for p in procs:
                    if p in binary_procs:
                        proc_types.append('B')
                    elif p in border_procs:
                        proc_types.append('R')
                    else:
                        proc_types.append('I')
                pattern = ''.join(proc_types)

                boundary_switches = 0
                for i in range(len(path)):
                    c = path[i]
                    s = path[(i+1) % len(path)]
                    if (c[3], c[7]) != (s[3], s[7]):
                        boundary_switches += 1

                print(f"  Trial {trial}: len={len(path)}, "
                      f"B/R/I={sum(1 for t in proc_types if t=='B')}/"
                      f"{sum(1 for t in proc_types if t=='R')}/"
                      f"{sum(1 for t in proc_types if t=='I')}, "
                      f"boundary_switches={boundary_switches}")
                if len(path) <= 20:
                    print(f"    Pattern: {pattern}")

        # ─── Key question: are the 2-cycles connected to the large SCCs? ──
        print(f"\n  Can 2-cycles reach this SCC?")
        two_cycles = [s for s in recurrent if len(s) == 2]
        two_cycle_set = set()
        for s in two_cycles:
            two_cycle_set |= s

        # Check if any config in this SCC can reach a 2-cycle config
        scc_to_2cycle = 0
        two_to_scc = 0
        for c in scc:
            for s, p in bad_succs.get(c, []):
                if s in two_cycle_set:
                    scc_to_2cycle += 1
        for c in two_cycle_set:
            for s, p in bad_succs.get(c, []):
                if s in scc:
                    two_to_scc += 1
        print(f"  Edges from SCC to 2-cycles: {scc_to_2cycle}")
        print(f"  Edges from 2-cycles to SCC: {two_to_scc}")

    # ─── Global structure: is the recurrent set one big component? ──
    print(f"\n{'='*70}")
    print(f"GLOBAL RECURRENT STRUCTURE")
    print(f"{'='*70}")

    recurrent_set = set()
    for s in recurrent:
        recurrent_set |= s

    # Can the two large SCCs reach each other?
    if len(recurrent) >= 2 and len(recurrent[0]) > 2 and len(recurrent[1]) > 2:
        scc0 = recurrent[0]
        scc1 = recurrent[1]

        # Check transitions between them (NOT within SCC, so these go through non-recurrent)
        edges_0_to_1 = 0
        edges_1_to_0 = 0
        for c in scc0:
            for s, p in bad_succs.get(c, []):
                if s in scc1:
                    edges_0_to_1 += 1
        for c in scc1:
            for s, p in bad_succs.get(c, []):
                if s in scc0:
                    edges_1_to_0 += 1

        print(f"SCC0 ({len(scc0)}) -> SCC1 ({len(scc1)}): {edges_0_to_1} direct edges")
        print(f"SCC1 ({len(scc1)}) -> SCC0 ({len(scc0)}): {edges_1_to_0} direct edges")

    # Configs shared between the two large SCCs
    if len(recurrent) >= 2:
        overlap = recurrent[0] & recurrent[1]
        print(f"Overlap between SCC0 and SCC1: {len(overlap)}")

    # What distinguishes the two 112-config SCCs?
    if len(recurrent) >= 2 and len(recurrent[0]) == 112 and len(recurrent[1]) == 112:
        print(f"\nComparing the two 112-config SCCs:")
        for idx in [0, 1]:
            scc = recurrent[idx]
            binary_vals = Counter()
            for c in scc:
                bv = (c[0], c[1], c[2])
                binary_vals[bv] += 1
            even_parity = sum(cnt for bv, cnt in binary_vals.items() if sum(bv) % 2 == 0)
            odd_parity = sum(cnt for bv, cnt in binary_vals.items() if sum(bv) % 2 == 1)
            print(f"  SCC{idx}: even-parity binary: {even_parity}, odd-parity: {odd_parity}")
            print(f"    Binary values: {dict(sorted(binary_vals.items()))}")


if __name__ == '__main__':
    main()
