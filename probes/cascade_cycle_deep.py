#!/usr/bin/env python3
"""Deep cascade cycle analysis — look inside the full recurrent SCCs.

The proc-1-locked approach was too restrictive (all cycles were interior-only).
Now: examine the large SCCs (112, 16) directly for cascade patterns.

Strategy:
1. Extract all cycles in recurrent SCCs
2. For each cycle, classify edges by firing proc type (binary/border/interior)
3. Find "boundary-switch sub-paths": consecutive edges where border procs fire
4. Test if interior ordering is incompatible across different boundary conditions
5. Look for the specific cascade pattern: interior→border→interior→border→return
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import defaultdict, Counter
import time

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
    """Build best n=8 3CB system."""
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
                    if rec == 0:
                        return best_result
    return best_result


def find_short_cycles(scc, edges_in_scc, max_len=12):
    """Find short cycles within an SCC using DFS."""
    cycles = []
    scc_list = sorted(scc)

    for start in scc_list[:50]:  # Limit starting nodes
        # DFS from start, looking for cycles back to start
        stack = [(start, [start], set([start]))]
        found = 0
        while stack and found < 5:
            node, path, visited = stack.pop()
            for succ, proc in edges_in_scc.get(node, []):
                if succ == start and len(path) >= 2:
                    cycles.append((list(path), [proc]))  # Will fix proc list below
                    found += 1
                    if found >= 5:
                        break
                elif succ not in visited and len(path) < max_len:
                    stack.append((succ, path + [succ], visited | {succ}))

    return cycles


def find_all_simple_cycles_bfs(scc, edges_in_scc, max_len=8):
    """Find ALL simple cycles up to max_len using path enumeration."""
    cycles = []
    scc_list = sorted(scc)

    for start in scc_list:
        # BFS paths from start
        queue = [(start, [start])]
        while queue:
            node, path = queue.pop(0)
            if len(path) > max_len:
                continue
            for succ, proc in edges_in_scc.get(node, []):
                if succ == start and len(path) >= 2:
                    # Found cycle - record procs
                    procs = []
                    for i in range(len(path)):
                        for s, p in edges_in_scc[path[i]]:
                            if s == path[(i+1) % len(path)]:
                                procs.append(p)
                                break
                    cycles.append((path, procs))
                elif succ not in set(path) and len(path) < max_len:
                    queue.append((succ, path + [succ]))

    # Deduplicate cycles (same set of nodes = same cycle)
    seen = set()
    unique = []
    for path, procs in cycles:
        key = frozenset(enumerate(path))  # ordered
        # Canonical form: rotate to smallest
        min_idx = path.index(min(path))
        canonical = tuple(path[min_idx:] + path[:min_idx])
        if canonical not in seen:
            seen.add(canonical)
            unique.append((path, procs))

    return unique


def analyze_scc_structure(scc, edges_in_scc, ms, fs, binary_procs, border_procs, interior_procs, scc_idx):
    """Deep structural analysis of a recurrent SCC."""
    n = len(ms)

    print(f"\n{'='*60}")
    print(f"SCC {scc_idx}: {len(scc)} configs")
    print(f"{'='*60}")

    # Firing procs
    firing_procs = set()
    edge_type_count = Counter()
    for c in scc:
        for s, p in edges_in_scc.get(c, []):
            firing_procs.add(p)
            if p in binary_procs:
                edge_type_count['binary'] += 1
            elif p in border_procs:
                edge_type_count['border'] += 1
            elif p in interior_procs:
                edge_type_count['interior'] += 1

    print(f"Firing procs: {sorted(firing_procs)}")
    print(f"Edge type counts: {dict(edge_type_count)}")

    # Boundary conditions
    boundaries = Counter()
    for c in scc:
        b = tuple(c[p] for p in border_procs)
        boundaries[b] += 1
    print(f"Boundary conditions: {dict(sorted(boundaries.items()))}")

    # Interior states
    interior_states = Counter()
    for c in scc:
        u = tuple(c[p] for p in interior_procs)
        interior_states[u] += 1
    print(f"Interior states: {len(interior_states)} distinct")

    # Binary states
    binary_states = Counter()
    for c in scc:
        bv = tuple(c[p] for p in binary_procs)
        binary_states[bv] += 1
    print(f"Binary states: {len(binary_states)} distinct")

    # ─── Interior DAG analysis per boundary condition ───────────────
    print(f"\n  INTERIOR BEHAVIOR PER BOUNDARY:")

    for boundary in sorted(boundaries.keys()):
        # Configs in this SCC with this boundary
        configs_at_b = [c for c in scc
                        if tuple(c[p] for p in border_procs) == boundary]

        # Interior-only transitions at this boundary
        interior_edges = []
        for c in configs_at_b:
            for s, p in edges_in_scc.get(c, []):
                if p in interior_procs and s in scc:
                    sc = tuple(s[ip] for ip in interior_procs)
                    cc = tuple(c[ip] for ip in interior_procs)
                    if tuple(s[bp] for bp in border_procs) == boundary:
                        interior_edges.append((cc, sc, p))

        # Check for interior cycles at this boundary
        int_states_here = set(tuple(c[ip] for ip in interior_procs) for c in configs_at_b)
        int_succs = defaultdict(set)
        for cc, sc, p in interior_edges:
            int_succs[cc].add(sc)

        # Simple cycle check
        has_int_cycle = False
        for u in int_states_here:
            visited = set()
            stack = [u]
            while stack:
                v = stack.pop()
                if v in visited:
                    if v == u and len(visited) > 0:
                        has_int_cycle = True
                        break
                    continue
                visited.add(v)
                for w in int_succs.get(v, set()):
                    stack.append(w)
            if has_int_cycle:
                break

        print(f"    Boundary {boundary}: {len(configs_at_b)} configs, "
              f"{len(interior_edges)} interior edges, "
              f"interior cycle: {has_int_cycle}")

        if len(int_states_here) <= 10:
            for u in sorted(int_states_here):
                targets = sorted(int_succs.get(u, set()))
                if targets:
                    print(f"      {u} -> {targets}")

    # ─── Border transition analysis ───────────────────────────────
    print(f"\n  BORDER TRANSITIONS:")
    border_transitions = []
    for c in scc:
        for s, p in edges_in_scc.get(c, []):
            if p in border_procs and s in scc:
                bc = tuple(c[bp] for bp in border_procs)
                bs = tuple(s[bp] for bp in border_procs)
                ic = tuple(c[ip] for ip in interior_procs)
                is_ = tuple(s[ip] for ip in interior_procs)
                bvc = tuple(c[bp] for bp in binary_procs)
                bvs = tuple(s[bp] for bp in binary_procs)
                border_transitions.append({
                    'from': c, 'to': s, 'proc': p,
                    'boundary_from': bc, 'boundary_to': bs,
                    'interior_from': ic, 'interior_to': is_,
                    'binary_from': bvc, 'binary_to': bvs,
                    'boundary_changed': bc != bs,
                })

    boundary_switch_count = sum(1 for t in border_transitions if t['boundary_changed'])
    print(f"  Total border transitions: {len(border_transitions)}")
    print(f"  Boundary-switching transitions: {boundary_switch_count}")

    if boundary_switch_count > 0:
        print(f"\n  BOUNDARY SWITCHES (first 20):")
        for t in border_transitions[:20]:
            if t['boundary_changed']:
                print(f"    p{t['proc']}: boundary {t['boundary_from']}->{t['boundary_to']}, "
                      f"interior {t['interior_from']}->{t['interior_to']}, "
                      f"binary {t['binary_from']}->{t['binary_to']}")

    # ─── Search for cascade cycles ────────────────────────────────
    print(f"\n  SEARCHING FOR CASCADE CYCLES...")

    # A cascade cycle: start at config c, follow edges,
    # require at least one border-switch and return to c
    if len(scc) <= 200:
        cycles = find_all_simple_cycles_bfs(scc, edges_in_scc, max_len=8)
        print(f"  Found {len(cycles)} simple cycles (len <= 8)")

        cascade_cycles = []
        interior_only_cycles = []
        for path, procs in cycles:
            has_border_fire = any(p in border_procs for p in procs)
            has_interior_fire = any(p in interior_procs for p in procs)
            has_binary_fire = any(p in binary_procs for p in procs)

            # Count boundary switches in cycle
            switches = 0
            for i in range(len(path)):
                c = path[i]
                s = path[(i+1) % len(path)]
                bc = tuple(c[bp] for bp in border_procs)
                bs = tuple(s[bp] for bp in border_procs)
                if bc != bs:
                    switches += 1

            if has_border_fire and switches >= 1:
                cascade_cycles.append((path, procs, switches))
            elif not has_border_fire and not has_binary_fire:
                interior_only_cycles.append((path, procs))

        print(f"  Cascade cycles (border-switch): {len(cascade_cycles)}")
        print(f"  Interior-only cycles: {len(interior_only_cycles)}")

        # Show cascade cycles
        for i, (path, procs, switches) in enumerate(cascade_cycles[:10]):
            print(f"\n    CASCADE CYCLE {i} (len={len(path)}, switches={switches}):")
            for j in range(len(path)):
                c = path[j]
                s = path[(j+1) % len(path)]
                p = procs[j] if j < len(procs) else '?'
                bc = tuple(c[bp] for bp in border_procs)
                ic = tuple(c[ip] for ip in interior_procs)
                bvc = tuple(c[bp] for bp in binary_procs)
                bs = tuple(s[bp] for bp in border_procs)
                is_ = tuple(s[ip] for ip in interior_procs)
                sw = " <<SWITCH>>" if bc != bs else ""
                ptype = "BIN" if p in binary_procs else ("BRD" if p in border_procs else "INT")
                print(f"      {c} --[p{p} {ptype}]--> border:{bc} int:{ic} bin:{bvc}{sw}")

        # Analyze cascade cycle patterns
        if cascade_cycles:
            print(f"\n  CASCADE CYCLE PATTERNS:")
            pattern_counts = Counter()
            for path, procs, switches in cascade_cycles:
                proc_types = []
                for p in procs:
                    if p in binary_procs:
                        proc_types.append('B')
                    elif p in border_procs:
                        proc_types.append('R')  # boRder
                    else:
                        proc_types.append('I')
                pattern = ''.join(proc_types)
                pattern_counts[pattern] += 1
            for pattern, count in pattern_counts.most_common(20):
                print(f"    {pattern}: {count}")

    # ─── Incompatible interior ordering ──────────────────────────
    print(f"\n  INCOMPATIBLE ORDERING CHECK:")
    # For each pair of boundary conditions, check if there exist interior states
    # u, v such that u->v under boundary b1 but v->u under boundary b2

    boundary_list = sorted(boundaries.keys())
    for i, b1 in enumerate(boundary_list):
        # Interior transitions under b1
        trans_b1 = {}
        for c in scc:
            if tuple(c[bp] for bp in border_procs) != b1:
                continue
            for s, p in edges_in_scc.get(c, []):
                if p in interior_procs and s in scc:
                    if tuple(s[bp] for bp in border_procs) == b1:
                        u = tuple(c[ip] for ip in interior_procs)
                        v = tuple(s[ip] for ip in interior_procs)
                        if u != v:
                            trans_b1[(u, v)] = p

        for j, b2 in enumerate(boundary_list):
            if j <= i:
                continue
            # Interior transitions under b2
            trans_b2 = {}
            for c in scc:
                if tuple(c[bp] for bp in border_procs) != b2:
                    continue
                for s, p in edges_in_scc.get(c, []):
                    if p in interior_procs and s in scc:
                        if tuple(s[bp] for bp in border_procs) == b2:
                            u = tuple(c[ip] for ip in interior_procs)
                            v = tuple(s[ip] for ip in interior_procs)
                            if u != v:
                                trans_b2[(u, v)] = p

            # Check for incompatible orderings: u->v in b1 and v->u in b2
            incompatible = []
            for (u, v) in trans_b1:
                if (v, u) in trans_b2:
                    incompatible.append((u, v, trans_b1[(u, v)], trans_b2[(v, u)]))

            if incompatible:
                print(f"    Boundaries {b1} vs {b2}: {len(incompatible)} INCOMPATIBLE pairs!")
                for u, v, p1, p2 in incompatible[:5]:
                    print(f"      {u} -> {v} (p{p1}) under {b1}, "
                          f"{v} -> {u} (p{p2}) under {b2}")
            else:
                print(f"    Boundaries {b1} vs {b2}: compatible (no reversals)")


def main():
    ms = (2, 2, 2, 3, 3, 3, 3, 4)
    n = len(ms)
    binary_procs = [0, 1, 2]
    border_procs = [3, 7]
    interior_procs = [4, 5, 6]

    print(f"n={n}, ms={ms}")
    print(f"Binary: {binary_procs}, Border: {border_procs}, Interior: {interior_procs}")

    print("\nBuilding best system...")
    t0 = time.time()
    result = build_best_n8()
    print(f"Build time: {time.time()-t0:.1f}s")

    ms, fs, tables, good_set, rec = result
    print(f"Recurrent bad: {rec}")

    # Build full bad graph with edge info
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

    # Find recurrent SCCs
    sccs = tarjan_scc(bad, lambda v: [s for s, _ in bad_succs.get(v, [])])
    recurrent = [s for s in sccs if len(s) > 1 or
                 (len(s) == 1 and any(s2 == next(iter(s)) for s2, _ in bad_succs.get(next(iter(s)), [])))]
    recurrent.sort(key=len, reverse=True)

    print(f"\nRecurrent SCCs: {len(recurrent)}")
    print(f"Sizes: {[len(s) for s in recurrent[:10]]}")

    # Build edges within each SCC
    for idx, scc in enumerate(recurrent):
        if len(scc) < 3:
            continue  # Skip trivial 2-cycles

        edges_in_scc = defaultdict(list)
        for c in scc:
            for s, p in bad_succs.get(c, []):
                if s in scc:
                    edges_in_scc[c].append((s, p))

        analyze_scc_structure(scc, edges_in_scc, ms, fs,
                             set(binary_procs), set(border_procs), set(interior_procs), idx)

    # ─── Also analyze the 2-cycles ─────────────────────────────
    print(f"\n{'='*60}")
    print(f"2-CYCLE ANALYSIS")
    print(f"{'='*60}")

    two_cycles = [s for s in recurrent if len(s) == 2]
    print(f"Total 2-cycles: {len(two_cycles)}")

    proc_counts = Counter()
    boundary_counts = Counter()
    for scc in two_cycles:
        procs = set()
        for c in scc:
            for s, p in bad_succs.get(c, []):
                if s in scc:
                    procs.add(p)
        for p in procs:
            proc_counts[p] += 1

        boundaries = set()
        for c in scc:
            b = tuple(c[bp] for bp in border_procs)
            boundaries.add(b)
        boundary_counts[frozenset(boundaries)] += 1

    print(f"Firing proc distribution: {dict(sorted(proc_counts.items()))}")
    print(f"Boundary condition distribution: {dict(boundary_counts)}")

    # ─── Transition table analysis for proc 6 (the oscillator) ─────
    print(f"\n{'='*60}")
    print(f"PROC 6 TRANSITION TABLE (the oscillator)")
    print(f"{'='*60}")

    table6 = tables[6]
    # Proc 6: L=c[5], S=c[6], R=c[7]
    # ms[5]=3, ms[6]=3, ms[7]=4
    print(f"ms[5]={ms[5]}, ms[6]={ms[6]}, ms[7]={ms[7]}")
    for L in range(ms[5]):
        for S in range(ms[6]):
            for R in range(ms[7]):
                out = table6[(L, S, R)]
                priv = "PRIV" if out != S else ""
                print(f"  f6({L},{S},{R}) = {out}  {priv}")


if __name__ == '__main__':
    main()
