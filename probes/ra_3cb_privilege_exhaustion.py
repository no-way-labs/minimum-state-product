#!/usr/bin/env python3
"""Exhaust ALL toggle-valid privilege rules at proc 1 (middle binary) for 3CB n=8.

ms = (2,2,2,3,3,3,3,4), proc 1 has m=2, neighbors m=2,m=2.
Context space: (c0, c1, c2) in {0,1}^3 = 8 triples.
Toggle constraint: if (a,b,c) privileged then (a,1-b,c) not privileged.
The 8 triples split into 4 toggle pairs: {(a,0,c),(a,1,c)} for (a,c) in {0,1}^2.
From each pair, pick at most one. So valid privilege subsets have size 0..4.
Total non-empty: 3^4 - 1 = 80.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import defaultdict
import time

from verifier import all_configs, apply_move, privileged_set, verify_system

MS = (2, 2, 2, 3, 3, 3, 3, 4)
N = len(MS)
PRODUCT = 1
for m in MS:
    PRODUCT *= m

ALL_CFGS = list(cartesian(*(range(m) for m in MS)))
ALL_CFGS_SET = set(ALL_CFGS)
TOTAL = len(ALL_CFGS)

print(f"ms={MS}, n={N}, product={PRODUCT}, total configs={TOTAL}")

toggle_pairs = []
for a in range(2):
    for c in range(2):
        toggle_pairs.append(((a, 0, c), (a, 1, c)))

print(f"\nToggle pairs at proc 1: {toggle_pairs}")

priv_subsets = []
for choices in cartesian(range(3), repeat=4):
    subset = set()
    for pair_idx, choice in enumerate(choices):
        if choice == 1:
            subset.add(toggle_pairs[pair_idx][0])
        elif choice == 2:
            subset.add(toggle_pairs[pair_idx][1])
    if len(subset) == 0:
        continue
    priv_subsets.append(frozenset(subset))

priv_subsets = sorted(set(priv_subsets), key=lambda s: (len(s), sorted(s)))
print(f"Toggle-valid privilege subsets (non-empty): {len(priv_subsets)}")


def make_fs(tables):
    fs = []
    for table in tables:
        def make_f(t):
            def f(L, S, R):
                return t[(L, S, R)]
            return f
        fs.append(make_f(table))
    return fs


def build_tables_from_cycle_with_fixed_p1(cycle, p1_movers):
    n = N
    ms = MS
    good_set = set(cycle)
    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        diffs = [p for p in range(n) if c[p] != c_next[p]]
        if len(diffs) != 1:
            return None
        mover = diffs[0]
        for p in range(n):
            L = c[(p-1) % n]
            S = c[p]
            R = c[(p+1) % n]
            key = (p, L, S, R)
            out = c_next[p] if p == mover else S
            if key in det and det[key] != out:
                return None
            det[key] = out

    for key, out in det.items():
        if key[0] == 1:
            triple = (key[1], key[2], key[3])
            if triple in p1_movers:
                if out != 1 - key[2]:
                    return None
            else:
                if out != key[2]:
                    return None

    comp = dict(det)
    non_good = [c for c in ALL_CFGS if c not in good_set]
    non_good_set = set(non_good)

    free_entries = []
    for p in range(n):
        m_L = ms[(p-1) % n]
        m_S = ms[p]
        m_R = ms[(p+1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in det:
                        free_entries.append(key)

    for key in free_entries:
        if key[0] == 1:
            p, L, S, R = key
            triple = (L, S, R)
            if triple in p1_movers:
                comp[key] = 1 - S
            else:
                comp[key] = S

    triple_index = defaultdict(list)
    for c in non_good:
        for p in range(n):
            key = (p, c[(p-1) % n], c[p], c[(p+1) % n])
            if key not in det and key[0] != 1:
                triple_index[key].append(c)

    edge_costs = {}
    for key in free_entries:
        if key[0] == 1:
            continue
        p, _, self_state, _ = key
        matching = triple_index.get(key, [])
        best_out = self_state
        best_good = 0
        best_ng = 0
        for out in range(ms[p]):
            if out == self_state:
                edge_costs[(key, out)] = 0
                continue
            good_count = 0
            ng_count = 0
            for c in matching:
                new_c = c[:p] + (out,) + c[p+1:]
                if new_c in good_set:
                    good_count += 1
                elif new_c in non_good_set:
                    ng_count += 1
            edge_costs[(key, out)] = ng_count
            if good_count > best_good or (good_count == best_good and ng_count < best_ng):
                best_out = out
                best_good = good_count
                best_ng = ng_count
        comp[key] = best_out

    for c in ALL_CFGS:
        has_priv = False
        for p in range(n):
            key = (p, c[(p-1) % n], c[p], c[(p+1) % n])
            if comp.get(key, c[p]) != c[p]:
                has_priv = True
                break
        if has_priv:
            continue
        best_key = None
        best_cost = float('inf')
        best_out = None
        for p in range(n):
            key = (p, c[(p-1) % n], c[p], c[(p+1) % n])
            if key in det:
                continue
            if p == 1:
                triple = (key[1], key[2], key[3])
                if triple in p1_movers:
                    out = 1 - key[2]
                    cost = edge_costs.get((key, out), 0)
                    if cost < best_cost:
                        best_cost = cost
                        best_key = key
                        best_out = out
                continue
            for out in range(ms[p]):
                if out == c[p]:
                    continue
                cost = edge_costs.get((key, out), 0)
                if cost < best_cost:
                    best_cost = cost
                    best_key = key
                    best_out = out
        if best_key is not None:
            comp[best_key] = best_out

    tables = []
    for p in range(n):
        table = {}
        m_L = ms[(p-1) % n]
        m_S = ms[p]
        m_R = ms[(p+1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    table[(L, S, R)] = comp.get(key, S)
        tables.append(table)
    return tables


def find_bad_sccs(ms, tables):
    fs = make_fs(tables)
    n = len(ms)
    configs = list(all_configs(ms))
    priv_map = {c: privileged_set(c, fs, ms) for c in configs}

    dead = [c for c in configs if len(priv_map[c]) == 0]
    if dead:
        return None, None, None

    single_priv = {c for c in configs if len(priv_map[c]) == 1}
    succ = {}
    for c in single_priv:
        i = priv_map[c][0]
        s = apply_move(c, i, fs, ms)
        succ[c] = (s, i)

    good = set(single_priv)
    changed = True
    while changed:
        changed = False
        to_remove = {c for c in good if succ[c][0] not in good}
        if to_remove:
            good -= to_remove
            changed = True

    fair = False
    visited = set()
    for start in good:
        if start in visited:
            continue
        path = []
        path_set = set()
        node = start
        while node not in visited and node not in path_set:
            path.append(node)
            path_set.add(node)
            node = succ[node][0]
        if node in path_set:
            cycle = path[path.index(node):]
            movers = {succ[c][1] for c in cycle}
            if movers == set(range(n)):
                fair = True
                rev = defaultdict(list)
                for c in single_priv:
                    rev[succ[c][0]].append(c)
                queue = list(cycle)
                good = set(cycle)
                while queue:
                    nd = queue.pop()
                    for pred in rev[nd]:
                        if pred not in good:
                            good.add(pred)
                            queue.append(pred)
                break
        visited.update(path)

    if not fair:
        return None, None, None

    bad = set(configs) - good
    adj = defaultdict(list)
    for c in bad:
        for p in priv_map[c]:
            nxt = apply_move(c, p, fs, ms)
            if nxt in bad:
                adj[c].append(nxt)

    idx_counter = [0]
    stack = []
    on_stack = set()
    index_map = {}
    lowlink = {}
    sccs = []

    def strongconnect(v):
        work = [(v, 0)]
        index_map[v] = lowlink[v] = idx_counter[0]
        idx_counter[0] += 1
        stack.append(v)
        on_stack.add(v)
        while work:
            node, si = work[-1]
            succs = adj.get(node, [])
            if si < len(succs):
                work[-1] = (node, si + 1)
                w = succs[si]
                if w not in index_map:
                    index_map[w] = lowlink[w] = idx_counter[0]
                    idx_counter[0] += 1
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
                    if len(scc) > 1 or (scc[0] in adj and scc[0] in adj.get(scc[0], [])):
                        sccs.append(scc)
                work.pop()
                if work:
                    lowlink[work[-1][0]] = min(lowlink[work[-1][0]], lowlink[node])

    for v in bad:
        if v not in index_map:
            strongconnect(v)

    scc_total = sum(len(s) for s in sccs)
    return len(good), len(sccs), scc_total


def build_sweep_cycle(ms, order, targets, return_same):
    n = len(ms)
    config = [0] * n
    cycle = [tuple(config)]
    for p in order:
        config = list(cycle[-1])
        config[p] = 1 if ms[p] == 2 else targets[p]
        cycle.append(tuple(config))
    down = order if return_same else tuple(reversed(order))
    for p in down:
        config = list(cycle[-1])
        config[p] = 0
        cycle.append(tuple(config))
    if cycle[-1] != cycle[0]:
        return None
    cycle = cycle[:-1]
    if len(set(cycle)) != len(cycle):
        return None
    return cycle


def build_bounce_cycle(ms, base_pattern=None, max_reps=8):
    n = len(ms)
    if base_pattern is None:
        base_pattern = list(range(n)) + list(range(n-2, 0, -1))
    for reps in range(1, max_reps):
        config = [0] * n
        cycle = [tuple(config)]
        visited = {tuple(config)}
        full = list(base_pattern) * reps
        for step, mover in enumerate(full):
            config = list(cycle[-1])
            config[mover] = (config[mover] + 1) % ms[mover]
            nc = tuple(config)
            if nc == cycle[0]:
                return cycle, full[:step+1]
            if nc in visited:
                break
            visited.add(nc)
            cycle.append(nc)
    return None, None


def cyclic_orders(n):
    seen = set()
    for base in (list(range(n)), list(range(n-1, -1, -1))):
        for shift in range(n):
            order = tuple(base[shift:] + base[:shift])
            if order not in seen:
                seen.add(order)
                yield order


def main():
    print("\n" + "=" * 72)
    print("EXHAUSTIVE PRIVILEGE RULE SEARCH AT PROC 1")
    print("=" * 72)

    non_binary = [p for p, m in enumerate(MS) if m > 2]
    target_ranges = [range(1, MS[p]) for p in non_binary]

    cycles_pool = []
    cycle_set_dedup = set()

    count = 0
    for combo in cartesian(*target_ranges):
        targets = {p: 1 for p, m in enumerate(MS) if m == 2}
        for idx, p in enumerate(non_binary):
            targets[p] = combo[idx]
        for order in cyclic_orders(N):
            for ret_same in (True, False):
                cycle = build_sweep_cycle(MS, order, targets, ret_same)
                if cycle is not None:
                    key = frozenset(cycle)
                    if key not in cycle_set_dedup:
                        cycle_set_dedup.add(key)
                        cycles_pool.append(cycle)
                        count += 1
                if count >= 300:
                    break
            if count >= 300:
                break
        if count >= 300:
            break

    for base in [list(range(N)) + list(range(N-2, 0, -1)),
                 list(range(N-1, -1, -1)) + list(range(1, N-1))]:
        for shift in range(len(base)):
            pattern = base[shift:] + base[:shift]
            cycle, movers = build_bounce_cycle(MS, pattern)
            if cycle is not None:
                key = frozenset(cycle)
                if key not in cycle_set_dedup:
                    cycle_set_dedup.add(key)
                    cycles_pool.append(cycle)

    print(f"Candidate good cycles: {len(cycles_pool)}")

    results = []
    start = time.time()

    for rule_idx, priv_set in enumerate(priv_subsets):
        p1_movers = set(priv_set)
        best_result = None
        tried = 0
        valid_found = False

        for cycle in cycles_pool:
            tables = build_tables_from_cycle_with_fixed_p1(cycle, p1_movers)
            if tables is None:
                continue
            tried += 1

            fs = make_fs(tables)
            result = verify_system(list(MS), fs, verbose=False)
            if result['valid']:
                valid_found = True
                best_result = ('VALID', len(cycle), result.get('cycle_length', '?'))
                break

            good_size, scc_count, scc_total = find_bad_sccs(MS, tables)
            if good_size is not None:
                if best_result is None or (scc_total, scc_count) < (best_result[0], best_result[1]):
                    best_result = (scc_total, scc_count, good_size)

        results.append({
            'rule_idx': rule_idx,
            'movers': sorted(p1_movers),
            'size': len(p1_movers),
            'tried': tried,
            'valid': valid_found,
            'best': best_result,
        })

        if (rule_idx + 1) % 10 == 0:
            elapsed = time.time() - start
            print(f"  Progress: {rule_idx+1}/{len(priv_subsets)} rules, {elapsed:.1f}s")

    elapsed = time.time() - start

    print(f"\nCompleted in {elapsed:.1f}s")
    print(f"\n{'='*100}")
    print(f"{'Rule':>4} | {'Size':>4} | {'Movers':<40} | {'Tried':>5} | {'Valid':>5} | Result")
    print(f"{'-'*100}")

    valid_count = 0
    for r in results:
        movers_str = str(r['movers'])
        if r['valid']:
            valid_count += 1
            best_str = f"VALID (cycle_len={r['best'][1]})"
        elif r['best'] is None:
            best_str = "NO COMPATIBLE CYCLE"
        else:
            best_str = f"bad_scc_nodes={r['best'][0]}, bad_sccs={r['best'][1]}, good={r['best'][2]}"
        print(f"{r['rule_idx']:>4} | {r['size']:>4} | {movers_str:<40} | {r['tried']:>5} | {'YES' if r['valid'] else 'no':>5} | {best_str}")

    print(f"\n{'='*72}")
    print(f"SUMMARY")
    print(f"Total privilege rules: {len(priv_subsets)}")
    print(f"Valid systems found: {valid_count}")
    print(f"Rules with no compatible cycle: {sum(1 for r in results if r['best'] is None)}")

    for size in range(1, 5):
        rules_of_size = [r for r in results if r['size'] == size]
        valid_of_size = [r for r in rules_of_size if r['valid']]
        no_compat = [r for r in rules_of_size if r['best'] is None]
        print(f"  Size {size}: {len(rules_of_size)} rules, {len(valid_of_size)} valid, {len(no_compat)} no compatible cycle")

    if valid_count == 0:
        print(f"\nOBSTRUCTION ANALYSIS:")
        scc_nodes_list = [r['best'][0] for r in results if r['best'] is not None and not r['valid']]
        if scc_nodes_list:
            print(f"  Min recurrent bad nodes across all rules: {min(scc_nodes_list)}")
            print(f"  Max recurrent bad nodes: {max(scc_nodes_list)}")
            good_sizes = [r['best'][2] for r in results if r['best'] is not None and not r['valid']]
            print(f"  Max good set size: {max(good_sizes)}")
            print(f"  Min good set size: {min(good_sizes)}")

        no_cycle = [r for r in results if r['best'] is None]
        if no_cycle:
            print(f"\n  Rules with NO compatible cycle ({len(no_cycle)}):")
            for r in no_cycle[:10]:
                print(f"    size={r['size']}: {r['movers']}")
            if len(no_cycle) > 10:
                print(f"    ... and {len(no_cycle)-10} more")

    print(f"\nAnswer: {'SOME privilege rules yield valid systems' if valid_count > 0 else 'NO privilege rule at proc 1 yields a valid system - failure is UNIVERSAL'}")


if __name__ == '__main__':
    main()
