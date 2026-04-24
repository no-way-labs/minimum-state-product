#!/usr/bin/env python3
"""Hill-climbing search to minimize bad SCCs, across ALL 3 compatible rule families.
Also: try ALL 11 compatible rules with multiple cycle types.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import defaultdict
import random
import time

from verifier import all_configs, apply_move, privileged_set, verify_system

MS = (2, 2, 2, 3, 3, 3, 3, 4)
N = len(MS)
ALL_CFGS = list(cartesian(*(range(m) for m in MS)))


def make_fs(tables):
    fs = []
    for table in tables:
        def make_f(t):
            def f(L, S, R): return t[(L, S, R)]
            return f
        fs.append(make_f(table))
    return fs


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


def build_tables_gt(cycle, p1_movers):
    """Good-targeting completion with proc 1 rule fixed."""
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
            L = c[(p-1) % n]; S = c[p]; R = c[(p+1) % n]
            key = (p, L, S, R)
            out = c_next[p] if p == mover else S
            if key in det and det[key] != out:
                return None
            det[key] = out

    for key, out in det.items():
        if key[0] == 1:
            triple = (key[1], key[2], key[3])
            if triple in p1_movers:
                if out != 1 - key[2]: return None
            else:
                if out != key[2]: return None

    comp = dict(det)
    non_good = [c for c in ALL_CFGS if c not in good_set]
    non_good_set = set(non_good)

    free_entries = []
    for p in range(n):
        m_L = ms[(p-1) % n]; m_S = ms[p]; m_R = ms[(p+1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in det:
                        free_entries.append(key)

    for key in free_entries:
        if key[0] == 1:
            triple = (key[1], key[2], key[3])
            comp[key] = 1 - key[2] if triple in p1_movers else key[2]

    triple_index = defaultdict(list)
    for c in non_good:
        for p in range(n):
            key = (p, c[(p-1) % n], c[p], c[(p+1) % n])
            if key not in det and key[0] != 1:
                triple_index[key].append(c)

    edge_costs = {}
    for key in free_entries:
        if key[0] == 1: continue
        p = key[0]
        matching = triple_index.get(key, [])
        best_out = key[2]  # self_state
        best_good = 0; best_ng = 0
        for out in range(ms[p]):
            if out == key[2]:
                edge_costs[(key, out)] = 0
                continue
            gc = ng = 0
            for c in matching:
                new_c = c[:p] + (out,) + c[p+1:]
                if new_c in good_set: gc += 1
                elif new_c in non_good_set: ng += 1
            edge_costs[(key, out)] = ng
            if gc > best_good or (gc == best_good and ng < best_ng):
                best_out = out; best_good = gc; best_ng = ng
        comp[key] = best_out

    for c in ALL_CFGS:
        has_priv = False
        for p in range(n):
            key = (p, c[(p-1) % n], c[p], c[(p+1) % n])
            if comp.get(key, c[p]) != c[p]:
                has_priv = True; break
        if has_priv: continue
        best_key = None; best_cost = float('inf'); best_out = None
        for p in range(n):
            key = (p, c[(p-1) % n], c[p], c[(p+1) % n])
            if key in det: continue
            if p == 1:
                triple = (key[1], key[2], key[3])
                if triple in p1_movers:
                    out = 1 - key[2]
                    cost = edge_costs.get((key, out), 0)
                    if cost < best_cost:
                        best_cost = cost; best_key = key; best_out = out
                continue
            for out in range(ms[p]):
                if out == c[p]: continue
                cost = edge_costs.get((key, out), 0)
                if cost < best_cost:
                    best_cost = cost; best_key = key; best_out = out
        if best_key is not None:
            comp[best_key] = best_out

    tables = []
    for p in range(n):
        table = {}
        m_L = ms[(p-1) % n]; m_S = ms[p]; m_R = ms[(p+1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    table[(L, S, R)] = comp.get(key, S)
        tables.append(table)
    return tables


def score_tables(ms, tables):
    """Score: (dead, no_fair, scc_total). Lower is better. 0 = valid."""
    fs = make_fs(tables)
    result = verify_system(list(ms), fs, verbose=False)
    if result['valid']:
        return (0, 0, 0), True

    configs = list(all_configs(ms))
    priv_map = {c: privileged_set(c, fs, ms) for c in configs}
    dead = sum(1 for c in configs if len(priv_map[c]) == 0)
    if dead:
        return (dead, 0, 0), False

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
            good -= to_remove; changed = True

    fair = False
    visited = set()
    for start in good:
        if start in visited: continue
        path = []; path_set = set(); node = start
        while node not in visited and node not in path_set:
            path.append(node); path_set.add(node); node = succ[node][0]
        if node in path_set:
            cycle = path[path.index(node):]
            movers = {succ[c][1] for c in cycle}
            if movers == set(range(len(ms))):
                fair = True
                rev = defaultdict(list)
                for c in single_priv: rev[succ[c][0]].append(c)
                queue = list(cycle); good = set(cycle)
                while queue:
                    nd = queue.pop()
                    for pred in rev[nd]:
                        if pred not in good: good.add(pred); queue.append(pred)
                break
        visited.update(path)

    if not fair:
        return (0, 1, 0), False

    bad = set(configs) - good
    adj = defaultdict(list)
    for c in bad:
        for p in priv_map[c]:
            nxt = apply_move(c, p, fs, ms)
            if nxt in bad: adj[c].append(nxt)

    # Quick SCC count via DFS
    idx_counter = [0]; stack = []; on_stack = set()
    index_map = {}; lowlink = {}; sccs = []
    def strongconnect(v):
        work = [(v, 0)]
        index_map[v] = lowlink[v] = idx_counter[0]; idx_counter[0] += 1
        stack.append(v); on_stack.add(v)
        while work:
            node, si = work[-1]; succs = adj.get(node, [])
            if si < len(succs):
                work[-1] = (node, si+1); w = succs[si]
                if w not in index_map:
                    index_map[w] = lowlink[w] = idx_counter[0]; idx_counter[0] += 1
                    stack.append(w); on_stack.add(w); work.append((w, 0))
                elif w in on_stack: lowlink[node] = min(lowlink[node], index_map[w])
            else:
                if lowlink[node] == index_map[node]:
                    scc = []
                    while True:
                        w = stack.pop(); on_stack.discard(w); scc.append(w)
                        if w == node: break
                    if len(scc) > 1 or (scc[0] in adj and scc[0] in adj.get(scc[0], [])):
                        sccs.append(scc)
                work.pop()
                if work: lowlink[work[-1][0]] = min(lowlink[work[-1][0]], lowlink[node])
    for v in bad:
        if v not in index_map: strongconnect(v)
    scc_total = sum(len(s) for s in sccs)
    return (0, 0, scc_total), False


def hill_climb(ms, seed_tables, p1_movers, steps=2000, seed=42):
    """Hill climb on non-proc-1 entries to minimize bad SCCs."""
    rng = random.Random(seed)
    n = len(ms)
    tables = [dict(t) for t in seed_tables]

    # Determine which entries are free (not proc 1, not cycle-determined)
    # We'll just mutate any non-proc-1 entry
    proc_keys = []
    for p in range(n):
        if p == 1: continue
        keys = []
        m_L = ms[(p-1) % n]; m_S = ms[p]; m_R = ms[(p+1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    keys.append((p, L, S, R))
        proc_keys.extend(keys)

    best_score, valid = score_tables(ms, tables)
    if valid:
        return tables, best_score, True

    for step in range(steps):
        pk = rng.choice(proc_keys)
        p = pk[0]
        old_val = tables[p][(pk[1], pk[2], pk[3])]
        opts = [v for v in range(ms[p]) if v != old_val]
        new_val = rng.choice(opts)
        tables[p][(pk[1], pk[2], pk[3])] = new_val

        new_score, valid = score_tables(ms, tables)
        if valid:
            return tables, new_score, True
        if new_score <= best_score:
            best_score = new_score
        else:
            tables[p][(pk[1], pk[2], pk[3])] = old_val

    return tables, best_score, False


def cyclic_orders(n):
    seen = set()
    for base in (list(range(n)), list(range(n-1,-1,-1))):
        for shift in range(n):
            order = tuple(base[shift:] + base[:shift])
            if order not in seen:
                seen.add(order)
                yield order


def main():
    # The 3 anti-diagonal fire patterns
    fire_patterns = [
        {(0, 1, 1), (1, 0, 0)},  # 288 cycles
        {(0, 0, 0), (1, 1, 1)},  # 48 cycles
        {(0, 1, 0), (1, 0, 1)},  # 48 cycles
    ]

    # For each pattern, find a compatible cycle
    non_binary = [p for p, m in enumerate(MS) if m > 2]

    print("=" * 72)
    print("HILL CLIMBING ACROSS ALL 3 RULE FAMILIES")
    print("=" * 72)

    for fi, fire_set in enumerate(fire_patterns):
        print(f"\n--- Fire pattern {fi}: {sorted(fire_set)} ---")

        # Find compatible cycle
        found_cycle = None
        for combo in cartesian(*[range(1, MS[p]) for p in non_binary]):
            targets = {p: 1 for p, m in enumerate(MS) if m == 2}
            for idx, p in enumerate(non_binary):
                targets[p] = combo[idx]
            for order in cyclic_orders(N):
                for ret in (True, False):
                    cycle = build_sweep_cycle(MS, order, targets, ret)
                    if cycle is None: continue
                    # Check compatibility
                    mf = set(); ms_set = set()
                    for idx in range(len(cycle)):
                        c = cycle[idx]; cn = cycle[(idx+1)%len(cycle)]
                        diffs = [p for p in range(N) if c[p] != cn[p]]
                        mover = diffs[0]
                        triple = (c[0], c[1], c[2])
                        if mover == 1: mf.add(triple)
                        else: ms_set.add(triple)
                    if mf == fire_set and not (ms_set & fire_set):
                        found_cycle = cycle
                        break
                if found_cycle: break
            if found_cycle: break

        if not found_cycle:
            print("  No compatible cycle found!")
            continue

        print(f"  Cycle length: {len(found_cycle)}")

        # Build good-targeting seed
        seed_tables = build_tables_gt(found_cycle, fire_set)
        if seed_tables is None:
            print("  Good-targeting failed!")
            continue

        base_score, valid = score_tables(MS, seed_tables)
        print(f"  Good-targeting score: {base_score}, valid={valid}")

        if valid:
            print("  VALID SYSTEM FOUND!")
            continue

        # Hill climb from this seed
        best_score = base_score
        for seed in range(10):
            tables, sc, valid = hill_climb(MS, seed_tables, fire_set, steps=3000, seed=seed)
            if valid:
                print(f"  VALID at hill-climb seed {seed}!")
                break
            if sc < best_score:
                best_score = sc
        print(f"  Best hill-climb score (10 seeds x 3000 steps): {best_score}")

    print("\n" + "=" * 72)
    print("CONCLUSION")
    print("=" * 72)


if __name__ == '__main__':
    main()
