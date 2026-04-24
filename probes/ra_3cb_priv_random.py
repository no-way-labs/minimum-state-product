#!/usr/bin/env python3
"""Test whether the (384,75,42) convergence obstruction is structural
or just an artifact of good-targeting completion.

Try many random completions for the non-proc-1 free entries.
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
            def f(L, S, R):
                return t[(L, S, R)]
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


def find_bad_sccs_from_tables(ms, tables):
    fs = make_fs(tables)
    n = len(ms)
    configs = list(all_configs(ms))
    priv_map = {c: privileged_set(c, fs, ms) for c in configs}

    dead = [c for c in configs if len(priv_map[c]) == 0]
    if dead:
        return len(dead), -1, -1, -1

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

    # Find fair cycle
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
        return 0, -1, -1, len(good)

    bad = set(configs) - good
    adj = defaultdict(list)
    for c in bad:
        for p in priv_map[c]:
            nxt = apply_move(c, p, fs, ms)
            if nxt in bad:
                adj[c].append(nxt)

    # Tarjan
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
    return 0, len(sccs), scc_total, len(good)


def random_completion_with_fixed_p1(cycle, p1_movers, rng):
    """Build tables with proc 1 rule fixed, other procs random."""
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

    # Check p1 consistency
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

    # Fill proc 1 free entries per rule
    for L in range(ms[0]):
        for S in range(ms[1]):
            for R in range(ms[2]):
                key = (1, L, S, R)
                if key not in det:
                    triple = (L, S, R)
                    if triple in p1_movers:
                        comp[key] = 1 - S
                    else:
                        comp[key] = S

    # Fill other procs RANDOMLY
    for p in range(n):
        if p == 1:
            continue
        m_L = ms[(p-1) % n]
        m_S = ms[p]
        m_R = ms[(p+1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in det:
                        comp[key] = rng.randrange(m_S)

    # Liveness fix
    for c in ALL_CFGS:
        has_priv = False
        for p in range(n):
            key = (p, c[(p-1) % n], c[p], c[(p+1) % n])
            if comp.get(key, c[p]) != c[p]:
                has_priv = True
                break
        if has_priv:
            continue
        # Fix randomly
        free_procs = [p for p in range(n) if (p, c[(p-1)%n], c[p], c[(p+1)%n]) not in det]
        if not free_procs:
            continue
        p = rng.choice(free_procs)
        key = (p, c[(p-1) % n], c[p], c[(p+1) % n])
        if p == 1:
            triple = (key[1], key[2], key[3])
            if triple in p1_movers:
                comp[key] = 1 - key[2]
            # else can't fix via proc 1
        else:
            opts = [out for out in range(ms[p]) if out != c[p]]
            if opts:
                comp[key] = rng.choice(opts)

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


def main():
    # Pick a representative cycle and rule
    # Rule 24: [(0,1,1), (1,0,0)] -- the most popular pattern (288 cycles)
    p1_movers = {(0, 1, 1), (1, 0, 0)}

    # Build one representative cycle
    cycle = build_sweep_cycle(MS, tuple(range(N)),
                               {0:1, 1:1, 2:1, 3:1, 4:1, 5:1, 6:1, 7:1}, True)

    rng = random.Random(42)

    # First check if this cycle is compatible
    n = N
    must_fire = set()
    must_stay = set()
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        diffs = [p for p in range(n) if c[p] != c_next[p]]
        mover = diffs[0]
        L = c[0]; S = c[1]; R = c[2]
        triple = (L, S, R)
        if mover == 1:
            must_fire.add(triple)
        else:
            must_stay.add(triple)

    compat = all(t in p1_movers for t in must_fire) and all(t not in p1_movers for t in must_stay)
    print(f"Cycle fire={sorted(must_fire)}, stay={sorted(must_stay)}")
    print(f"Compatible with rule {sorted(p1_movers)}: {compat}")

    if not compat:
        # Try all cycles to find a compatible one
        for order in [tuple(range(N)), tuple(range(N-1,-1,-1))]:
            for combo_vals in cartesian(*[range(1, MS[p]) for p in range(N) if MS[p] > 2]):
                targets = {p: 1 for p, m in enumerate(MS) if m == 2}
                nb = [p for p, m in enumerate(MS) if m > 2]
                for idx, p in enumerate(nb):
                    targets[p] = combo_vals[idx]
                for ret in (True, False):
                    cy = build_sweep_cycle(MS, order, targets, ret)
                    if cy is None:
                        continue
                    mf = set()
                    ms_set = set()
                    for idx in range(len(cy)):
                        c = cy[idx]
                        cn = cy[(idx+1)%len(cy)]
                        diffs = [p for p in range(n) if c[p] != cn[p]]
                        mover = diffs[0]
                        triple = (c[0], c[1], c[2])
                        if mover == 1:
                            mf.add(triple)
                        else:
                            ms_set.add(triple)
                    if all(t in p1_movers for t in mf) and all(t not in p1_movers for t in ms_set):
                        cycle = cy
                        print(f"Found compatible cycle with fire={sorted(mf)}")
                        break
                else:
                    continue
                break
            else:
                continue
            break

    print(f"\nCycle length: {len(cycle)}")

    # Now try many random completions
    print("\n" + "=" * 72)
    print("RANDOM COMPLETION SEARCH (1000 trials)")
    print("=" * 72)

    results = defaultdict(int)
    valid_count = 0
    best_scc = float('inf')
    start = time.time()

    for trial in range(1000):
        tables = random_completion_with_fixed_p1(cycle, p1_movers, rng)
        if tables is None:
            results['incompatible'] += 1
            continue

        # Quick verify
        fs = make_fs(tables)
        result = verify_system(list(MS), fs, verbose=False)
        if result['valid']:
            valid_count += 1
            print(f"  VALID at trial {trial}!")
            continue

        dead, scc_count, scc_total, good_size = find_bad_sccs_from_tables(MS, tables)
        if dead > 0:
            results[f'dead={dead}'] += 1
        elif scc_count < 0:
            results['no_fair_cycle'] += 1
        else:
            key = f'scc={scc_total},sccs={scc_count},good={good_size}'
            results[key] += 1
            if scc_total < best_scc:
                best_scc = scc_total

    elapsed = time.time() - start
    print(f"\nElapsed: {elapsed:.1f}s")
    print(f"Valid systems found: {valid_count}")
    print(f"Best (min) SCC total: {best_scc}")
    print(f"\nResult distribution:")
    for key, count in sorted(results.items(), key=lambda x: -x[1]):
        print(f"  {count:>5} x {key}")


if __name__ == '__main__':
    main()
