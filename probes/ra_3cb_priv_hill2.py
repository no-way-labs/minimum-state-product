#!/usr/bin/env python3
"""Faster hill climbing: 500 steps, 3 seeds per pattern. Also try full random search."""

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


def cyclic_orders(n):
    seen = set()
    for base in (list(range(n)), list(range(n-1,-1,-1))):
        for shift in range(n):
            order = tuple(base[shift:] + base[:shift])
            if order not in seen:
                seen.add(order)
                yield order


def count_bad_sccs(ms, fs):
    """Lightweight: just count bad SCC nodes. Returns (dead, scc_total, good_size) or None."""
    n = len(ms)
    configs = ALL_CFGS
    priv_map = {}
    for c in configs:
        priv = []
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            if fs[i](L, S, R) != S:
                priv.append(i)
        priv_map[c] = priv

    dead = sum(1 for c in configs if not priv_map[c])
    if dead:
        return dead, -1, -1

    single_priv = {c for c in configs if len(priv_map[c]) == 1}
    succ = {}
    for c in single_priv:
        i = priv_map[c][0]
        lst = list(c); lst[i] = fs[i](c[(i-1)%n], c[i], c[(i+1)%n])
        succ[c] = (tuple(lst), i)

    good = set(single_priv)
    changed = True
    while changed:
        changed = False
        to_remove = {c for c in good if succ[c][0] not in good}
        if to_remove:
            good -= to_remove; changed = True

    # Find fair cycle
    visited = set()
    for start in good:
        if start in visited: continue
        path = []; path_set = set(); node = start
        while node not in visited and node not in path_set:
            path.append(node); path_set.add(node); node = succ[node][0]
        if node in path_set:
            cycle = path[path.index(node):]
            movers = {succ[c][1] for c in cycle}
            if movers == set(range(n)):
                rev = defaultdict(list)
                for c in single_priv: rev[succ[c][0]].append(c)
                queue = list(cycle); good = set(cycle)
                while queue:
                    nd = queue.pop()
                    for pred in rev[nd]:
                        if pred not in good: good.add(pred); queue.append(pred)

                # Count bad SCCs
                bad = set(configs) - good
                adj = defaultdict(list)
                for c in bad:
                    for p in priv_map[c]:
                        lst = list(c); lst[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
                        nxt = tuple(lst)
                        if nxt in bad:
                            adj[c].append(nxt)

                # Tarjan
                idx_c = [0]; stack = []; on_s = set()
                ix = {}; ll = {}; sccs = []
                def sc(v):
                    work = [(v, 0)]
                    ix[v] = ll[v] = idx_c[0]; idx_c[0] += 1
                    stack.append(v); on_s.add(v)
                    while work:
                        nd, si = work[-1]; su = adj.get(nd, [])
                        if si < len(su):
                            work[-1] = (nd, si+1); w = su[si]
                            if w not in ix:
                                ix[w] = ll[w] = idx_c[0]; idx_c[0] += 1
                                stack.append(w); on_s.add(w); work.append((w, 0))
                            elif w in on_s: ll[nd] = min(ll[nd], ix[w])
                        else:
                            if ll[nd] == ix[nd]:
                                scc = []
                                while True:
                                    w = stack.pop(); on_s.discard(w); scc.append(w)
                                    if w == nd: break
                                if len(scc) > 1 or (scc[0] in adj and scc[0] in adj.get(scc[0], [])):
                                    sccs.append(scc)
                            work.pop()
                            if work: ll[work[-1][0]] = min(ll[work[-1][0]], ll[nd])
                for v in bad:
                    if v not in ix: sc(v)
                return 0, sum(len(s) for s in sccs), len(good)
        visited.update(path)
    return 0, -1, -1  # no fair cycle


def build_tables_gt(cycle, p1_movers):
    n = N; ms = MS; good_set = set(cycle)
    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]; c_next = cycle[(idx+1)%len(cycle)]
        diffs = [p for p in range(n) if c[p] != c_next[p]]
        if len(diffs) != 1: return None
        mover = diffs[0]
        for p in range(n):
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            key = (p, L, S, R)
            out = c_next[p] if p == mover else S
            if key in det and det[key] != out: return None
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
        for L in range(ms[(p-1)%n]):
            for S in range(ms[p]):
                for R in range(ms[(p+1)%n]):
                    key = (p, L, S, R)
                    if key not in det: free_entries.append(key)
    for key in free_entries:
        if key[0] == 1:
            triple = (key[1], key[2], key[3])
            comp[key] = 1-key[2] if triple in p1_movers else key[2]
    ti = defaultdict(list)
    for c in non_good:
        for p in range(n):
            key = (p, c[(p-1)%n], c[p], c[(p+1)%n])
            if key not in det and key[0] != 1: ti[key].append(c)
    for key in free_entries:
        if key[0] == 1: continue
        p = key[0]; matching = ti.get(key, [])
        best_out = key[2]; best_good = 0; best_ng = 0
        for out in range(ms[p]):
            if out == key[2]: continue
            gc = ng = 0
            for c in matching:
                new_c = c[:p] + (out,) + c[p+1:]
                if new_c in good_set: gc += 1
                elif new_c in non_good_set: ng += 1
            if gc > best_good or (gc == best_good and ng < best_ng):
                best_out = out; best_good = gc; best_ng = ng
        comp[key] = best_out
    for c in ALL_CFGS:
        has_priv = any(comp.get((p, c[(p-1)%n], c[p], c[(p+1)%n]), c[p]) != c[p] for p in range(n))
        if has_priv: continue
        for p in range(n):
            key = (p, c[(p-1)%n], c[p], c[(p+1)%n])
            if key in det: continue
            if p == 1:
                if (key[1], key[2], key[3]) in p1_movers:
                    comp[key] = 1-key[2]; break
                continue
            for out in range(ms[p]):
                if out != c[p]:
                    comp[key] = out; break
            else: continue
            break
    tables = []
    for p in range(n):
        table = {}
        for L in range(ms[(p-1)%n]):
            for S in range(ms[p]):
                for R in range(ms[(p+1)%n]):
                    key = (p, L, S, R)
                    table[(L, S, R)] = comp.get(key, S)
        tables.append(table)
    return tables


def main():
    fire_patterns = [
        {(0, 1, 1), (1, 0, 0)},
        {(0, 0, 0), (1, 1, 1)},
        {(0, 1, 0), (1, 0, 1)},
    ]

    non_binary = [p for p, m in enumerate(MS) if m > 2]
    ms = MS

    print("=" * 72)
    print("HILL CLIMBING (FAST) + RANDOM MUTATION")
    print("=" * 72)

    for fi, fire_set in enumerate(fire_patterns):
        print(f"\n--- Fire pattern {fi}: {sorted(fire_set)} ---")

        # Find compatible cycle
        found_cycle = None
        for combo in cartesian(*[range(1, ms[p]) for p in non_binary]):
            targets = {p: 1 for p, m in enumerate(ms) if m == 2}
            for idx, p in enumerate(non_binary): targets[p] = combo[idx]
            for order in cyclic_orders(N):
                for ret in (True, False):
                    cycle = build_sweep_cycle(ms, order, targets, ret)
                    if cycle is None: continue
                    mf = set(); ms_set = set()
                    for idx in range(len(cycle)):
                        c = cycle[idx]; cn = cycle[(idx+1)%len(cycle)]
                        diffs = [p for p in range(N) if c[p] != cn[p]]
                        mover = diffs[0]; triple = (c[0], c[1], c[2])
                        if mover == 1: mf.add(triple)
                        else: ms_set.add(triple)
                    if mf == fire_set and not (ms_set & fire_set):
                        found_cycle = cycle; break
                if found_cycle: break
            if found_cycle: break

        if not found_cycle:
            print("  No compatible cycle!"); continue

        seed_tables = build_tables_gt(found_cycle, fire_set)
        if seed_tables is None:
            print("  GT failed!"); continue

        fs = make_fs(seed_tables)
        dead, scc_total, good_size = count_bad_sccs(ms, fs)
        print(f"  GT baseline: dead={dead}, scc_total={scc_total}, good={good_size}")

        # Hill climb
        rng = random.Random(42)
        proc_keys = []
        for p in range(N):
            if p == 1: continue
            for L in range(ms[(p-1)%N]):
                for S in range(ms[p]):
                    for R in range(ms[(p+1)%N]):
                        proc_keys.append((p, L, S, R))

        best_scc = scc_total
        t0 = time.time()
        for seed in range(5):
            rng = random.Random(seed)
            tables = [dict(t) for t in seed_tables]
            cur_scc = scc_total

            for step in range(500):
                pk = rng.choice(proc_keys)
                p = pk[0]
                old_val = tables[p][(pk[1], pk[2], pk[3])]
                opts = [v for v in range(ms[p]) if v != old_val]
                new_val = rng.choice(opts)
                tables[p][(pk[1], pk[2], pk[3])] = new_val

                fs = make_fs(tables)
                d, st, gs = count_bad_sccs(ms, fs)
                if d == 0 and st == 0:
                    print(f"    VALID at seed={seed} step={step}!")
                    # Verify properly
                    result = verify_system(list(ms), fs, verbose=False)
                    print(f"    verify_system: valid={result['valid']}")
                    break
                if d == 0 and st >= 0 and st <= cur_scc:
                    cur_scc = st
                else:
                    tables[p][(pk[1], pk[2], pk[3])] = old_val

            if cur_scc < best_scc:
                best_scc = cur_scc

        elapsed = time.time() - t0
        print(f"  Hill climb best SCC total: {best_scc} ({elapsed:.1f}s)")

        # Also random mutation search (no hill structure)
        t0 = time.time()
        found_valid = False
        for trial in range(2000):
            rng2 = random.Random(trial + 10000)
            tables = [dict(t) for t in seed_tables]
            # Make 1-4 random mutations
            for _ in range(rng2.randint(1, 4)):
                pk = rng2.choice(proc_keys)
                p = pk[0]
                tables[p][(pk[1], pk[2], pk[3])] = rng2.randrange(ms[p])
            fs = make_fs(tables)
            result = verify_system(list(ms), fs, verbose=False)
            if result['valid']:
                print(f"    VALID at mutation trial {trial}!")
                found_valid = True
                break
        if not found_valid:
            print(f"  Random mutation (2000 trials): no valid system ({time.time()-t0:.1f}s)")

    print("\n" + "=" * 72)
    print("CONCLUSION")
    print("=" * 72)
    print("If no valid system found: convergence failure is NOT an artifact of")
    print("good-targeting -- it persists across random completions, hill climbing,")
    print("and random mutation. The obstruction is structural to ms=(2,2,2,3,3,3,3,4).")


if __name__ == '__main__':
    main()
