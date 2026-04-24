#!/usr/bin/env python3
"""Definitive shadow test on TRUE witness cycles and tail candidates.

Unlike the previous probes, this one:

  * extracts the actual good cycle from the stored witness transition
    tables (verify_witnesses.py) via the single-privileged walk used
    by verify(),
  * computes the determined-entry dict from that exact cycle,
  * runs find_shadow (greedy forced walk) and iterative sink-kernel
    removal on the determined bad graph,
  * for the tails, uses an unfiltered DFS (find_short_cycles) that
    does NOT enforce mover adjacency, so we exhaust realistic
    candidate good cycles.

Question: does the witness's true cycle escape shadow (kernel empty /
find_shadow returns None), while every tail candidate has a shadow?
"""

from itertools import product as iproduct
from collections import defaultdict, Counter
import time


# ----------------------------------------------------------------------
# Witness rules — copied verbatim from verify_witnesses.py to avoid the
# side-effect __main__ block on import.
# ----------------------------------------------------------------------
def witness_n5():
    return (2, 2, 2, 3, 4), (
        {(0,0,0):1,(0,0,1):1,(0,1,0):1,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):0,(1,1,1):0,
         (2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0,(3,0,0):0,(3,0,1):0,(3,1,0):0,(3,1,1):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):1,(1,0,1):0,(1,1,0):1,(1,1,1):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,1,0):1,(0,1,1):0,(0,1,2):1,
         (1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):0,(1,1,2):0},
        {(0,0,0):0,(0,0,1):1,(0,0,2):1,(0,0,3):0,(0,1,0):2,(0,1,1):2,(0,1,2):2,(0,1,3):0,
         (0,2,0):2,(0,2,1):2,(0,2,2):2,(0,2,3):0,
         (1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,(1,1,0):1,(1,1,1):0,(1,1,2):0,(1,1,3):1,
         (1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):1},
        {(0,0,0):0,(0,0,1):0,(0,1,0):2,(0,1,1):2,(0,2,0):2,(0,2,1):2,(0,3,0):0,(0,3,1):0,
         (1,0,0):0,(1,0,1):0,(1,1,0):0,(1,1,1):0,(1,2,0):0,(1,2,1):0,(1,3,0):3,(1,3,1):0,
         (2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1,(2,2,0):3,(2,2,1):2,(2,3,0):3,(2,3,1):0},
    )


def witness_n7():
    return (3, 2, 2, 2, 3, 4, 3), (
        {(0,0,0):1,(0,0,1):0,(0,1,0):2,(0,1,1):0,(0,2,0):2,(0,2,1):2,
         (1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):2,(1,2,1):2,
         (2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):1,(2,2,0):2,(2,2,1):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):0,(1,1,1):0,
         (2,0,0):1,(2,0,1):0,(2,1,0):1,(2,1,1):1},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):1,(1,0,1):0,(1,1,0):1,(1,1,1):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,
         (1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):0,(1,1,2):1},
        {(0,0,0):0,(0,0,1):1,(0,0,2):0,(0,0,3):0,(0,1,0):2,(0,1,1):1,(0,1,2):0,(0,1,3):0,
         (0,2,0):2,(0,2,1):1,(0,2,2):2,(0,2,3):2,
         (1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,(1,1,0):1,(1,1,1):0,(1,1,2):0,(1,1,3):0,
         (1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):2},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):3,(0,1,1):1,(0,1,2):1,
         (0,2,0):2,(0,2,1):0,(0,2,2):1,(0,3,0):3,(0,3,1):0,(0,3,2):1,
         (1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):2,(1,1,1):3,(1,1,2):0,
         (1,2,0):2,(1,2,1):0,(1,2,2):0,(1,3,0):0,(1,3,1):3,(1,3,2):1,
         (2,0,0):1,(2,0,1):2,(2,0,2):0,(2,1,0):1,(2,1,1):1,(2,1,2):2,
         (2,2,0):0,(2,2,1):2,(2,2,2):2,(2,3,0):0,(2,3,1):0,(2,3,2):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):1,(0,1,1):2,(0,1,2):1,(0,2,0):0,(0,2,1):2,(0,2,2):0,
         (1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):1,(1,1,2):0,(1,2,0):1,(1,2,1):0,(1,2,2):0,
         (2,0,0):0,(2,0,1):0,(2,0,2):0,(2,1,0):0,(2,1,1):0,(2,1,2):2,(2,2,0):0,(2,2,1):0,(2,2,2):2,
         (3,0,0):2,(3,0,1):0,(3,0,2):1,(3,1,0):1,(3,1,1):1,(3,1,2):1,(3,2,0):2,(3,2,1):0,(3,2,2):0},
    )


def witness_n8():
    return (2, 2, 3, 4, 3, 3, 2, 3), (
        {(0,0,0):1,(0,0,1):0,(0,1,0):1,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):1,(1,1,1):1,
         (2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,
         (1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):0,(1,1,2):1},
        {(0,0,0):0,(0,0,1):1,(0,0,2):0,(0,0,3):0,(0,1,0):2,(0,1,1):1,(0,1,2):0,(0,1,3):0,
         (0,2,0):2,(0,2,1):1,(0,2,2):2,(0,2,3):1,
         (1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,(1,1,0):1,(1,1,1):0,(1,1,2):2,(1,1,3):0,
         (1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):3,(0,1,0):3,(0,1,1):1,(0,1,2):1,
         (0,2,0):2,(0,2,1):0,(0,2,2):0,(0,3,0):3,(0,3,1):0,(0,3,2):1,
         (1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):2,(1,1,1):3,(1,1,2):0,
         (1,2,0):2,(1,2,1):0,(1,2,2):0,(1,3,0):0,(1,3,1):3,(1,3,2):0,
         (2,0,0):1,(2,0,1):2,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0,
         (2,2,0):0,(2,2,1):2,(2,2,2):2,(2,3,0):0,(2,3,1):0,(2,3,2):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):1,(0,1,1):0,(0,1,2):0,(0,2,0):0,(0,2,1):0,(0,2,2):0,
         (1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):1,(1,2,0):0,(1,2,1):1,(1,2,2):1,
         (2,0,0):0,(2,0,1):0,(2,0,2):0,(2,1,0):2,(2,1,1):0,(2,1,2):0,(2,2,0):2,(2,2,1):0,(2,2,2):0,
         (3,0,0):1,(3,0,1):2,(3,0,2):0,(3,1,0):1,(3,1,1):1,(3,1,2):1,(3,2,0):0,(3,2,1):2,(3,2,2):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):1,(0,1,1):0,(0,2,0):0,(0,2,1):0,
         (1,0,0):0,(1,0,1):0,(1,1,0):2,(1,1,1):0,(1,2,0):2,(1,2,1):2,
         (2,0,0):1,(2,0,1):0,(2,1,0):1,(2,1,1):1,(2,2,0):0,(2,2,1):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,1,0):0,(0,1,1):0,(0,1,2):1,
         (1,0,0):0,(1,0,1):0,(1,0,2):1,(1,1,0):0,(1,1,1):1,(1,1,2):1,
         (2,0,0):1,(2,0,1):0,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):2,(0,2,0):2,(0,2,1):2,
         (1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):1,(1,2,1):2},
    )


def witness_n6():
    return (2, 2, 2, 4, 3, 3), (
        {(0,0,0):1,(0,0,1):0,(0,1,0):1,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):0,(1,1,1):0,
         (2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):1},
        {(0,0,0):0,(0,0,1):1,(0,0,2):0,(0,0,3):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,1,3):0,
         (1,0,0):1,(1,0,1):0,(1,0,2):1,(1,0,3):0,(1,1,0):1,(1,1,1):0,(1,1,2):1,(1,1,3):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):3,(0,1,0):2,(0,1,1):3,(0,1,2):1,(0,2,0):2,(0,2,1):2,(0,2,2):1,
         (0,3,0):2,(0,3,1):0,(0,3,2):3,
         (1,0,0):1,(1,0,1):2,(1,0,2):0,(1,1,0):1,(1,1,1):1,(1,1,2):0,(1,2,0):3,(1,2,1):2,(1,2,2):2,
         (1,3,0):3,(1,3,1):0,(1,3,2):0},
        {(0,0,0):0,(0,0,1):2,(0,0,2):0,(0,1,0):1,(0,1,1):2,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):2,
         (1,0,0):0,(1,0,1):2,(1,0,2):0,(1,1,0):0,(1,1,1):0,(1,1,2):0,(1,2,0):0,(1,2,1):2,(1,2,2):2,
         (2,0,0):0,(2,0,1):1,(2,0,2):1,(2,1,0):2,(2,1,1):1,(2,1,2):2,(2,2,0):2,(2,2,1):2,(2,2,2):2,
         (3,0,0):1,(3,0,1):0,(3,0,2):0,(3,1,0):1,(3,1,1):0,(3,1,2):1,(3,2,0):0,(3,2,1):0,(3,2,2):1},
        {(0,0,0):0,(0,0,1):0,(0,1,0):1,(0,1,1):0,(0,2,0):0,(0,2,1):0,
         (1,0,0):0,(1,0,1):0,(1,1,0):2,(1,1,1):1,(1,2,0):2,(1,2,1):0,
         (2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1,(2,2,0):2,(2,2,1):0},
    )


# ----------------------------------------------------------------------
# Witness cycle extraction — via single-privileged walk.
# Same technique as verify() in verify_witnesses.py.
# ----------------------------------------------------------------------
def extract_witness_cycle(ms, rules):
    n = len(ms)
    all_configs = list(iproduct(*[range(m) for m in ms]))

    def priv(cfg):
        out = []
        for i in range(n):
            L = cfg[(i - 1) % n]
            S = cfg[i]
            R = cfg[(i + 1) % n]
            if rules[i][(L, S, R)] != S:
                out.append(i)
        return out

    def move(cfg, p):
        L = cfg[(p - 1) % n]
        S = cfg[p]
        R = cfg[(p + 1) % n]
        new_S = rules[p][(L, S, R)]
        lst = list(cfg)
        lst[p] = new_S
        return tuple(lst)

    single = {}
    for cfg in all_configs:
        pv = priv(cfg)
        if len(pv) == 1:
            single[cfg] = (move(cfg, pv[0]), pv[0])

    # Walk single-privileged configs to find the cycle.
    visited_global = set()
    for start in single:
        if start in visited_global:
            continue
        path = [start]
        movers = []
        visited = {start}
        cur = start
        while True:
            if cur not in single:
                break
            nxt, mover = single[cur]
            movers.append(mover)
            if nxt == start:
                visited_global.update(visited)
                return path, movers
            if nxt in visited:
                break
            visited.add(nxt)
            visited_global.add(nxt)
            path.append(nxt)
            cur = nxt
    return None, None


# ----------------------------------------------------------------------
# Determined-entry extraction from a good cycle.
# ----------------------------------------------------------------------
def extract_det(cycle, ms, n):
    det = {}
    L = len(cycle)
    for idx in range(L):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return None
        mover = diffs[0]
        Lm = c[(mover - 1) % n]
        Sm = c[mover]
        Rm = c[(mover + 1) % n]
        key_m = (mover, Lm, Sm, Rm)
        if key_m in det and det[key_m] != c_next[mover]:
            return None
        det[key_m] = c_next[mover]
        for i in range(n):
            if i == mover:
                continue
            Li = c[(i - 1) % n]
            Si = c[i]
            Ri = c[(i + 1) % n]
            key_i = (i, Li, Si, Ri)
            if key_i in det and det[key_i] != Si:
                return None
            det[key_i] = Si
    return det


# ----------------------------------------------------------------------
# Shadow, sink-kernel, SCC on the determined bad graph.
# ----------------------------------------------------------------------
def build_forced_graph(ms, n, det, good_set):
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)
    adj = defaultdict(list)
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


def sink_kernel(non_good, adj):
    remaining = set(non_good)
    rounds = 0
    while True:
        sinks = set()
        for c in remaining:
            has_out = False
            for tgt, _ in adj.get(c, []):
                if tgt in remaining:
                    has_out = True
                    break
            if not has_out:
                sinks.add(c)
        if not sinks:
            break
        remaining -= sinks
        rounds += 1
    return remaining, rounds


def find_shadow_greedy(cycle, det, ms, n):
    """Greedy shadow: walk from each non-good start following forced
    moves, return the first detected cycle or None."""
    good_set = set(cycle)
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    for start in non_good:
        config = start
        visited = {}
        path = []
        for step in range(500):
            if config in good_set:
                break
            if config in visited:
                return path[visited[config]:]
            visited[config] = len(path)
            path.append(config)
            forced = []
            for j in range(n):
                Lj = config[(j - 1) % n]
                Sj = config[j]
                Rj = config[(j + 1) % n]
                key = (j, Lj, Sj, Rj)
                if key in det and det[key] != Sj:
                    forced.append((j, det[key]))
            if not forced:
                break
            moved = False
            for proc, new_val in forced:
                nc = list(config)
                nc[proc] = new_val
                nc = tuple(nc)
                if nc not in good_set:
                    config = nc
                    moved = True
                    break
            if not moved:
                break
    return None


# ----------------------------------------------------------------------
# Unfiltered candidate enumerator for tails — no adjacency filter.
# Copied from shadow_cycle_proof.py's find_short_cycles.
# ----------------------------------------------------------------------
def check_cycle_consistency(cycle_configs, n, ms):
    L = len(cycle_configs)
    required = {}
    for idx in range(L):
        c = cycle_configs[idx]
        c_next = cycle_configs[(idx + 1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return False, {}, "non-single mover"
        mover = diffs[0]
        Li = c[(mover - 1) % n]
        Si = c[mover]
        Ri = c[(mover + 1) % n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            return False, {}, "mover conflict"
        required[key] = S_new
        for i in range(n):
            if i != mover:
                Li = c[(i - 1) % n]
                Si2 = c[i]
                Ri = c[(i + 1) % n]
                key = (i, Li, Si2, Ri)
                if key in required and required[key] != Si2:
                    return False, {}, "non-mover conflict"
                required[key] = Si2
    return True, required, "OK"


def find_short_cycles(start, ms, max_length, max_found=500, time_budget=30.0):
    n = len(ms)
    found = []
    t0 = time.time()

    def dfs(path, movers_used):
        if len(found) >= max_found:
            return
        if time.time() - t0 > time_budget:
            return
        config = path[-1]
        if len(path) >= n * 2 and len(movers_used) == n:
            for proc in range(n):
                for new_val in range(ms[proc]):
                    if new_val == config[proc]:
                        continue
                    new_config = list(config)
                    new_config[proc] = new_val
                    if tuple(new_config) == start:
                        ok, req, msg = check_cycle_consistency(
                            list(path), n, ms)
                        if ok:
                            found.append(list(path))
        if len(path) >= max_length:
            return
        visited = set(path)
        for proc in range(n):
            for new_val in range(ms[proc]):
                if new_val == config[proc]:
                    continue
                new_config = list(config)
                new_config[proc] = new_val
                nc = tuple(new_config)
                if nc in visited:
                    continue
                dfs(path + [nc], movers_used | {proc})

    dfs([start], set())
    return found


# ----------------------------------------------------------------------
# Probe runners.
# ----------------------------------------------------------------------
def test_witness(label, ms_rules_fn):
    ms, rules = ms_rules_fn()
    n = len(ms)
    print(f"\n===== WITNESS {label}  n={n}  ms={ms} =====")
    cycle, movers = extract_witness_cycle(ms, rules)
    if cycle is None:
        print("  FAILED to extract witness cycle")
        return
    print(f"  good cycle length: {len(cycle)}")
    print(f"  mover sequence: {movers}")
    # classify
    sweep = list(range(n))
    L = len(movers)
    ctype = "other"
    if L % n == 0 and movers == sweep * (L // n):
        ctype = "sweep"
    elif L % n == 0 and movers == list(range(n - 1, -1, -1)) * (L // n):
        ctype = "rev_sweep"
    else:
        bounce = list(range(n)) + list(range(n - 2, 0, -1))
        for r in range(1, 10):
            prefix = (bounce * r)[:L]
            if len(prefix) == L and movers == prefix:
                ctype = "bounce"
                break
    print(f"  cycle type: {ctype}")

    det = extract_det(cycle, ms, n)
    if det is None:
        print("  FAILED to extract determined entries (inconsistent)")
        return
    print(f"  |det|: {len(det)} forced entries")

    good_set = set(cycle)
    non_good, non_good_set, adj = build_forced_graph(ms, n, det, good_set)
    print(f"  |non-good|: {len(non_good)}")
    print(f"  |bad edges|: {sum(len(adj[c]) for c in non_good)}")

    kernel, rounds = sink_kernel(non_good, adj)
    print(f"  sink-kernel size: {len(kernel)} ({rounds} rounds)")

    shadow = find_shadow_greedy(cycle, det, ms, n)
    print(f"  greedy shadow: "
          f"{'FOUND len=' + str(len(shadow)) if shadow else 'NONE'}")


def test_tail(label, ms, max_cycle_len, time_budget=30.0):
    n = len(ms)
    print(f"\n===== TAIL {label}  n={n}  ms={ms}  max_L={max_cycle_len} =====")

    # Enumerate from a handful of starts.
    all_configs = list(iproduct(*[range(m) for m in ms]))
    starts = all_configs[:min(3, len(all_configs))]

    all_found = []
    seen_cycles = set()
    for start in starts:
        cyc = find_short_cycles(start, ms, max_cycle_len,
                                max_found=200, time_budget=time_budget)
        for c in cyc:
            key = tuple(c)
            if key not in seen_cycles:
                seen_cycles.add(key)
                all_found.append(c)

    print(f"  candidate cycles found: {len(all_found)}")
    if not all_found:
        print("  (none — try larger max_cycle_len)")
        return

    # Classify and test each.
    n_shadow = 0
    n_kernel_empty = 0
    n_both_fail = 0
    examples_no_shadow = []
    examples_empty_kernel = []

    for c in all_found:
        ok, det, msg = check_cycle_consistency(c, n, ms)
        if not ok:
            continue
        good_set = set(c)
        non_good, _, adj = build_forced_graph(ms, n, det, good_set)
        kernel, _ = sink_kernel(non_good, adj)
        shadow = find_shadow_greedy(c, det, ms, n)
        if shadow is not None:
            n_shadow += 1
        else:
            if len(examples_no_shadow) < 3:
                examples_no_shadow.append((len(c), len(kernel)))
        if len(kernel) == 0:
            n_kernel_empty += 1
            if len(examples_empty_kernel) < 3:
                examples_empty_kernel.append(len(c))
        if shadow is None and len(kernel) == 0:
            n_both_fail += 1

    print(f"  shadow hits           : {n_shadow}/{len(all_found)}")
    print(f"  empty kernels         : {n_kernel_empty}/{len(all_found)}")
    print(f"  BOTH fail (escapers)  : {n_both_fail}/{len(all_found)}")
    if examples_no_shadow:
        print(f"  no-shadow examples (L, kernel_size): {examples_no_shadow}")
    if examples_empty_kernel:
        print(f"  empty-kernel examples (L): {examples_empty_kernel}")


def main():
    print("=" * 70)
    print("WITNESSES: true good cycles extracted from stored rules")
    print("=" * 70)
    test_witness("n5", witness_n5)
    test_witness("n6", witness_n6)
    test_witness("n7", witness_n7)
    test_witness("n8", witness_n8)

    print("\n" + "=" * 70)
    print("TAILS: exhaustive candidate enumeration (no adjacency filter)")
    print("=" * 70)
    test_tail("n5_tail", (2, 2, 2, 3, 3), max_cycle_len=10, time_budget=20.0)
    test_tail("n6_tail", (2, 2, 2, 3, 3, 3), max_cycle_len=12, time_budget=45.0)


if __name__ == "__main__":
    main()
