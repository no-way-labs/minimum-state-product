#!/usr/bin/env python3
"""SK (sink-kernel) invariant: flesh-out probe.

Four experiments:

  (1) MONOTONICITY: for each stored witness ms, compute SK on the
      determined bad graph from the witness's true good cycle (SK_det)
      and SK on the full transition table's bad graph (SK_full).
      Verify SK_det ⊆ SK_full (monotonicity in action — both should
      be empty for valid witnesses, but we print both sizes).

  (2) WITNESS CANDIDATE MULTIPLICITY: at each witness ms (n=5,6,7,8),
      enumerate candidate good cycles via find_short_cycles and count
      how many have empty SK. Asks whether the witness is structurally
      unique or whether many candidates escape obstruction.

  (3) TAIL EXTENSION n=7: run the tail probe on the canonical pure
      (2^3, 3^4) multiset at n=7. Count candidate cycles with empty
      SK. Expected: zero.

  (4) KERNEL STRUCTURE AT TAILS: for a few tail candidate cycles,
      inspect SK(C) — single SCC? non-trivial SCC count? Does it
      contain a binary 6-cycle backbone?
"""

from itertools import product as iproduct
from collections import defaultdict
import time


# ----------------------------------------------------------------------
# Witness rule tables (verbatim from verify_witnesses.py).
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


# ----------------------------------------------------------------------
# Core primitives.
# ----------------------------------------------------------------------
def extract_good_cycle(ms, rules):
    n = len(ms)
    all_configs = list(iproduct(*[range(m) for m in ms]))
    priv_cache = {}
    for cfg in all_configs:
        pv = []
        for i in range(n):
            L = cfg[(i-1)%n]; S = cfg[i]; R = cfg[(i+1)%n]
            if rules[i][(L,S,R)] != S:
                pv.append(i)
        priv_cache[cfg] = pv
    def move(cfg, p):
        L = cfg[(p-1)%n]; S = cfg[p]; R = cfg[(p+1)%n]
        lst = list(cfg); lst[p] = rules[p][(L,S,R)]
        return tuple(lst)
    single = {c: (move(c, priv_cache[c][0]), priv_cache[c][0])
              for c in all_configs if len(priv_cache[c]) == 1}
    for start in single:
        path = [start]; movers = []; visited = {start}; cur = start
        while cur in single:
            nxt, mv = single[cur]
            movers.append(mv)
            if nxt == start:
                return path, movers
            if nxt in visited:
                break
            visited.add(nxt); path.append(nxt); cur = nxt
    return None, None


def extract_det(cycle, ms, n):
    det = {}
    L = len(cycle)
    for idx in range(L):
        c = cycle[idx]; c_next = cycle[(idx+1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return None
        mover = diffs[0]
        Lm = c[(mover-1)%n]; Sm = c[mover]; Rm = c[(mover+1)%n]
        km = (mover, Lm, Sm, Rm)
        if km in det and det[km] != c_next[mover]:
            return None
        det[km] = c_next[mover]
        for i in range(n):
            if i == mover: continue
            Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
            ki = (i, Li, Si, Ri)
            if ki in det and det[ki] != Si:
                return None
            det[ki] = Si
    return det


def det_from_full_rules(ms, rules):
    """Full transition table as a det dict (every (p,L,S,R) has an entry)."""
    n = len(ms)
    det = {}
    for p in range(n):
        for key, val in rules[p].items():
            L, S, R = key
            det[(p, L, S, R)] = val
    return det


def build_forced_graph(ms, n, det, good_set):
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    ng_set = set(non_good)
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p-1)%n]; Sp = c[p]; Rp = c[(p+1)%n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                nc = list(c); nc[p] = det[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append((nc, p))
    return non_good, ng_set, adj


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


def count_sccs(kernel, adj):
    """Tarjan SCC on kernel, return (scc_count, largest_scc_size)."""
    import sys
    sys.setrecursionlimit(max(sys.getrecursionlimit(), len(kernel) + 100))
    kset = set(kernel)
    index_map = {}
    lowlink = {}
    on_stack = set()
    stack = []
    counter = [0]
    sccs = []
    def strongconnect(v):
        index_map[v] = counter[0]
        lowlink[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on_stack.add(v)
        for w, _ in adj.get(v, ()):
            if w not in kset:
                continue
            if w not in index_map:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], index_map[w])
        if lowlink[v] == index_map[v]:
            comp = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                comp.append(w)
                if w == v:
                    break
            sccs.append(comp)
    for v in kset:
        if v not in index_map:
            strongconnect(v)
    nontriv = [s for s in sccs if len(s) > 1]
    largest = max((len(s) for s in sccs), default=0)
    return len(nontriv), largest


def check_cycle_consistency(cycle_configs, n, ms):
    required = {}
    L = len(cycle_configs)
    for idx in range(L):
        c = cycle_configs[idx]
        c_next = cycle_configs[(idx+1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return False, {}
        mv = diffs[0]
        Li = c[(mv-1)%n]; Si = c[mv]; Ri = c[(mv+1)%n]
        km = (mv, Li, Si, Ri)
        if km in required and required[km] != c_next[mv]:
            return False, {}
        required[km] = c_next[mv]
        for i in range(n):
            if i == mv: continue
            Li2 = c[(i-1)%n]; Si2 = c[i]; Ri2 = c[(i+1)%n]
            ki = (i, Li2, Si2, Ri2)
            if ki in required and required[ki] != Si2:
                return False, {}
            required[ki] = Si2
    return True, required


def find_short_cycles(start, ms, max_length, max_found=500, time_budget=30.0):
    n = len(ms)
    found = []
    t0 = time.time()
    def dfs(path, movers_used):
        if len(found) >= max_found or time.time() - t0 > time_budget:
            return
        config = path[-1]
        if len(path) >= n * 2 and len(movers_used) == n:
            for proc in range(n):
                for new_val in range(ms[proc]):
                    if new_val == config[proc]: continue
                    nc = list(config); nc[proc] = new_val
                    if tuple(nc) == start:
                        ok, _ = check_cycle_consistency(list(path), n, ms)
                        if ok:
                            found.append(list(path))
        if len(path) >= max_length:
            return
        visited = set(path)
        for proc in range(n):
            for new_val in range(ms[proc]):
                if new_val == config[proc]: continue
                nc = list(config); nc[proc] = new_val
                nc_t = tuple(nc)
                if nc_t in visited: continue
                dfs(path + [nc_t], movers_used | {proc})
    dfs([start], set())
    return found


# ----------------------------------------------------------------------
# Experiment 1: monotonicity
# ----------------------------------------------------------------------
def exp_monotonicity():
    print("=" * 70)
    print("EXPERIMENT 1: monotonicity  SK(det_witness) ⊆ SK(full_table)")
    print("=" * 70)
    for label, fn in [("n5", witness_n5), ("n6", witness_n6),
                      ("n7", witness_n7), ("n8", witness_n8)]:
        ms, rules = fn()
        n = len(ms)
        cycle, movers = extract_good_cycle(ms, rules)
        if cycle is None:
            print(f"  {label}: FAILED to extract cycle")
            continue
        det = extract_det(cycle, ms, n)
        det_full = det_from_full_rules(ms, rules)

        good_set = set(cycle)
        ng_det, _, adj_det = build_forced_graph(ms, n, det, good_set)
        ng_full, _, adj_full = build_forced_graph(ms, n, det_full, good_set)

        sk_det, r_det = sink_kernel(ng_det, adj_det)
        sk_full, r_full = sink_kernel(ng_full, adj_full)

        det_edges = sum(len(adj_det[c]) for c in ng_det)
        full_edges = sum(len(adj_full[c]) for c in ng_full)
        subset_ok = set(sk_det).issubset(set(sk_full))

        print(f"  {label}  ms={ms}")
        print(f"    |det|: {len(det)}  |full|: {len(det_full)}  "
              f"edges: {det_edges} vs {full_edges}")
        print(f"    SK(det): {len(sk_det)} ({r_det}r)  "
              f"SK(full): {len(sk_full)} ({r_full}r)")
        print(f"    SK(det) ⊆ SK(full): {subset_ok}")


# ----------------------------------------------------------------------
# Experiment 2: witness candidate multiplicity
# ----------------------------------------------------------------------
def exp_witness_multiplicity():
    print("\n" + "=" * 70)
    print("EXPERIMENT 2: witness ms — how many candidate cycles have empty SK?")
    print("=" * 70)
    for label, fn, max_L, time_budget in [
        ("n5", witness_n5, 12, 15.0),
        ("n6", witness_n6, 14, 30.0),
        ("n7", witness_n7, 16, 45.0),
        ("n8", witness_n8, 16, 60.0),
    ]:
        ms, _ = fn()
        n = len(ms)
        print(f"\n  {label}  ms={ms}  max_L={max_L}  budget={time_budget}s")

        all_configs = list(iproduct(*[range(m) for m in ms]))
        starts = all_configs[:min(3, len(all_configs))]

        seen = set()
        empty_sk = 0
        nonempty_sk = 0
        lens_empty = []
        t0 = time.time()
        for start in starts:
            budget_remaining = time_budget - (time.time() - t0)
            if budget_remaining <= 1.0:
                break
            cycles = find_short_cycles(start, ms, max_L, max_found=300,
                                        time_budget=budget_remaining)
            for c in cycles:
                key = tuple(c)
                if key in seen: continue
                seen.add(key)
                ok, det = check_cycle_consistency(c, n, ms)
                if not ok: continue
                good_set = set(c)
                ng, _, adj = build_forced_graph(ms, n, det, good_set)
                sk, _ = sink_kernel(ng, adj)
                if len(sk) == 0:
                    empty_sk += 1
                    if len(lens_empty) < 10:
                        lens_empty.append(len(c))
                else:
                    nonempty_sk += 1
        total = empty_sk + nonempty_sk
        print(f"    candidates tested: {total}")
        print(f"    empty SK   : {empty_sk}")
        print(f"    nonempty SK: {nonempty_sk}")
        if lens_empty:
            print(f"    empty-SK cycle lengths: {sorted(lens_empty)}")


# ----------------------------------------------------------------------
# Experiment 3: tail extension to n=7
# ----------------------------------------------------------------------
def exp_tail_n7():
    print("\n" + "=" * 70)
    print("EXPERIMENT 3: tail n=7  ms=(2,2,2,3,3,3,3) — any escapers?")
    print("=" * 70)
    ms = (2, 2, 2, 3, 3, 3, 3)
    n = 7
    max_L = 16
    time_budget = 90.0
    all_configs = list(iproduct(*[range(m) for m in ms]))
    starts = all_configs[:3]
    seen = set()
    empty_sk = 0; nonempty_sk = 0
    t0 = time.time()
    for start in starts:
        budget = time_budget - (time.time() - t0)
        if budget <= 1.0: break
        cycles = find_short_cycles(start, ms, max_L, max_found=400,
                                    time_budget=budget)
        for c in cycles:
            key = tuple(c)
            if key in seen: continue
            seen.add(key)
            ok, det = check_cycle_consistency(c, n, ms)
            if not ok: continue
            good_set = set(c)
            ng, _, adj = build_forced_graph(ms, n, det, good_set)
            sk, _ = sink_kernel(ng, adj)
            if len(sk) == 0:
                empty_sk += 1
            else:
                nonempty_sk += 1
    total = empty_sk + nonempty_sk
    print(f"  candidates tested: {total}")
    print(f"  empty SK   : {empty_sk}")
    print(f"  nonempty SK: {nonempty_sk}  (escapers = {empty_sk})")


# ----------------------------------------------------------------------
# Experiment 4: kernel structure at tails
# ----------------------------------------------------------------------
def exp_kernel_structure():
    print("\n" + "=" * 70)
    print("EXPERIMENT 4: SK structure at tail candidates")
    print("=" * 70)
    for label, ms, max_L in [
        ("n5_tail", (2,2,2,3,3),    10),
        ("n6_tail", (2,2,2,3,3,3),  12),
    ]:
        n = len(ms)
        print(f"\n  {label}  ms={ms}")
        all_configs = list(iproduct(*[range(m) for m in ms]))
        cycles = find_short_cycles(all_configs[0], ms, max_L,
                                    max_found=20, time_budget=15.0)
        for idx, c in enumerate(cycles[:8]):
            ok, det = check_cycle_consistency(c, n, ms)
            if not ok: continue
            good_set = set(c)
            ng, _, adj = build_forced_graph(ms, n, det, good_set)
            sk, rounds = sink_kernel(ng, adj)
            if len(sk) == 0: continue
            nt_scc, largest = count_sccs(sk, adj)
            # Binary projections in the kernel.
            bpos = [i for i, m in enumerate(ms) if m == 2]
            bproj = {tuple(cfg[i] for i in bpos) for cfg in sk}
            print(f"    cycle {idx} L={len(c)}: |SK|={len(sk)} "
                  f"rounds={rounds} nt_SCCs={nt_scc} largest={largest} "
                  f"binary_projs={len(bproj)}")


def main():
    exp_monotonicity()
    exp_witness_multiplicity()
    exp_tail_n7()
    exp_kernel_structure()


if __name__ == "__main__":
    main()
