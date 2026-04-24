#!/usr/bin/env python3
"""CIC: Verify the No Binary 2-Cycle Lemma and check forced SCCs for
DFS-found cycles.

No Binary 2-Cycle Lemma:
In a valid system, for binary processor p and any (L,R) context,
we CANNOT have both f_p(L,0,R)=1 AND f_p(L,1,R)=0.
(Otherwise adversary creates non-good 2-cycle: state 0->1->0->...)

This means: each (L,R) pair for binary p is either:
  "up":      f_p(L,0,R)=1, f_p(L,1,R)=1  (privileged at 0, not at 1)
  "down":    f_p(L,0,R)=0, f_p(L,1,R)=0  (privileged at 1, not at 0)
  "neutral": f_p(L,0,R)=0, f_p(L,1,R)=1  (never privileged)
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict


# ================================================================
# Part 1: Verify No Binary 2-Cycle in known valid systems
# ================================================================
print("=" * 60)
print("Part 1: No Binary 2-Cycle in known valid systems")
print("=" * 60)


def check_binary_2cycle(ms, fs, label=""):
    """Check if any binary processor has a (L,R) with both
    f(L,0,R)=1 and f(L,1,R)=0."""
    n = len(ms)
    violations = 0
    for p in range(n):
        if ms[p] != 2:
            continue
        m_L = ms[(p - 1) % n]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for R in range(m_R):
                v0 = fs[p](L, 0, R)
                v1 = fs[p](L, 1, R)
                if v0 == 1 and v1 == 0:
                    violations += 1
    if violations == 0:
        print(f"  {label}: OK (no binary 2-cycles)")
    else:
        print(f"  {label}: {violations} VIOLATIONS!")
    return violations


# Dijkstra Solution 3 (n=3,4)
for n in [3, 4]:
    ms = [3] * n

    def make_sol3(n):
        def f0(L, S, R):
            return (S + 1) % 3 if S == L else S

        def fi(L, S, R):
            return L if L != S else S
        return [f0] + [fi] * (n - 1)

    # No binary processors in Sol 3
    fs = make_sol3(n)
    print(f"  Sol3 n={n}: no binary processors (all ternary)")

# CLB endpoint-binary
print("\nCLB endpoint-binary (ms=(2,3,...,3,2)):")
for n in [5, 6, 7, 8]:
    ms = tuple([2] + [3] * (n - 2) + [2])
    up_down = list(range(n)) + list(range(n - 2, 0, -1))

    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * 5
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            cycle_found = cycle
            movers_found = full[:step + 1]
            break
        if nc in visited:
            cycle_found = None
            break
        visited.add(nc)
        cycle.append(nc)
    else:
        cycle_found = None

    if cycle_found is None:
        print(f"  n={n}: no bounce cycle")
        continue

    # Good-targeting completion
    good_set = set(cycle_found)
    all_cfgs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_cfgs if c not in good_set]
    non_good_set = set(non_good)

    det = {}
    for idx in range(len(cycle_found)):
        c = cycle_found[idx]
        c_next = cycle_found[(idx + 1) % len(cycle_found)]
        mv = movers_found[idx]
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            key = (p, L, S, R)
            if p == mv:
                det[key] = c_next[p]
            else:
                det[key] = S

    free_entries = []
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in det:
                        free_entries.append(key)

    comp = dict(det)
    for key in free_entries:
        p, L, S, R = key
        best_out = S
        best_good = 0
        best_ng = float('inf')
        for out in range(ms[p]):
            ng = 0
            good_count = 0
            if out != S:
                for c in non_good:
                    if (c[(p - 1) % n] == L and c[p] == S
                            and c[(p + 1) % n] == R):
                        nc2 = list(c)
                        nc2[p] = out
                        nc2 = tuple(nc2)
                        if nc2 in good_set:
                            good_count += 1
                        elif nc2 in non_good_set:
                            ng += 1
            if (good_count > best_good
                    or (good_count == best_good and ng < best_ng)):
                best_out = out
                best_good = good_count
                best_ng = ng
        comp[key] = best_out

    for c in all_cfgs:
        has_priv = any(
            comp.get((p, c[(p - 1) % n], c[p], c[(p + 1) % n]),
                     c[p]) != c[p]
            for p in range(n))
        if not has_priv:
            for p in range(n):
                L2 = c[(p - 1) % n]
                S2 = c[p]
                R2 = c[(p + 1) % n]
                key = (p, L2, S2, R2)
                if key not in det:
                    for out in range(ms[p]):
                        if out != S2:
                            comp[key] = out
                            break
                    break

    def make_f(p_idx):
        def f(L, S, R):
            return comp.get((p_idx, L, S, R), S)
        return f

    from verifier import verify_system
    fs = [make_f(p) for p in range(n)]
    result = verify_system(list(ms), fs, verbose=False)
    if result['valid']:
        check_binary_2cycle(list(ms), fs, f"n={n}")
    else:
        print(f"  n={n}: system not valid (good-targeting failed)")

# ================================================================
# Part 2: For DFS-found cycle, check forced SCCs
# ================================================================
print(f"\n{'=' * 60}")
print("Part 2: Forced SCCs for DFS-found cycle")
print("=" * 60)

ms_test = (3, 2, 3, 2, 4, 2, 5, 2, 2)
n = len(ms_test)
product = 1
for m in ms_test:
    product *= m
print(f"ms={ms_test}  product={product}")
print(f"Binary positions: {[i for i in range(n) if ms_test[i] == 2]}")

# Try to find a cycle with DFS
try:
    from p2_good_cycle_search import search_good_cycle
    result = search_good_cycle(ms_test, time_limit=15.0)
    if result.cycle is not None:
        cycle = result.cycle
        movers = result.movers
        print(f"DFS found cycle: len={len(cycle)}")
        print(f"  movers: {movers}")

        # Check adjacent movers
        violations = 0
        for k in range(len(movers)):
            m0 = movers[k]
            m1 = movers[(k + 1) % len(movers)]
            diff = min(abs(m1 - m0), n - abs(m1 - m0))
            if diff > 1:
                violations += 1
        print(f"  Adjacent-mover violations: {violations}")

        # Check forced SCCs
        good_set = set(cycle)
        all_cfgs = list(cartesian(*(range(m) for m in ms_test)))
        non_good = [c for c in all_cfgs if c not in good_set]
        non_good_set = set(non_good)

        det = {}
        for idx in range(len(cycle)):
            c = cycle[idx]
            c_next = cycle[(idx + 1) % len(cycle)]
            mv = movers[idx]
            for p in range(n):
                L = c[(p - 1) % n]
                S = c[p]
                R = c[(p + 1) % n]
                key = (p, L, S, R)
                if p == mv:
                    det[key] = c_next[p]
                else:
                    det[key] = S

        # Analyze determined entries per processor
        mover_ent = defaultdict(set)
        nonmover_ent = defaultdict(set)
        for idx in range(len(cycle)):
            c = cycle[idx]
            mv = movers[idx]
            for p in range(n):
                L = c[(p - 1) % n]
                S = c[p]
                R = c[(p + 1) % n]
                if p == mv:
                    mover_ent[p].add((L, S, R))
                else:
                    nonmover_ent[p].add((L, S, R))

        total_ctx = {}
        for p in range(n):
            m_L = ms_test[(p - 1) % n]
            m_S = ms_test[p]
            m_R = ms_test[(p + 1) % n]
            total_ctx[p] = m_L * m_S * m_R

        print(f"\n  Entries per processor:")
        for p in range(n):
            overlap = mover_ent[p] & nonmover_ent[p]
            print(f"    P{p} (m={ms_test[p]}): "
                  f"mover={len(mover_ent[p])}, "
                  f"nonmover={len(nonmover_ent[p])}, "
                  f"total={total_ctx[p]}, "
                  f"overlap={'YES' if overlap else 'no'}")

        # Build forced adjacency
        forced_adj = defaultdict(list)
        priv_counts = defaultdict(int)
        for c in non_good:
            privs = []
            for p in range(n):
                L = c[(p - 1) % n]
                S = c[p]
                R = c[(p + 1) % n]
                key = (p, L, S, R)
                if key in det and det[key] != S:
                    privs.append(p)
                    new_c = list(c)
                    new_c[p] = det[key]
                    nc = tuple(new_c)
                    if nc in non_good_set:
                        forced_adj[c].append(nc)
            if privs:
                priv_counts[len(privs)] += 1

        total_w_priv = sum(priv_counts.values())
        print(f"\n  Non-good configs: {len(non_good)}")
        print(f"  With forced privilege: {total_w_priv} "
              f"({100*total_w_priv/len(non_good):.0f}%)")
        print(f"  Privilege distribution: {dict(priv_counts)}")

        # Find SCCs
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
                nd, si = work[-1]
                succs = forced_adj.get(nd, [])
                if si < len(succs):
                    work[-1] = (nd, si + 1)
                    w = succs[si]
                    if w not in index_map:
                        index_map[w] = lowlink[w] = idx_counter[0]
                        idx_counter[0] += 1
                        stack.append(w)
                        on_stack.add(w)
                        work.append((w, 0))
                    elif w in on_stack:
                        lowlink[nd] = min(lowlink[nd], index_map[w])
                else:
                    if lowlink[nd] == index_map[nd]:
                        scc = []
                        while True:
                            w = stack.pop()
                            on_stack.discard(w)
                            scc.append(w)
                            if w == nd:
                                break
                        if (len(scc) > 1
                                or (scc[0] in forced_adj
                                    and scc[0] in forced_adj[scc[0]])):
                            sccs.append(scc)
                    work.pop()
                    if work:
                        lowlink[work[-1][0]] = min(
                            lowlink[work[-1][0]], lowlink[nd])

        for v in forced_adj:
            if v not in index_map:
                strongconnect(v)

        print(f"\n  Forced SCCs: {len(sccs)}")
        if sccs:
            scc_sizes = sorted([len(s) for s in sccs], reverse=True)
            print(f"  SCC sizes: {scc_sizes[:10]}"
                  f"{'...' if len(scc_sizes) > 10 else ''}")
            # Show smallest SCC
            smallest = min(sccs, key=len)
            print(f"\n  Smallest SCC (size {len(smallest)}):")
            for c in smallest[:5]:
                print(f"    {c}")

            # Check if SCCs involve binary processors
            for si, scc in enumerate(sccs[:3]):
                binary_movers = set()
                for c in scc:
                    for nc in forced_adj.get(c, []):
                        if nc in set(scc):
                            for p in range(n):
                                if c[p] != nc[p]:
                                    binary_movers.add(p)
                print(f"\n  SCC {si}: movers involved: {binary_movers}")
                bin_movers = [p for p in binary_movers
                              if ms_test[p] == 2]
                nonbin_movers = [p for p in binary_movers
                                 if ms_test[p] > 2]
                print(f"    Binary movers: {bin_movers}")
                print(f"    Non-binary movers: {nonbin_movers}")
        else:
            print("  *** NO forced SCCs! ***")

    else:
        print("No cycle found by DFS")
except ImportError:
    print("p2_good_cycle_search not available")

# ================================================================
# Part 3: Prove no-binary-2-cycle analytically
# ================================================================
print(f"\n{'=' * 60}")
print("Part 3: No Binary 2-Cycle Lemma (analytical)")
print("=" * 60)
print("""
LEMMA (No Binary 2-Cycle):
For any valid self-stabilizing token ring, for any binary processor p
(m_p = 2) and any neighbor context (L, R):
  NOT(f_p(L, 0, R) = 1  AND  f_p(L, 1, R) = 0)

PROOF:
Suppose for contradiction that f_p(L, 0, R) = 1 and f_p(L, 1, R) = 0.

Consider any config c where p sees context (L, 0, R). Then:
- f_p(L, 0, R) = 1 ≠ 0 = c[p], so p is privileged
- When p fires: c' = c with c'[p] = 1 (only p changes)
- At c': p sees context (L, 1, R) (neighbors unchanged)
- f_p(L, 1, R) = 0 ≠ 1 = c'[p], so p is STILL privileged
- When p fires: c'' = c' with c''[p] = 0 = c[p]
- c'' = c (original config)

So c → c' → c is a 2-cycle. If c is non-good, the adversary
can fire p forever at c and c', never reaching the good cycle.
Contradiction with self-stabilization.

If ALL configs with context (L,0,R) and (L,1,R) at p are good:
then c and c' are both in the good cycle. But in the good cycle,
each config appears exactly once, and the cycle visits c → c' → c
implies the good cycle has length 2. For n ≥ 3, the good cycle
must have length ≥ n ≥ 3, contradiction.

COROLLARY:
For binary p and context (L, R), exactly one of:
(a) f_p(L,0,R) = 0, f_p(L,1,R) = 1: NEUTRAL (p never privileged)
(b) f_p(L,0,R) = 1, f_p(L,1,R) = 1: UP (0→1 only)
(c) f_p(L,0,R) = 0, f_p(L,1,R) = 0: DOWN (1→0 only)

Note: case (d) f_p(L,0,R)=1, f_p(L,1,R)=0 is FORBIDDEN.

This means binary processors have DIRECTED entries:
each (L,R) context either pushes UP, pushes DOWN, or is neutral.
""")
