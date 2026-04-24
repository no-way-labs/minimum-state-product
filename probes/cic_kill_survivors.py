#!/usr/bin/env python3
"""CIC Exploration 1b: Kill surviving multisets at n=9.

For each of the 12 multisets with product in (7776, 8748), try ALL distinct
ring orientations (necklaces) with multiple cycle search strategies.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
from verifier import verify_system
import time


def multiset_perms(lst):
    """Generate all distinct permutations of a list (multiset)."""
    lst = sorted(lst)
    yield tuple(lst)
    while True:
        # Find largest i such that lst[i] < lst[i+1]
        i = len(lst) - 2
        while i >= 0 and lst[i] >= lst[i + 1]:
            i -= 1
        if i < 0:
            return
        # Find largest j such that lst[i] < lst[j]
        j = len(lst) - 1
        while lst[j] <= lst[i]:
            j -= 1
        lst[i], lst[j] = lst[j], lst[i]
        lst[i + 1:] = lst[i + 1:][::-1]
        yield tuple(lst)


def distinct_necklaces(multiset, n):
    """Generate distinct ring arrangements up to rotation+reflection."""
    seen = set()
    results = []
    for p in multiset_perms(list(multiset)):
        variants = []
        for r in range(n):
            rot = tuple(p[(i + r) % n] for i in range(n))
            variants.append(rot)
            ref = tuple(p[(r - i) % n] for i in range(n))
            variants.append(ref)
        canonical = min(variants)
        if canonical not in seen:
            seen.add(canonical)
            results.append(canonical)
    return results


def max_consecutive_binary(ms, n):
    """Max run of 2s in ring arrangement ms."""
    if all(v == 2 for v in ms):
        return n
    start = None
    for i in range(n):
        if ms[i] != 2:
            start = i
            break
    max_run = 0
    current_run = 0
    for j in range(n):
        idx = (start + j) % n
        if ms[idx] == 2:
            current_run += 1
            max_run = max(max_run, current_run)
        else:
            current_run = 0
    return max_run


def build_bounce_cycle(ms, n, base_pattern=None, max_reps=5):
    if base_pattern is None:
        base_pattern = list(range(n - 1, -1, -1)) + list(range(1, n))
    for reps in range(1, max_reps):
        config = [0] * n
        cycle = [tuple(config)]
        visited = {tuple(config)}
        full = base_pattern * reps
        for step, mover in enumerate(full):
            config = list(cycle[-1])
            config[mover] = (config[mover] + 1) % ms[mover]
            nc = tuple(config)
            if nc == cycle[0]:
                return cycle, full[:step + 1]
            if nc in visited:
                break
            visited.add(nc)
            cycle.append(nc)
    return None, None


def check_triple_overlap(ms_t, n, cycle, movers):
    """Check for mover/non-mover triple overlap."""
    mover_triples = defaultdict(set)
    nonmover_triples = defaultdict(set)
    for idx in range(len(cycle)):
        c = cycle[idx]
        mv = movers[idx]
        for p in range(n):
            triple = (c[(p - 1) % n], c[p], c[(p + 1) % n])
            if p == mv:
                mover_triples[p].add(triple)
            else:
                nonmover_triples[p].add(triple)
    for p in range(n):
        if mover_triples[p] & nonmover_triples[p]:
            return True
    return False


def try_good_targeting(ms_tuple, cycle, movers, n):
    """Apply good-targeting completion. Return (valid, info)."""
    good_set = set(cycle)
    all_configs = list(cartesian(*(range(m) for m in ms_tuple)))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    # Extract determined entries
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

    # Find free entries
    free_entries = []
    for p in range(n):
        m_L = ms_tuple[(p - 1) % n]
        m_S = ms_tuple[p]
        m_R = ms_tuple[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in det:
                        free_entries.append(key)

    # Good-targeting completion
    comp = dict(det)
    for key in free_entries:
        p, L, S, R = key
        best_out = S
        best_good = 0
        best_ng = float('inf')
        for out in range(ms_tuple[p]):
            ng = 0
            good_count = 0
            if out != S:
                for c in non_good:
                    if (c[(p - 1) % n] == L and c[p] == S
                            and c[(p + 1) % n] == R):
                        new_c = list(c)
                        new_c[p] = out
                        nc = tuple(new_c)
                        if nc in good_set:
                            good_count += 1
                        elif nc in non_good_set:
                            ng += 1
            if (good_count > best_good
                    or (good_count == best_good and ng < best_ng)):
                best_out = out
                best_good = good_count
                best_ng = ng
        comp[key] = best_out

    # Liveness fix
    for c in all_configs:
        has_priv = any(
            comp.get((p, c[(p - 1) % n], c[p], c[(p + 1) % n]),
                     c[p]) != c[p]
            for p in range(n))
        if not has_priv:
            best_key = None
            best_cost = float('inf')
            best_out_val = None
            for p in range(n):
                L2 = c[(p - 1) % n]
                S2 = c[p]
                R2 = c[(p + 1) % n]
                key = (p, L2, S2, R2)
                if key not in det:
                    for out in range(ms_tuple[p]):
                        if out != S2:
                            cost = 0
                            for c2 in non_good:
                                if (c2[(p - 1) % n] == L2
                                        and c2[p] == S2
                                        and c2[(p + 1) % n] == R2):
                                    nc2 = list(c2)
                                    nc2[p] = out
                                    if tuple(nc2) in non_good_set:
                                        cost += 1
                            if cost < best_cost:
                                best_cost = cost
                                best_key = key
                                best_out_val = out
            if best_key:
                comp[best_key] = best_out_val

    def make_f(p_idx):
        def f(L, S, R):
            return comp.get((p_idx, L, S, R), S)
        return f

    fs = [make_f(p) for p in range(n)]
    result = verify_system(list(ms_tuple), fs, verbose=False)
    return result['valid'], result


def find_sccs(adj):
    """Tarjan's SCC algorithm."""
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
                    lowlink[node] = min(
                        lowlink[node], index_map[w])
            else:
                if lowlink[node] == index_map[node]:
                    scc = []
                    while True:
                        w = stack.pop()
                        on_stack.discard(w)
                        scc.append(w)
                        if w == node:
                            break
                    if (len(scc) > 1
                            or (scc[0] in adj
                                and scc[0] in adj[scc[0]])):
                        sccs.append(scc)
                work.pop()
                if work:
                    lowlink[work[-1][0]] = min(
                        lowlink[work[-1][0]], lowlink[node])

    for v in adj:
        if v not in index_map:
            strongconnect(v)
    return sccs


def check_forced_sccs(ms_tuple, cycle, movers, n):
    """Check if determined entries create forced SCCs."""
    good_set = set(cycle)
    all_configs = list(cartesian(*(range(m) for m in ms_tuple)))
    non_good = [c for c in all_configs if c not in good_set]
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

    forced_adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            key = (p, L, S, R)
            if key in det and det[key] != S:
                new_c = list(c)
                new_c[p] = det[key]
                nc = tuple(new_c)
                if nc in non_good_set:
                    forced_adj[c].append(nc)

    return find_sccs(forced_adj)


n = 9
TARGET = 4 * 3**7  # 8748

surviving_multisets = [
    (2, 2, 2, 2, 2, 2, 5, 5, 5),     # 8000
    (2, 2, 2, 2, 2, 3, 3, 4, 7),      # 8064
    (2, 2, 2, 2, 2, 2, 3, 3, 14),     # 8064
    (2, 2, 2, 2, 2, 2, 3, 6, 7),      # 8064
    (2, 2, 2, 2, 2, 4, 4, 4, 4),      # 8192
    (2, 2, 2, 2, 2, 2, 4, 4, 8),      # 8192
    (2, 2, 2, 2, 2, 2, 3, 4, 11),     # 8448
    (2, 2, 2, 2, 3, 3, 3, 4, 5),      # 8640
    (2, 2, 2, 2, 2, 3, 3, 3, 10),     # 8640
    (2, 2, 2, 2, 2, 3, 3, 5, 6),      # 8640
    (2, 2, 2, 2, 2, 2, 3, 3, 15),     # 8640
    (2, 2, 2, 2, 2, 2, 3, 5, 9),      # 8640
]

bounce_patterns = [
    ("down-up", list(range(n - 1, -1, -1)) + list(range(1, n))),
    ("up-down", list(range(n)) + list(range(n - 2, 0, -1))),
    ("fwd-sweep", list(range(n))),
    ("rev-sweep", list(range(n - 1, -1, -1))),
]

print("=" * 70)
print("CIC Kill Sweep: surviving multisets, product in (7776, 8748)")
print("=" * 70)

all_results = []

for ms_sorted in surviving_multisets:
    product = 1
    for m in ms_sorted:
        product *= m
    k_binary = ms_sorted.count(2)

    print(f"\n{'─' * 60}")
    print(f"ms={ms_sorted}  product={product}  k={k_binary}")
    print(f"{'─' * 60}")

    t0 = time.time()
    try:
        necklaces = distinct_necklaces(ms_sorted, n)
    except ImportError:
        # Fallback: use random permutations
        import random
        random.seed(42)
        seen = set()
        necklaces = []
        for _ in range(200):
            p = list(ms_sorted)
            random.shuffle(p)
            p = tuple(p)
            variants = []
            for r in range(n):
                rot = tuple(p[(i + r) % n] for i in range(n))
                variants.append(rot)
                ref = tuple(p[(r - i) % n] for i in range(n))
                variants.append(ref)
            canonical = min(variants)
            if canonical not in seen:
                seen.add(canonical)
                necklaces.append(canonical)

    valid_nk = [nk for nk in necklaces
                if max_consecutive_binary(nk, n) <= 3]
    t1 = time.time()
    print(f"  Necklaces: {len(necklaces)}, "
          f"valid: {len(valid_nk)}  [{t1-t0:.1f}s]")

    if not valid_nk:
        print("  >>> KILLED by consecutive binary!")
        all_results.append((ms_sorted, product, "consec_binary"))
        continue

    found_valid = False
    tests = 0
    overlaps = 0
    no_cycle = 0
    scc_found = 0

    for ms_perm in valid_nk:
        if found_valid:
            break
        for pname, base in bounce_patterns:
            cycle, mseq = build_bounce_cycle(ms_perm, n, base)
            if cycle is None:
                no_cycle += 1
                continue
            tests += 1
            if check_triple_overlap(ms_perm, n, cycle, mseq):
                overlaps += 1
                continue
            sccs = check_forced_sccs(ms_perm, cycle, mseq, n)
            if sccs:
                scc_found += 1
            valid, result = try_good_targeting(
                ms_perm, cycle, mseq, n)
            if valid:
                cl = result.get('cycle_length', '?')
                print(f"  *** VALID! ms={ms_perm} "
                      f"pattern={pname} cycle_len={cl} ***")
                found_valid = True
                break

    status = "VALID" if found_valid else "DEAD"
    print(f"  tests={tests} overlap={overlaps} "
          f"no_cycle={no_cycle} forced_scc={scc_found}")
    print(f"  >>> {status}")
    all_results.append((ms_sorted, product, status))

print(f"\n{'=' * 70}")
print("SUMMARY")
print("=" * 70)
for ms, prod, status in all_results:
    print(f"  {ms} product={prod}: {status}")
