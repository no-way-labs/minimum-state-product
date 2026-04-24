#!/usr/bin/env python3
"""
CONVERGENCE PROOF 23: Excursion Chain Trace & Potential
========================================================

DISCOVERY: Excursion depth = 2(n-4) = 2 * |T_mid positions| exactly.

This script:
1. Trace the longest excursion chains step by step
2. At each step: record which anomalous entry fires, interior values,
   and what changes
3. Identify the decreasing quantity
4. Test candidate potentials: #(2,1) interior pairs, interior value sum,
   alternating pattern count
5. Prove the depth = 2(n-4) bound
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import deque, defaultdict, Counter


def frontier_type(a, b):
    if a == b:
        return 0
    return (b - a) % 3


def w1(j, n):
    if j == n - 1:
        return 0
    if j == n - 2:
        return 1
    return j + 1


def w2(j, n):
    if j == n - 1:
        return 0
    if 1 <= j <= n - 2:
        return n - 1 - j
    return n - 1


def psi(c, n):
    total = 0
    for j in range(n):
        ft = frontier_type(c[j], c[(j + 1) % n])
        if ft == 1:
            total += w1(j, n)
        elif ft == 2:
            total += w2(j, n)
    return total


def fc_val(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))


def classify_entry(L, S, R, out):
    if out == S:
        return "stay"
    if out == L:
        return "copy_L"
    if out == R:
        return "copy_R"
    return "anomalous"


def interior_vals(c, n):
    """Values at interior positions 2..n-3."""
    return tuple(c[j] for j in range(2, n - 2))


def count_21_pairs(c, n):
    """Count interior adjacent (2,1) pairs: c[j]=2, c[j+1]=1 for j in 2..n-3."""
    count = 0
    for j in range(2, n - 2):
        if c[j] == 2 and c[(j + 1) % n] == 1:
            count += 1
    return count


def interior_sum(c, n):
    """Sum of values at interior positions 2..n-3."""
    return sum(c[j] for j in range(2, n - 2))


def count_2s_interior(c, n):
    """Count value 2 at interior positions."""
    return sum(1 for j in range(2, n - 2) if c[j] == 2)


def weighted_interior(c, n):
    """Weighted sum of interior values, weight = position index."""
    return sum(c[j] * (j - 1) for j in range(2, n - 2))


def weighted_interior_rev(c, n):
    """Weighted sum with reversed weights."""
    return sum(c[j] * (n - 2 - j) for j in range(2, n - 2))


def analyze(n_val):
    ms, fs = build_system(n_val)
    n = n_val
    result = verify_system(ms, fs)
    assert result['valid']

    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    print(f"\n{'=' * 70}")
    print(f"n = {n_val}: {len(bad_list)} bad configs")
    print(f"{'=' * 70}")

    # Build transitions
    anom_edges = []
    dfc_le0_adj = defaultdict(list)

    for c in bad_list:
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c)
                lst[i] = out
                succ = tuple(lst)
                if succ in bad_set:
                    dfc = delta_fc(L, S, R, out)
                    cls = classify_entry(L, S, R, out)
                    if dfc <= 0:
                        dfc_le0_adj[c].append(succ)
                    if cls == "anomalous":
                        anom_edges.append((c, succ, i, dfc))

    anom_sources = set(c for c, _, _, _ in anom_edges)
    anom_targets = set(succ for _, succ, _, _ in anom_edges)

    # Build excursion graph
    target_to_sources = defaultdict(list)
    for b in anom_targets:
        visited = set()
        queue = deque([b])
        visited.add(b)
        while queue:
            node = queue.popleft()
            if node in anom_sources and node != b:
                target_to_sources[b].append(node)
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt)
                    queue.append(nxt)
        if b in anom_sources:
            target_to_sources[b].append(b)

    exc_graph = defaultdict(set)
    # Also store which anomalous edge connects them
    exc_edges_detail = []  # (source, target_after_anom, reachable_source, anom_pos)
    for c, succ, i, dfc in anom_edges:
        for src in target_to_sources.get(succ, []):
            exc_graph[c].add(src)
            exc_edges_detail.append((c, succ, src, i))

    # Compute excursion DAG rank
    all_exc_nodes = set(exc_graph.keys())
    for src_set in exc_graph.values():
        all_exc_nodes |= src_set

    in_deg = {v: 0 for v in all_exc_nodes}
    for a in exc_graph:
        for b in exc_graph[a]:
            in_deg[b] = in_deg.get(b, 0) + 1

    q = deque(v for v in all_exc_nodes if in_deg[v] == 0)
    topo = []
    while q:
        v = q.popleft()
        topo.append(v)
        for w_v in exc_graph.get(v, set()):
            in_deg[w_v] -= 1
            if in_deg[w_v] == 0:
                q.append(w_v)

    exc_rank = {}
    exc_parent = {}  # For tracing chains
    for v in reversed(topo):
        best_child = None
        best_rank = -1
        for w_v in exc_graph.get(v, set()):
            if exc_rank[w_v] > best_rank:
                best_rank = exc_rank[w_v]
                best_child = w_v
        exc_rank[v] = best_rank + 1 if best_rank >= 0 else 0
        exc_parent[v] = best_child

    exc_depth = max(exc_rank.values()) if exc_rank else 0

    # ═══════════════════════════════════════════════════════════
    # TRACE longest excursion chains
    # ═══════════════════════════════════════════════════════════
    print(f"\n  Excursion depth: {exc_depth} (predicted: {2*(n-4)})")

    # Find max-depth nodes and trace their chains
    max_nodes = [v for v in all_exc_nodes if exc_rank[v] == exc_depth]

    for start in max_nodes[:2]:
        print(f"\n  LONGEST CHAIN from {start}:")
        current = start
        step = 0
        while current is not None:
            # What anomalous entry fires at current?
            entries_at = [(c, succ, i, dfc) for c, succ, i, dfc in anom_edges
                          if c == current]
            entry_info = ""
            if entries_at:
                c, succ, i, dfc = entries_at[0]
                L = c[(i - 1) % n]
                S = c[i]
                R = c[(i + 1) % n]
                out = succ[i]
                tname = {0: 'T_bot', 1: 'T_low', n-2: 'T_high',
                         n-1: 'T_top'}.get(i, f'T_mid[{i}]')
                entry_info = f"{tname}({L},{S},{R})→{out}"

            iv = interior_vals(current, n)
            n21 = count_21_pairs(current, n)
            isum = interior_sum(current, n)
            n2i = count_2s_interior(current, n)
            wi = weighted_interior(current, n)
            wir = weighted_interior_rev(current, n)

            print(f"    Step {step}: rank={exc_rank[current]}, "
                  f"config={current}")
            print(f"           interior={iv}, "
                  f"#(2,1)={n21}, isum={isum}, #2={n2i}, "
                  f"wi={wi}, wir={wir}, "
                  f"fc={fc_val(current,n)}, "
                  f"entry={entry_info}")

            current = exc_parent.get(current)
            step += 1

    # ═══════════════════════════════════════════════════════════
    # TEST CANDIDATE POTENTIALS on excursion graph
    # ═══════════════════════════════════════════════════════════
    print(f"\n  Excursion graph potential tests:")

    def test_exc_potential(name, phi_func):
        violations = 0
        total = 0
        for a in exc_graph:
            for ap in exc_graph[a]:
                total += 1
                if phi_func(ap) >= phi_func(a):
                    violations += 1
        print(f"    {name}: {violations}/{total}")
        return violations

    test_exc_potential("interior_sum",
                       lambda c: interior_sum(c, n))
    test_exc_potential("#(2,1) pairs",
                       lambda c: count_21_pairs(c, n))
    test_exc_potential("#2s_interior",
                       lambda c: count_2s_interior(c, n))
    test_exc_potential("weighted_interior (j-1)",
                       lambda c: weighted_interior(c, n))
    test_exc_potential("weighted_interior_rev (n-2-j)",
                       lambda c: weighted_interior_rev(c, n))

    # Combined with fc, psi
    test_exc_potential("(isum, fc, Ψ) lex",
                       lambda c: (interior_sum(c, n), fc_val(c, n), psi(c, n)))
    test_exc_potential("(#2i, isum, fc, Ψ) lex",
                       lambda c: (count_2s_interior(c, n), interior_sum(c, n),
                                  fc_val(c, n), psi(c, n)))
    test_exc_potential("(#(2,1), fc, Ψ) lex",
                       lambda c: (count_21_pairs(c, n), fc_val(c, n), psi(c, n)))
    test_exc_potential("(wir, fc, Ψ) lex",
                       lambda c: (weighted_interior_rev(c, n),
                                  fc_val(c, n), psi(c, n)))

    # 2D lex on interior features
    test_exc_potential("(#2i, #(2,1), fc, Ψ) lex",
                       lambda c: (count_2s_interior(c, n),
                                  count_21_pairs(c, n),
                                  fc_val(c, n), psi(c, n)))

    # Interior 2-pattern: count positions j where c[j]=2 OR (c[j]=1 and c[j-1]=2)
    def interior_active(c):
        count = 0
        for j in range(2, n - 2):
            if c[j] == 2:
                count += 1
            elif c[j] == 1 and c[(j - 1)] == 2:
                count += 1
        return count
    test_exc_potential("interior_active",
                       lambda c: interior_active(c))
    test_exc_potential("(int_active, fc, Ψ)",
                       lambda c: (interior_active(c), fc_val(c, n), psi(c, n)))

    # Sorted interior values (multiset ordering)
    def int_sorted_desc(c):
        vals = [c[j] for j in range(2, n - 2)]
        return tuple(sorted(vals, reverse=True))
    test_exc_potential("sorted_desc_interior",
                       lambda c: int_sorted_desc(c))
    test_exc_potential("(sorted_desc_int, fc, Ψ)",
                       lambda c: (int_sorted_desc(c), fc_val(c, n), psi(c, n)))

    # Full sorted config (DM multiset on ALL values)
    test_exc_potential("sorted_desc_full",
                       lambda c: tuple(sorted(c, reverse=True)))

    # ═══════════════════════════════════════════════════════════
    # BEST POTENTIAL: try ALL config projections
    # ═══════════════════════════════════════════════════════════
    # Try: (f(c), fc, Ψ) where f is a simple counting function
    print(f"\n  Comprehensive potential search:")

    # Count of value v at position subset
    for v in [0, 1, 2]:
        # Interior
        test_exc_potential(
            f"(#val={v} interior, fc, Ψ)",
            lambda c, val=v: (sum(1 for j in range(2, n-2) if c[j] == val),
                              fc_val(c, n), psi(c, n)))
        # Left half interior
        mid = (2 + n - 2) // 2
        test_exc_potential(
            f"(#val={v} left_int, fc, Ψ)",
            lambda c, val=v, m=mid: (sum(1 for j in range(2, m) if c[j] == val),
                                     fc_val(c, n), psi(c, n)))
        # Right half interior
        test_exc_potential(
            f"(#val={v} right_int, fc, Ψ)",
            lambda c, val=v, m=mid: (sum(1 for j in range(m, n-2) if c[j] == val),
                                     fc_val(c, n), psi(c, n)))

    # Transition pattern: what values change
    # Count "2-1 alternation length"
    def alt_21_len(c):
        """Length of longest (2,1,2,1,...) pattern in interior."""
        best = 0
        for start in range(2, n - 2):
            length = 0
            j = start
            expect = c[j]  # start with whatever is at j
            if expect not in (1, 2):
                continue
            while j < n - 2:
                if c[j] == expect:
                    length += 1
                    expect = 3 - expect  # toggle 1↔2
                    j += 1
                else:
                    break
            best = max(best, length)
        return best
    test_exc_potential("(alt_21_len, fc, Ψ)",
                       lambda c: (alt_21_len(c), fc_val(c, n), psi(c, n)))

    return exc_depth


if __name__ == '__main__':
    all_results = {}
    for nv in range(5, 11):
        prod = 4 * 3 ** (nv - 2)
        if prod > 100000:
            break
        d = analyze(nv)
        all_results[nv] = d

    print(f"\n{'=' * 70}")
    print(f"DEPTH = 2(n-4) verification")
    print(f"{'=' * 70}")
    for nv, d in sorted(all_results.items()):
        predicted = 2 * (nv - 4)
        match = "✓" if d == predicted else "✗"
        print(f"  n={nv}: depth={d}, 2(n-4)={predicted} {match}")
