#!/usr/bin/env python3
"""
CONVERGENCE PROOF 25: Excursion Chain Anomalous Type Sequences
===============================================================

KEY QUESTION: Do the anomalous entries fire in a STRICT ORDER along
excursion chains? If so, this directly proves the excursion graph is a DAG.

Anomalous types:
  A1: T_bot(0,0,0)→1  at pos 0    (0→1)
  A2: T_bot(1,1,2)→0  at pos 0    (1→0)
  A3: T_mid(2,1,1)→0  at pos i    (1→0) for each i ∈ {2,...,n-3}
  A4: T_high(1,1,1)→2 at pos n-2  (1→2)
  A5: T_top(2,0,0)→1  at pos n-1  (0→1)

This script:
1. For each excursion graph edge, record which anomalous type + position fires
2. Build a "type transition graph" showing which types can follow which
3. Check if the type transition graph is acyclic
4. Trace full excursion chains with type annotations
5. Look for a position-based monotone quantity
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import deque, defaultdict, Counter


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


def anom_type(pos, L, S, R, out, n):
    """Classify which anomalous entry is firing."""
    if pos == 0 and (L, S, R, out) == (0, 0, 0, 1):
        return "A1:T_bot(000→1)"
    if pos == 0 and (L, S, R, out) == (1, 1, 2, 0):
        return "A2:T_bot(112→0)"
    if 2 <= pos <= n - 3 and (L, S, R, out) == (2, 1, 1, 0):
        return f"A3:T_mid[{pos}](211→0)"
    if pos == n - 2 and (L, S, R, out) == (1, 1, 1, 2):
        return "A4:T_high(111→2)"
    if pos == n - 1 and (L, S, R, out) == (2, 0, 0, 1):
        return "A5:T_top(200→1)"
    return f"??:pos{pos}({L},{S},{R})→{out}"


def anom_class(pos, L, S, R, out, n):
    """Return a short class label for the anomalous type."""
    if pos == 0 and (L, S, R, out) == (0, 0, 0, 1):
        return "A1"
    if pos == 0 and (L, S, R, out) == (1, 1, 2, 0):
        return "A2"
    if 2 <= pos <= n - 3 and (L, S, R, out) == (2, 1, 1, 0):
        return f"A3[{pos}]"
    if pos == n - 2 and (L, S, R, out) == (1, 1, 1, 2):
        return "A4"
    if pos == n - 1 and (L, S, R, out) == (2, 0, 0, 1):
        return "A5"
    return f"?[{pos}]"


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

    # Classify all transitions
    anom_edges = []  # (source, target, pos, dfc, anom_class_label)
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
                        ac = anom_class(i, L, S, R, out, n)
                        anom_edges.append((c, succ, i, dfc, ac))

    anom_sources = set(c for c, _, _, _, _ in anom_edges)
    anom_targets = set(succ for _, succ, _, _, _ in anom_edges)

    # Map each anomalous source to its anomalous class(es)
    source_classes = defaultdict(set)
    for c, succ, i, dfc, ac in anom_edges:
        source_classes[c].add(ac)

    # For each target, BFS to find reachable sources
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

    # Build excursion graph with type annotations
    exc_graph = defaultdict(set)
    exc_edges_typed = []  # (source, target, reachable_source, anom_class_of_source)
    for c, succ, i, dfc, ac in anom_edges:
        for src in target_to_sources.get(succ, []):
            exc_graph[c].add(src)
            exc_edges_typed.append((c, succ, src, ac))

    # ═══════════════════════════════════════════════════════════
    # TEST 1: Type transition matrix
    # For each excursion edge a →[type_a]→ ... → a', what is type_a'?
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 1: Anomalous type transition matrix")
    type_trans = Counter()
    for c, succ, src, ac_source in exc_edges_typed:
        for ac_target in source_classes[src]:
            type_trans[(ac_source, ac_target)] += 1

    # Print matrix
    all_types = sorted(set(t for pair in type_trans for t in pair))
    print(f"    Types present: {all_types}")
    print(f"\n    From \\ To  ", end="")
    for t in all_types:
        print(f"  {t:>12}", end="")
    print()
    for t1 in all_types:
        print(f"    {t1:>12}", end="")
        for t2 in all_types:
            cnt = type_trans.get((t1, t2), 0)
            print(f"  {cnt:>12}", end="")
        print()

    # Check if the type transition graph (on classes) is acyclic
    type_adj = defaultdict(set)
    for (t1, t2), cnt in type_trans.items():
        if cnt > 0:
            type_adj[t1].add(t2)

    # Cycle check via DFS
    type_color = {}
    has_type_cycle = False
    for start in all_types:
        if start in type_color:
            continue
        stack = [(start, False)]
        while stack:
            node, returning = stack.pop()
            if returning:
                type_color[node] = 2
                continue
            if node in type_color:
                if type_color[node] == 1:
                    has_type_cycle = True
                continue
            type_color[node] = 1
            stack.append((node, True))
            for nxt in type_adj.get(node, set()):
                if nxt not in type_color:
                    stack.append((nxt, False))
                elif type_color[nxt] == 1:
                    has_type_cycle = True

    print(f"\n    Type transition graph has cycle: {'YES' if has_type_cycle else 'NO'}")

    # ═══════════════════════════════════════════════════════════
    # TEST 2: Position-based analysis
    # For each excursion edge, track: position of anomalous fire at source
    # vs position of anomalous fire at target
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 2: Anomalous position transitions")
    pos_trans = Counter()
    for c, succ, i, dfc, ac in anom_edges:
        # i is the anomalous position at source c
        for src in target_to_sources.get(succ, []):
            # What positions are anomalous at src?
            for c2, s2, i2, d2, ac2 in anom_edges:
                if c2 == src:
                    pos_trans[(i, i2)] += 1

    print(f"    Source_pos → Target_pos transitions:")
    all_anom_pos = sorted(set(p for pair in pos_trans for p in pair))
    print(f"    Positions: {all_anom_pos}")
    print(f"\n    From \\ To  ", end="")
    for p in all_anom_pos:
        print(f"  {p:>4}", end="")
    print()
    for p1 in all_anom_pos:
        print(f"    {p1:>8}  ", end="")
        for p2 in all_anom_pos:
            cnt = pos_trans.get((p1, p2), 0)
            print(f"  {cnt:>4}", end="")
        print()

    # ═══════════════════════════════════════════════════════════
    # TEST 3: Trace longest excursion chains with type annotations
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 3: Longest excursion chains with types")

    # Compute excursion rank
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
    exc_parent = {}
    exc_parent_type = {}  # anomalous type used at this step
    for v in reversed(topo):
        best_child = None
        best_rank = -1
        best_type = None
        for w_v in exc_graph.get(v, set()):
            if exc_rank[w_v] > best_rank:
                best_rank = exc_rank[w_v]
                best_child = w_v
        exc_rank[v] = best_rank + 1 if best_rank >= 0 else 0
        exc_parent[v] = best_child

        # Find which anomalous type connects v to best_child
        if best_child is not None:
            for c, succ, src, ac in exc_edges_typed:
                if c == v and src == best_child:
                    best_type = ac
                    break
        exc_parent_type[v] = best_type

    exc_depth = max(exc_rank.values()) if exc_rank else 0
    print(f"    Excursion depth: {exc_depth} (= 2(n-4) = {2*(n-4)})")

    # Trace longest chains
    max_nodes = [v for v in all_exc_nodes if exc_rank[v] == exc_depth]

    for start in max_nodes[:3]:
        print(f"\n    Chain from {start} (rank {exc_depth}):")
        current = start
        step = 0
        type_seq = []
        pos_seq = []
        while current is not None:
            # Get anomalous type at current
            types_here = source_classes.get(current, set())
            type_used = exc_parent_type.get(current, None)

            # Get anomalous position
            anom_pos_here = set()
            for c, succ, i, dfc, ac in anom_edges:
                if c == current:
                    anom_pos_here.add((i, ac))

            pos_str = ",".join(f"p{p}" for p, _ in sorted(anom_pos_here))
            type_str = type_used if type_used else "(terminal)"

            if type_used:
                type_seq.append(type_used)
            if anom_pos_here:
                pos_seq.append(min(p for p, _ in anom_pos_here))

            interior = tuple(current[j] for j in range(2, n - 2))
            print(f"      [{step:>2}] rank={exc_rank[current]:>2} "
                  f"config={current} "
                  f"int={interior} "
                  f"type={type_str} "
                  f"pos={pos_str}")

            current = exc_parent.get(current)
            step += 1

        print(f"    Type sequence: {' → '.join(type_seq)}")
        if pos_seq:
            print(f"    Position sequence: {pos_seq}")

    # ═══════════════════════════════════════════════════════════
    # TEST 4: Position-based potential on excursion graph
    # Try: rank = f(anomalous_position)
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 4: Position-based excursion potentials")

    # For each config, get the set of anomalous positions
    def anom_positions(c):
        positions = set()
        for c2, succ, i, dfc, ac in anom_edges:
            if c2 == c:
                positions.add(i)
        return positions

    def max_anom_pos(c):
        positions = anom_positions(c)
        return max(positions) if positions else -1

    def min_anom_pos(c):
        positions = anom_positions(c)
        return min(positions) if positions else n

    def sum_anom_pos(c):
        return sum(anom_positions(c))

    def test_exc_pot(name, phi):
        viol = 0
        total = 0
        for a in exc_graph:
            for ap in exc_graph[a]:
                total += 1
                if phi(ap) >= phi(a):
                    viol += 1
        print(f"    {name}: {viol}/{total}")
        return viol

    test_exc_pot("max_anom_pos", max_anom_pos)
    test_exc_pot("min_anom_pos", min_anom_pos)
    test_exc_pot("-max_anom_pos", lambda c: -max_anom_pos(c))
    test_exc_pot("-min_anom_pos", lambda c: -min_anom_pos(c))
    test_exc_pot("sum_anom_pos", sum_anom_pos)
    test_exc_pot("(max_pos, fc, Ψ)", lambda c: (max_anom_pos(c),
                                                  fc_val(c, n), psi(c, n)))
    test_exc_pot("(-max_pos, fc, Ψ)", lambda c: (-max_anom_pos(c),
                                                   fc_val(c, n), psi(c, n)))
    test_exc_pot("(min_pos, fc, Ψ)", lambda c: (min_anom_pos(c),
                                                  fc_val(c, n), psi(c, n)))
    test_exc_pot("(-min_pos, fc, Ψ)", lambda c: (-min_anom_pos(c),
                                                   fc_val(c, n), psi(c, n)))

    # Interior value at specific positions
    def int_weighted(c):
        """2*#(2 in interior) + #(1 in interior)."""
        total = 0
        for j in range(2, n - 2):
            total += c[j]  # 0→0, 1→1, 2→2
        return total

    def int_pos_weighted(c):
        """Sum of (n-j)*c[j] for interior positions — weights favor left."""
        return sum((n - j) * c[j] for j in range(2, n - 2))

    def int_pos_weighted_r(c):
        """Sum of j*c[j] for interior positions — weights favor right."""
        return sum(j * c[j] for j in range(2, n - 2))

    test_exc_pot("int_val_sum", int_weighted)
    test_exc_pot("(int_val_sum, fc, Ψ)", lambda c: (int_weighted(c),
                                                      fc_val(c, n), psi(c, n)))
    test_exc_pot("int_pos_wt_left", int_pos_weighted)
    test_exc_pot("(int_pos_wt_left, fc, Ψ)", lambda c: (int_pos_weighted(c),
                                                          fc_val(c, n), psi(c, n)))
    test_exc_pot("int_pos_wt_right", int_pos_weighted_r)
    test_exc_pot("(int_pos_wt_right, fc, Ψ)", lambda c: (int_pos_weighted_r(c),
                                                           fc_val(c, n), psi(c, n)))

    # Boundary values
    def bnd_val(c):
        """c[0] + c[1] + c[n-2] + c[n-1] weighted."""
        return 4 * c[0] + 3 * c[1] + 2 * c[n - 2] + c[n - 1]

    test_exc_pot("bnd_val", bnd_val)
    test_exc_pot("(bnd_val, fc, Ψ)", lambda c: (bnd_val(c),
                                                  fc_val(c, n), psi(c, n)))

    # Full weighted sum: position × value
    for w_type in ["linear", "quadratic", "boundary_heavy"]:
        if w_type == "linear":
            weights = [j for j in range(n)]
        elif w_type == "quadratic":
            weights = [j * j for j in range(n)]
        else:
            weights = [n] + [1] * (n - 2) + [n]
        def make_wsum(w):
            return lambda c: sum(w[j] * c[j] for j in range(n))
        test_exc_pot(f"wsum_{w_type}", make_wsum(weights))
        test_exc_pot(f"(wsum_{w_type}, fc, Ψ)",
                     lambda c, w=weights: (sum(w[j] * c[j] for j in range(n)),
                                           fc_val(c, n), psi(c, n)))

    # ═══════════════════════════════════════════════════════════
    # TEST 5: Combined potential: (anom_class_rank, ..., fc, Ψ)
    # Assign a rank to each anomalous class and test lex ordering
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 5: Class-rank based potentials")

    # Try different orderings of the anomalous classes
    from itertools import permutations

    # Get all class labels used
    all_class_labels = sorted(set(ac for _, _, _, _, ac in anom_edges))
    print(f"    Class labels: {all_class_labels}")

    # For each config, get its "primary" class (the one used in longest chain)
    def primary_class(c):
        """Return the class label of the first anomalous entry at c."""
        for c2, succ, i, dfc, ac in anom_edges:
            if c2 == c:
                return ac
        return ""

    # Test: just the class label as a string (lexicographic)
    test_exc_pot("primary_class_lex", primary_class)

    # For small number of classes, try all rank assignments
    if len(all_class_labels) <= 8:
        best_perm_violations = len(exc_edges_typed) + 1
        best_perm = None
        for perm in permutations(range(len(all_class_labels))):
            class_rank = dict(zip(all_class_labels, perm))

            def make_phi(cr):
                def phi(c):
                    cls = primary_class(c)
                    return (cr.get(cls, 0), fc_val(c, n), psi(c, n))
                return phi

            viol = sum(1 for a in exc_graph for ap in exc_graph[a]
                       if make_phi(class_rank)(ap) >= make_phi(class_rank)(a))
            if viol < best_perm_violations:
                best_perm_violations = viol
                best_perm = dict(zip(all_class_labels, perm))

        print(f"    Best class rank permutation: {best_perm}")
        print(f"    Violations: {best_perm_violations}/{len(exc_edges_typed)}")

    # ═══════════════════════════════════════════════════════════
    # TEST 6: Excursion graph analysis by anomalous position
    # For each anomalous position p, what positions can follow?
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST 6: Detailed position flow analysis")

    # For each excursion edge, get the SPECIFIC anomalous position at source
    # and ALL anomalous positions at the target
    for c, succ, src, ac in exc_edges_typed[:20]:
        src_pos = set()
        for c2, s2, i2, d2, ac2 in anom_edges:
            if c2 == c:
                src_pos.add(i2)
        tgt_pos = set()
        for c2, s2, i2, d2, ac2 in anom_edges:
            if c2 == src:
                tgt_pos.add(i2)
        # Only print if position changes
        if src_pos != tgt_pos:
            pass  # Skip individual printing, we'll summarize

    # Summary: what's the typical anomalous position at max-rank configs?
    rank_pos = defaultdict(Counter)
    for v in all_exc_nodes:
        for c2, s2, i2, d2, ac2 in anom_edges:
            if c2 == v:
                rank_pos[exc_rank[v]][i2] += 1

    print(f"    Anomalous position distribution by excursion rank:")
    for rank in sorted(rank_pos.keys(), reverse=True)[:10]:
        pos_dist = sorted(rank_pos[rank].items())
        dist_str = ", ".join(f"p{p}:{cnt}" for p, cnt in pos_dist)
        print(f"      rank {rank:>3}: {dist_str}")

    return exc_depth, has_type_cycle


if __name__ == '__main__':
    for nv in range(5, 11):
        prod = 4 * 3 ** (nv - 2)
        if prod > 100000:
            break
        analyze(nv)
