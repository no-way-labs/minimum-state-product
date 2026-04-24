#!/usr/bin/env python3
"""
CONVERGENCE PROOF 33: Cascade Structure Analysis
=================================================

Analyze the step-by-step transitions along excursion edges to understand
WHY the pair potential works. For each excursion edge a→a':
1. The anomalous step a→b
2. The Δfc≤0 path b→...→a'
3. Track how pairs change at each step
4. Identify the key mechanism (cascade, Q recovery, etc.)

Focus on small n (n=5,6) where we can enumerate completely.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, deque


def frontier_type(a, b):
    if a == b:
        return 0
    return (b - a) % 3


def fc_val(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def Q_val(c, n):
    return sum(1 for j in range(n)
               if c[j] == c[(j + 1) % n] and c[j] in (0, 1))


def P2_val(c, n):
    return sum(1 for j in range(n)
               if c[j] == c[(j + 1) % n] and c[j] == 2)


def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))


def pair_vector(c, n):
    """Return the list of (position, c[j], c[j+1]) pairs."""
    return [(j, c[j], c[(j + 1) % n]) for j in range(n)]


def classify_entry(L, S, R, out):
    if out == S:
        return "stay"
    if out == L:
        return "copy_L"
    if out == R:
        return "copy_R"
    return "anomalous"


def sigma2(c, n):
    """Set of positions with value 2."""
    return frozenset(j for j in range(n) if c[j] == 2)


def count_21_pairs(c, n):
    """Count (2,1) adjacent pairs."""
    return sum(1 for j in range(n)
               if c[j] == 2 and c[(j + 1) % n] == 1)


def analyze(n_val):
    ms, fs = build_system(n_val)
    n = n_val
    result = verify_system(ms, fs)
    assert result['valid']

    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    # Build transitions
    adj = defaultdict(list)
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
                    adj[c].append((succ, i))
                    dfc = delta_fc(L, S, R, out)
                    if dfc <= 0:
                        dfc_le0_adj[c].append(succ)
                    cls = classify_entry(L, S, R, out)
                    if cls == "anomalous":
                        anom_edges.append((c, succ, i, dfc))

    anom_sources = set(c for c, _, _, _ in anom_edges)

    print(f"\n{'=' * 70}")
    print(f"n = {n}: CASCADE STRUCTURE ANALYSIS")
    print(f"{'=' * 70}")

    # For each anomalous edge, trace the SHORTEST Δfc≤0 path to each
    # reachable anomalous source
    anom_type = {}
    for c, succ, pos, dfc in anom_edges:
        # Classify anomalous type
        L = c[(pos - 1) % n]
        S = c[pos]
        R = c[(pos + 1) % n]
        out = succ[pos]
        anom_type[(c, succ)] = (pos, L, S, R, out)

    # BFS from each anomalous target to find shortest Δfc≤0 path to
    # next anomalous source
    print(f"\n  {len(anom_edges)} anomalous edges, "
          f"{len(anom_sources)} anomalous sources")

    # Trace a few representative excursion edges
    traced = 0
    max_trace = 10 if n <= 6 else 5

    for c_src, b_tgt, anom_pos, anom_dfc in anom_edges:
        if traced >= max_trace:
            break

        # BFS from b_tgt in Δfc≤0 graph, record path
        parent = {b_tgt: None}
        queue = deque([b_tgt])
        reached_sources = []

        while queue:
            node = queue.popleft()
            if node in anom_sources and node != b_tgt:
                reached_sources.append(node)
                if len(reached_sources) >= 3:
                    break
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in parent:
                    parent[nxt] = node
                    queue.append(nxt)
            if b_tgt in anom_sources:
                if b_tgt not in [x for x in reached_sources]:
                    reached_sources.append(b_tgt)

        if not reached_sources:
            continue

        # Trace path to first reached source
        target = reached_sources[0]
        path = [target]
        while parent.get(path[-1]) is not None:
            path.append(parent[path[-1]])
        path.reverse()

        # Print the excursion edge trace
        traced += 1
        atype = anom_type[(c_src, b_tgt)]
        pos, L, S, R, out = atype

        print(f"\n  EXCURSION EDGE #{traced}:")
        print(f"  Source: {c_src}")
        print(f"  Anomalous: pos={pos}, ({L},{S},{R})→{out}, "
              f"Δfc={anom_dfc}")
        print(f"  Target: {b_tgt}")
        print(f"  Δfc≤0 path length: {len(path) - 1} steps")
        print(f"  Reaches: {target}")

        # Detailed trace
        print(f"\n  {'step':>4} {'config':>35} {'pos':>4} {'type':>8} "
              f"{'fc':>3} {'Q':>3} {'P2':>3} {'#21':>4} {'σ₂':>15}")

        # Step 0: source
        c_cur = c_src
        s2 = sigma2(c_cur, n)
        print(f"  {0:>4} {str(c_cur):>35} {'src':>4} {'':>8} "
              f"{fc_val(c_cur,n):>3} {Q_val(c_cur,n):>3} "
              f"{P2_val(c_cur,n):>3} {count_21_pairs(c_cur,n):>4} "
              f"{str(set(s2)):>15}")

        # Step 1: anomalous
        c_cur = b_tgt
        s2 = sigma2(c_cur, n)
        print(f"  {1:>4} {str(c_cur):>35} {pos:>4} {'ANOM':>8} "
              f"{fc_val(c_cur,n):>3} {Q_val(c_cur,n):>3} "
              f"{P2_val(c_cur,n):>3} {count_21_pairs(c_cur,n):>4} "
              f"{str(set(s2)):>15}")

        # Steps 2+: Δfc≤0 path
        for step_idx in range(len(path) - 1):
            c_prev = path[step_idx]
            c_next = path[step_idx + 1]

            # Find which position changed
            changed_pos = None
            for j in range(n):
                if c_prev[j] != c_next[j]:
                    changed_pos = j
                    break

            if changed_pos is not None:
                L_s = c_prev[(changed_pos - 1) % n]
                S_s = c_prev[changed_pos]
                R_s = c_prev[(changed_pos + 1) % n]
                out_s = c_next[changed_pos]
                cls = classify_entry(L_s, S_s, R_s, out_s)
                dfc_s = delta_fc(L_s, S_s, R_s, out_s)
            else:
                cls = "?"
                dfc_s = 0

            s2 = sigma2(c_next, n)
            print(f"  {step_idx+2:>4} {str(c_next):>35} "
                  f"{changed_pos:>4} {cls:>8} "
                  f"{fc_val(c_next,n):>3} {Q_val(c_next,n):>3} "
                  f"{P2_val(c_next,n):>3} "
                  f"{count_21_pairs(c_next,n):>4} "
                  f"{str(set(s2)):>15}")

        # Summary
        print(f"  Net: fc {fc_val(c_src,n)}→{fc_val(target,n)}, "
              f"Q {Q_val(c_src,n)}→{Q_val(target,n)}, "
              f"P2 {P2_val(c_src,n)}→{P2_val(target,n)}, "
              f"#21 {count_21_pairs(c_src,n)}→{count_21_pairs(target,n)}, "
              f"|σ₂| {len(sigma2(c_src,n))}→{len(sigma2(target,n))}")

    # ═══════════════════════════════════════════════════════════
    # GLOBAL ANALYSIS: How do key quantities change across ALL
    # excursion edges?
    # ═══════════════════════════════════════════════════════════
    print(f"\n  ── Global excursion edge statistics ──")

    # Build excursion graph
    anom_target_map = defaultdict(list)
    for c, succ, i, dfc in anom_edges:
        anom_target_map[succ].append(c)

    exc_edges = set()
    for b in set(s for _, s, _, _ in anom_edges):
        visited = set()
        queue_g = deque([b])
        visited.add(b)
        while queue_g:
            node = queue_g.popleft()
            if node in anom_sources:
                for src in anom_target_map.get(b, []):
                    exc_edges.add((src, node))
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt)
                    queue_g.append(nxt)

    # For each excursion edge, compute changes in key quantities
    delta_stats = defaultdict(list)
    for src, tgt in exc_edges:
        for name, func in [
            ("fc", lambda c: fc_val(c, n)),
            ("Q", lambda c: Q_val(c, n)),
            ("P2", lambda c: P2_val(c, n)),
            ("#21", lambda c: count_21_pairs(c, n)),
            ("|σ₂|", lambda c: len(sigma2(c, n))),
        ]:
            delta_stats[name].append(func(tgt) - func(src))

    print(f"  {len(exc_edges)} excursion edges")
    for name in ["fc", "Q", "P2", "#21", "|σ₂|"]:
        deltas = delta_stats[name]
        if deltas:
            print(f"  Δ{name:>5}: min={min(deltas):>3}, max={max(deltas):>3}, "
                  f"mean={sum(deltas)/len(deltas):>+6.2f}, "
                  f"always≤0: {all(d <= 0 for d in deltas)}, "
                  f"always<0: {all(d < 0 for d in deltas)}")

    # Check if #(2,1) + something works
    # Test: Δ(α·#21 + β·fc) ≤ -1 for all excursion edges?
    print(f"\n  Testing combined quantities on excursion edges:")
    for alpha, beta, gamma in [
        (1, 0, 0), (0, 1, 0), (1, 1, 0), (2, 1, 0),
        (1, 0, 1), (0, 0, 1), (1, 1, 1), (2, 1, 1),
    ]:
        viol = 0
        for src, tgt in exc_edges:
            val_s = (alpha * count_21_pairs(src, n)
                     + beta * fc_val(src, n)
                     + gamma * P2_val(src, n))
            val_t = (alpha * count_21_pairs(tgt, n)
                     + beta * fc_val(tgt, n)
                     + gamma * P2_val(tgt, n))
            if val_t >= val_s:
                viol += 1
        print(f"    {alpha}·#21 + {beta}·fc + {gamma}·P2: "
              f"{viol}/{len(exc_edges)} violations")


if __name__ == '__main__':
    for nv in [5, 6, 7]:
        analyze(nv)
