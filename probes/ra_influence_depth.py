#!/usr/bin/env python3
"""
Investigate bounded influence depth for PhiFull in CUP-2.

Question: Is there a fixed depth k such that PhiFull(c) is determined by
the first k and last k values of c?

The boundary 6-tuple alone (k=3) is NOT sufficient (known counterexample).
We test k=4,5,... to find the minimal sufficient depth.
"""

import sys, time
from itertools import product as cartesian
from collections import defaultdict

sys.stdout.reconfigure(line_buffering=True)

# ── CUP-2 transition tables ──────────────────────────────────────────────
T_low = {
    (0,0,0):0, (0,0,1):0, (0,0,2):0,
    (0,1,0):0, (0,1,1):0, (0,1,2):0,
    (1,0,0):0, (1,0,1):0, (1,0,2):0,
    (1,1,0):0, (1,1,1):1, (1,1,2):0,
}

T_high = {
    (0,0,0):0, (0,0,1):0,
    (0,1,0):0, (0,1,1):0,
    (0,2,0):0, (0,2,1):0,
    (1,0,0):0, (1,0,1):1,
    (1,1,0):0, (1,1,1):1,
    (1,2,0):0, (1,2,1):1,
}

T_mid = {
    (0,0,0):0, (0,0,1):0, (0,0,2):0,
    (0,1,0):1, (0,1,1):0, (0,1,2):0,
    (0,2,0):2, (0,2,1):0, (0,2,2):0,
    (1,0,0):0, (1,0,1):1, (1,0,2):1,
    (1,1,0):1, (1,1,1):1, (1,1,2):1,
    (1,2,0):2, (1,2,1):1, (1,2,2):1,
    (2,0,0):0, (2,0,1):0, (2,0,2):2,
    (2,1,0):1, (2,1,1):0, (2,1,2):2,
    (2,2,0):2, (2,2,1):0, (2,2,2):2,
}

T_lo_adj = {
    (0,0,0):0, (0,0,1):0, (0,0,2):0,
    (0,1,0):1, (0,1,1):0, (0,1,2):0,
    (1,0,0):0, (1,0,1):1, (1,0,2):1,
    (1,1,0):1, (1,1,1):1, (1,1,2):1,
    (2,0,0):0, (2,0,1):0, (2,0,2):2,
    (2,1,0):1, (2,1,1):0, (2,1,2):2,
}

T_hi_adj = {
    (0,0,0):0, (0,0,1):0,
    (0,1,0):1, (0,1,1):0,
    (0,2,0):2, (0,2,1):0,
    (1,0,0):0, (1,0,1):1,
    (1,1,0):1, (1,1,1):1,
    (1,2,0):2, (1,2,1):1,
    (2,0,0):0, (2,0,1):0,
    (2,1,0):1, (2,1,1):0,
    (2,2,0):2, (2,2,1):0,
}

def cup2_output(n, c, i):
    S = c[i]
    L = c[(i - 1) % n]
    R = c[(i + 1) % n]
    if i == 0:
        return T_low.get((S, L, R), S)
    elif i == n - 1:
        return T_high.get((S, L, R), S)
    elif i == 1:
        return T_lo_adj.get((S, L, R), S)
    elif i == n - 2:
        return T_hi_adj.get((S, L, R), S)
    else:
        return T_mid.get((S, L, R), S)

def is_privileged(n, c, i):
    return cup2_output(n, c, i) != c[i]

def fire(n, c, i):
    lst = list(c)
    lst[i] = cup2_output(n, c, i)
    return tuple(lst)

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])

def modulus(i, n):
    return 2 if i == 0 or i == n - 1 else 3

def all_configs(n):
    return list(cartesian(*(range(modulus(i, n)) for i in range(n))))

# ── TP invariant (exp2_count, int_21, exp2_weight) ───────────────────────
def tp_invariant(c, n):
    e2 = 0
    i21 = 0
    ew = 0
    for j in range(2, n - 2):
        if c[j] == 2:
            r = c[(j + 1) % n]
            if r == 0 or r == 1:
                e2 += 1
                ew += j
                if r == 1:
                    i21 += 1
    return (e2, i21, ew)

# ── Good cycle identification (from CUP-2 construction) ─────────────────
def build_good_cycle(n):
    """Build the CUP-2 good cycle for ring of size n.
    Good configs are those on the unique good cycle.
    We identify them as the unique SCC of the good-step subgraph."""
    configs = all_configs(n)
    # A config is "good" if fc=0 (i.e., it's a fixed point of the daemon)
    # Actually, good cycle configs are those with fc=0 under the legitimate config view.
    # For CUP-2, the good cycle consists of configs where exactly one proc is privileged.
    # Let me just use: good = {c : fc(c,n) == 0}? No, fc counts non-privileged.
    # fc counts *frontiers* = positions where c[j] != c[j+1].
    # Actually fc here counts the number of adjacent pairs that differ.
    # In the self-stabilization context, a "legitimate" config has exactly one privileged proc.
    # For the CUP-2 system, good configs form a cycle. Let me find them by finding
    # configs with exactly 1 privileged proc.
    # Actually, let me just build the full reachability graph and find good cycle
    # differently. From the Lean code, the good cycle has a specific structure.
    # For now, let's find it computationally: start from the all-zero config.
    # In a token ring, (0,0,...,0) has exactly one token at position 0.

    # Actually the simplest: configs on the good cycle are those reachable from (0,...,0)
    # via privileged moves where each step has exactly 1 privileged proc.
    # That's not quite right either. Let me use the standard definition:
    # A config is on the good cycle if it has exactly 1 privileged proc.
    good = set()
    for c in configs:
        priv_count = sum(1 for i in range(n) if is_privileged(n, c, i))
        if priv_count == 1:
            good.add(c)
    return good

# ── PhiFull computation via fixed-point iteration ────────────────────────
def compute_phi_full(n, verbose=True):
    """Compute PhiFull for all configs via Bellman-Ford style iteration.
    PhiFull(c) = max { fc(d) : d TP-reachable from c via bad steps }
    where TP-reachable means reachable via steps preserving TpInvariant,
    and we only follow steps that stay within bad configs.
    For good configs, PhiFull = 0 by convention."""
    t0 = time.time()
    configs = all_configs(n)
    good = build_good_cycle(n)
    bad = [c for c in configs if c not in good]
    bad_set = set(bad)

    if verbose:
        print(f"  n={n}: {len(configs)} configs, {len(good)} good, {len(bad)} bad")

    # Initialize PhiFull = fc for bad, 0 for good
    phi = {}
    for c in configs:
        if c in good:
            phi[c] = 0
        else:
            phi[c] = fc(c, n)

    # Build TP-preserving edges between bad configs
    # Edge c -> d if: c is bad, d is bad, d = fire(c, i), tp_invariant preserved
    tp_edges = defaultdict(list)  # c -> list of successors
    for c in bad:
        tp_c = tp_invariant(c, n)
        for i in range(n):
            if not is_privileged(n, c, i):
                continue
            d = fire(n, c, i)
            if d not in bad_set:
                continue
            if tp_invariant(d, n) == tp_c:
                tp_edges[c].append(d)

    if verbose:
        total_edges = sum(len(v) for v in tp_edges.values())
        print(f"  TP edges: {total_edges}")

    # Bellman-Ford: propagate max fc backwards
    # PhiFull(c) = max(fc(c), max over TP-successors d of PhiFull(d))
    for iteration in range(3 * n):
        changed = False
        for c in bad:
            old = phi[c]
            best = fc(c, n)
            for d in tp_edges[c]:
                if phi[d] > best:
                    best = phi[d]
            if best > old:
                phi[c] = best
                changed = True
        if not changed:
            if verbose:
                print(f"  PhiFull converged in {iteration + 1} iterations")
            break

    if verbose:
        elapsed = time.time() - t0
        phi_vals = sorted(set(phi[c] for c in bad))
        print(f"  PhiFull values for bad configs: {phi_vals}")
        print(f"  Elapsed: {elapsed:.1f}s")

    return phi, good

# ── Influence depth test ─────────────────────────────────────────────────
def test_influence_depth(n, phi, good, max_k=None):
    """Test if PhiFull is determined by the first/last k positions.
    k=3 means boundary 6-tuple only.
    k=4 means boundary + c[3] and c[n-4].
    etc.

    Also test: PhiFull conditioned on (window, tp_invariant)."""
    if max_k is None:
        max_k = (n - 1) // 2 + 1  # up to middle

    configs = [c for c in phi if c not in good]

    print(f"\n  Influence depth test at n={n}:")
    found_k = None
    for k in range(3, max_k + 1):
        if 2 * k >= n:
            print(f"    k={k}: window covers entire config (2k={2*k} >= n={n})")
            if found_k is None:
                found_k = n  # need full config
            break

        groups = defaultdict(set)
        for c in configs:
            window = c[:k] + c[n-k:]
            groups[window].add(phi[c])

        ambiguous = {w: vals for w, vals in groups.items() if len(vals) > 1}
        if not ambiguous:
            print(f"    k={k}: DETERMINES PhiFull (all {len(groups)} windows map to unique value)")
            if found_k is None:
                found_k = k
        else:
            worst_w = max(ambiguous, key=lambda w: max(ambiguous[w]) - min(ambiguous[w]))
            worst_vals = sorted(ambiguous[worst_w])
            count_amb = len(ambiguous)
            print(f"    k={k}: AMBIGUOUS — {count_amb} windows have multiple PhiFull values")
            print(f"           Worst: window={worst_w} -> PhiFull in {worst_vals}")

    # Also test: window + TP invariant
    print(f"\n  Influence depth test WITH TP invariant at n={n}:")
    found_k_tp = None
    for k in range(3, max_k + 1):
        if 2 * k >= n:
            print(f"    k={k}: window covers entire config")
            if found_k_tp is None:
                found_k_tp = n
            break

        groups = defaultdict(set)
        for c in configs:
            window = c[:k] + c[n-k:]
            tp = tp_invariant(c, n)
            groups[(window, tp)].add(phi[c])

        ambiguous = {w: vals for w, vals in groups.items() if len(vals) > 1}
        if not ambiguous:
            print(f"    k={k}: (window, TP) DETERMINES PhiFull ({len(groups)} groups)")
            if found_k_tp is None:
                found_k_tp = k
        else:
            worst_w = max(ambiguous, key=lambda w: max(ambiguous[w]) - min(ambiguous[w]))
            worst_vals = sorted(ambiguous[worst_w])
            count_amb = len(ambiguous)
            print(f"    k={k}: AMBIGUOUS — {count_amb} groups with multiple PhiFull values")
            print(f"           Worst spread: {worst_vals}")

    # Also test: window + deep copy pair count
    print(f"\n  Influence depth with DEEP COPY PAIR count at n={n}:")
    found_k_dcp = None
    for k in range(3, max_k + 1):
        if 2 * k >= n:
            if found_k_dcp is None:
                found_k_dcp = n
            break

        groups = defaultdict(set)
        for c in configs:
            window = c[:k] + c[n-k:]
            # Count deep copy pairs in the hidden interior
            dcp = 0
            for j in range(k, n - k):
                if c[j] == c[j-1] or c[j] == c[j+1]:
                    dcp += 1
            groups[(window, dcp)].add(phi[c])

        ambiguous = {w: vals for w, vals in groups.items() if len(vals) > 1}
        if not ambiguous:
            print(f"    k={k}: (window, #DCP) DETERMINES PhiFull ({len(groups)} groups)")
            if found_k_dcp is None:
                found_k_dcp = k
        else:
            count_amb = len(ambiguous)
            print(f"    k={k}: AMBIGUOUS — {count_amb} groups")

    return found_k, found_k_tp, found_k_dcp

# ── PhiFull-achieving config depth analysis ──────────────────────────────
def achiever_depth_analysis(n, phi, good):
    """For each bad config c, find a PhiFull-achieving config d*
    (TP-reachable from c with fc(d*) = PhiFull(c)).
    Measure how deep into the interior d* differs from c."""
    configs = all_configs(n)
    bad = [c for c in configs if c not in good]
    bad_set = set(bad)

    # Build TP-edges (again, or pass from above)
    tp_edges = defaultdict(list)
    for c in bad:
        tp_c = tp_invariant(c, n)
        for i in range(n):
            if not is_privileged(n, c, i):
                continue
            d = fire(n, c, i)
            if d not in bad_set:
                continue
            if tp_invariant(d, n) == tp_c:
                tp_edges[c].append(d)

    # For each c, BFS to find an achiever d* with fc(d*) = PhiFull(c)
    max_depth = 0
    depth_histogram = defaultdict(int)

    # Sample: only check configs where PhiFull > fc
    interesting = [c for c in bad if phi[c] > fc(c, n)]
    if not interesting:
        print(f"\n  n={n}: No config has PhiFull > fc (all configs ARE their own achiever)")
        return 0

    print(f"\n  Achiever depth analysis at n={n}: {len(interesting)} configs with PhiFull > fc")

    for c in interesting:
        target = phi[c]
        # BFS from c via TP-edges
        visited = {c}
        queue = [c]
        found = None
        while queue and found is None:
            next_queue = []
            for cfg in queue:
                for d in tp_edges[cfg]:
                    if d not in visited:
                        visited.add(d)
                        if fc(d, n) == target:
                            found = d
                            break
                        next_queue.append(d)
                if found:
                    break
            queue = next_queue

        if found is None:
            # Shouldn't happen if PhiFull is correct
            continue

        # Measure depth: how many interior positions differ?
        # Interior = positions 3..n-4
        diff_positions = [j for j in range(n) if c[j] != found[j]]
        interior_diffs = [j for j in diff_positions if 3 <= j <= n - 4]

        if interior_diffs:
            deepest = max(min(j, n - 1 - j) for j in interior_diffs)
        else:
            deepest = 0

        # Distance from boundary: min distance to position 0 or n-1
        max_bdist = 0
        for j in diff_positions:
            bdist = min(j, n - 1 - j)
            if bdist > max_bdist:
                max_bdist = bdist

        depth_histogram[max_bdist] += 1
        if max_bdist > max_depth:
            max_depth = max_bdist
            print(f"    New max depth {max_bdist}: c={c} -> d*={found}")
            print(f"      fc(c)={fc(c,n)}, PhiFull={target}, fc(d*)={fc(found,n)}")
            print(f"      Diff positions: {diff_positions}")

    print(f"  Max achiever depth: {max_depth}")
    print(f"  Depth histogram: {dict(sorted(depth_histogram.items()))}")
    return max_depth

# ── Main ─────────────────────────────────────────────────────────────────
def main():
    print("=" * 70)
    print("PhiFull INFLUENCE DEPTH INVESTIGATION")
    print("=" * 70)

    results = {}
    for n in [9, 10, 11]:
        print(f"\n{'─'*60}")
        print(f"n = {n}")
        print(f"{'─'*60}")

        phi, good = compute_phi_full(n)
        k_raw, k_tp, k_dcp = test_influence_depth(n, phi, good)
        d = achiever_depth_analysis(n, phi, good)
        results[n] = (k_raw, k_tp, k_dcp, d)

    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")
    for n, (k_raw, k_tp, k_dcp, d) in results.items():
        print(f"  n={n}: window-only k={k_raw}, (window,TP) k={k_tp}, (window,#DCP) k={k_dcp}, achiever depth={d}")

if __name__ == "__main__":
    main()
