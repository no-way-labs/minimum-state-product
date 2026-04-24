#!/usr/bin/env python3
"""Convergence proof investigation — Part 5.

PROOF STRATEGY:
If freezing any single position p gives a DAG with depth D_p, then
any simple cycle of length T must satisfy:
  k_p >= T / (D_p + 1)  for each p (where k_p = # firings of p in cycle)
  T = Σ k_p >= T * Σ 1/(D_p + 1)
If Σ 1/(D_p + 1) > 1, no cycle can exist!

Also: explore if freezing any position gives DAG for ALL n (inductive argument).
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import deque, defaultdict
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system


def get_full_graph(n):
    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(c for c in all_configs if c not in good_set)
    return ms, fs, good_set, bad_set


def compute_frozen_depth(bad_set, fs, n, frozen_pos):
    """Compute DAG depth when position frozen_pos is excluded from firing."""
    # Build adjacency
    in_deg = {c: 0 for c in bad_set}
    adj = {c: [] for c in bad_set}

    for c in bad_set:
        for i in range(n):
            if i == frozen_pos:
                continue
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    adj[c].append(succ)
                    in_deg[succ] += 1

    # Topological sort
    q = deque(c for c in bad_set if in_deg[c] == 0)
    topo = []
    while q:
        c = q.popleft()
        topo.append(c)
        for s in adj[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)

    if len(topo) != len(bad_set):
        return -1  # Not a DAG!

    # Compute depth (longest path from each node)
    rank = {}
    for c in reversed(topo):
        rank[c] = max((rank[s] + 1 for s in adj[c]), default=0)

    return max(rank.values()) if rank else 0


def compute_frozen_depth_pair(bad_set, fs, n, frozen1, frozen2):
    """Compute DAG depth when two positions are frozen."""
    in_deg = {c: 0 for c in bad_set}
    adj = {c: [] for c in bad_set}

    for c in bad_set:
        for i in range(n):
            if i == frozen1 or i == frozen2:
                continue
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    adj[c].append(succ)
                    in_deg[succ] += 1

    q = deque(c for c in bad_set if in_deg[c] == 0)
    topo = []
    while q:
        c = q.popleft()
        topo.append(c)
        for s in adj[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)

    if len(topo) != len(bad_set):
        return -1

    rank = {}
    for c in reversed(topo):
        rank[c] = max((rank[s] + 1 for s in adj[c]), default=0)

    return max(rank.values()) if rank else 0


def main():
    # ================================================================
    # PART 1: FROZEN-POSITION DAG DEPTHS
    # ================================================================
    print("=" * 95)
    print("PART 1: FROZEN-POSITION DAG DEPTHS")
    print("=" * 95)

    # For each n, compute D_p for each position p
    # Also compute the full DAG depth for comparison

    results = {}  # n -> {p: D_p}

    for nv in range(5, 13):
        ms, fs, good_set, bad_set = get_full_graph(nv)
        n = nv

        # Full DAG depth
        full_depth = compute_frozen_depth(bad_set, fs, n, -1)  # -1 = freeze nothing

        # Wait, -1 won't match any position, so no position is frozen
        # Actually, let me rewrite to handle this cleanly

        # Full depth
        in_deg = {c: 0 for c in bad_set}
        adj = {c: [] for c in bad_set}
        for c in bad_set:
            for i in range(n):
                L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c); lst[i] = new_S; succ = tuple(lst)
                    if succ in bad_set:
                        adj[c].append(succ)
                        in_deg[succ] += 1

        q = deque(c for c in bad_set if in_deg[c] == 0)
        topo = []
        while q:
            c = q.popleft()
            topo.append(c)
            for s in adj[c]:
                in_deg[s] -= 1
                if in_deg[s] == 0:
                    q.append(s)

        rank = {}
        for c in reversed(topo):
            rank[c] = max((rank[s] + 1 for s in adj[c]), default=0)
        full_depth = max(rank.values()) if rank else 0

        depths = {}
        for p in range(n):
            depths[p] = compute_frozen_depth(bad_set, fs, n, p)

        results[nv] = depths

        # Harmonic criterion
        harmonic_sum = sum(1.0 / (depths[p] + 1) for p in range(n))

        print(f"\nn={nv}: full_depth={full_depth}, |bad|={len(bad_set)}")
        print(f"  Position depths: ", end="")
        for p in range(n):
            tbl = 'bot' if p == 0 else 'low' if p == 1 else \
                  'mid' if p < n-2 else 'high' if p == n-2 else 'top'
            print(f"P{p}({tbl})={depths[p]}", end="  ")
        print()
        print(f"  Harmonic sum Σ 1/(D_p+1) = {harmonic_sum:.6f}")
        if harmonic_sum > 1:
            print(f"  *** HARMONIC CRITERION SATISFIED: NO CYCLE POSSIBLE! ***")
        else:
            print(f"  Harmonic criterion NOT satisfied ({harmonic_sum:.4f} ≤ 1)")

        if 4 * 3 ** (nv - 2) > 500000:
            break

    # ================================================================
    # PART 2: DEPTH PATTERNS
    # ================================================================
    print("\n" + "=" * 95)
    print("PART 2: DEPTH PATTERN ANALYSIS")
    print("=" * 95)

    print(f"\n{'n':>3}  {'full':>6}  ", end="")
    for label in ['D_bot', 'D_low', 'D_mid(2)', 'D_mid(mid)', 'D_high', 'D_top']:
        print(f"{label:>10}", end="")
    print()
    print("-" * 80)

    for nv in sorted(results.keys()):
        depths = results[nv]
        n = nv

        # Full depth (formula)
        full = (3*n*n - 4*n - 11) // 4

        # Get representative depths
        d_bot = depths[0]
        d_low = depths[1]
        d_mid2 = depths[2] if n > 4 else '-'
        d_mid_mid = depths[n//2] if n > 5 else d_mid2
        d_high = depths[n-2]
        d_top = depths[n-1]

        print(f"{nv:>3}  {full:>6}  {d_bot:>10}{d_low:>10}"
              f"{str(d_mid2):>10}{str(d_mid_mid):>10}{d_high:>10}{d_top:>10}")

    # ================================================================
    # PART 3: FROZEN DEPTH FORMULAS
    # ================================================================
    print("\n" + "=" * 95)
    print("PART 3: FROZEN DEPTH FORMULA SEARCH")
    print("=" * 95)

    # For each position type, try to fit D_p as a function of n
    # Candidates: an² + bn + c

    for pos_type in ['bot', 'low', 'mid_first', 'mid_center', 'high', 'top']:
        vals = []
        for nv in sorted(results.keys()):
            n = nv
            depths = results[nv]
            if pos_type == 'bot':
                vals.append((n, depths[0]))
            elif pos_type == 'low':
                vals.append((n, depths[1]))
            elif pos_type == 'mid_first':
                if n >= 6:
                    vals.append((n, depths[2]))
            elif pos_type == 'mid_center':
                if n >= 7:
                    vals.append((n, depths[n // 2]))
            elif pos_type == 'high':
                vals.append((n, depths[n - 2]))
            elif pos_type == 'top':
                vals.append((n, depths[n - 1]))

        if len(vals) < 3:
            continue

        # Try quadratic fit: D = an² + bn + c
        # Using three points to solve
        ns = [v[0] for v in vals]
        ds = [v[1] for v in vals]

        print(f"\n  {pos_type}: {list(zip(ns, ds))}")

        # Check differences
        diffs1 = [ds[i+1] - ds[i] for i in range(len(ds)-1)]
        diffs2 = [diffs1[i+1] - diffs1[i] for i in range(len(diffs1)-1)]
        print(f"    First differences: {diffs1}")
        print(f"    Second differences: {diffs2}")

        # If second differences are constant, it's quadratic
        if len(set(diffs2)) == 1 and diffs2[0] != 0:
            a2 = diffs2[0]  # 2a
            a = a2 / 2
            # From first point: D = a*n² + b*n + c
            # First diff: D(n+1) - D(n) = a(2n+1) + b = diffs1[0] at n = ns[0]
            b = diffs1[0] - a * (2 * ns[0] + 1)
            c = ds[0] - a * ns[0] ** 2 - b * ns[0]
            print(f"    Quadratic fit: D = {a}n² + {b}n + {c}")

            # Verify
            all_match = True
            for n_val, d_val in vals:
                pred = a * n_val ** 2 + b * n_val + c
                if pred != d_val:
                    all_match = False
                    print(f"    MISMATCH at n={n_val}: predicted {pred}, actual {d_val}")
            if all_match:
                print(f"    ✓ Formula matches ALL values!")
        elif len(set(diffs1)) == 1:
            # Linear fit
            slope = diffs1[0]
            intercept = ds[0] - slope * ns[0]
            print(f"    Linear fit: D = {slope}n + {intercept}")
            all_match = all(slope * n_val + intercept == d_val for n_val, d_val in vals)
            if all_match:
                print(f"    ✓ Formula matches ALL values!")

    # ================================================================
    # PART 4: CAN WE USE PAIRS TO STRENGTHEN THE HARMONIC CRITERION?
    # ================================================================
    print("\n" + "=" * 95)
    print("PART 4: PAIR-FROZEN DEPTHS (for small n)")
    print("=" * 95)

    for nv in [6, 7, 8]:
        ms, fs, good_set, bad_set = get_full_graph(nv)
        n = nv
        print(f"\nn={nv}:")

        # For a cycle, we need k_p1 + k_p2 >= T/(D_{p1,p2} + 1) + ...
        # Actually, the pair-frozen criterion is different.
        # If freezing (p1, p2) gives DAG with depth D_{p1,p2}, then
        # in any cycle, the number of non-{p1,p2} transitions between
        # consecutive (p1 or p2) firings is <= D_{p1,p2}.
        # But this is harder to use cleanly.

        # Instead, just report the depths and look for patterns
        for p1 in range(n):
            for p2 in range(p1 + 1, n):
                d = compute_frozen_depth_pair(bad_set, fs, n, p1, p2)
                if d < 0:
                    print(f"  Freeze (P{p1}, P{p2}): NOT DAG!")
                else:
                    # Only report if interesting (much smaller than full depth)
                    full_d = results[nv]
                    pass  # Collect for summary

        # Summary: min and max pair depths
        pair_depths = {}
        for p1 in range(n):
            for p2 in range(p1 + 1, n):
                d = compute_frozen_depth_pair(bad_set, fs, n, p1, p2)
                pair_depths[(p1, p2)] = d

        min_pair = min(pair_depths.values())
        max_pair = max(pair_depths.values())
        full_d = max(results[nv].values())

        print(f"  Full depth: {full_d}")
        print(f"  Single-frozen depths: {[results[nv][p] for p in range(n)]}")
        print(f"  Pair-frozen depths: min={min_pair}, max={max_pair}")

        # Show all pair depths
        for (p1, p2), d in sorted(pair_depths.items()):
            if d <= min_pair + 2:
                print(f"    Freeze (P{p1}, P{p2}): depth={d}")

    # ================================================================
    # PART 5: ALTERNATIVE CYCLE BOUND — USING MINIMUM k_p
    # ================================================================
    print("\n" + "=" * 95)
    print("PART 5: CYCLE LENGTH BOUNDS")
    print("=" * 95)

    for nv in sorted(results.keys()):
        depths = results[nv]
        n = nv

        # For a cycle of length T:
        # k_p >= 2 for all p (each position fires at least twice)
        # T - k_p <= k_p * D_p  =>  T <= k_p * (D_p + 1)
        # So k_p >= T / (D_p + 1)
        #
        # Combined with k_p >= 2:
        # T = Σ k_p >= Σ max(2, T/(D_p+1))
        #
        # If all D_p are large (D_p >> T/2), then k_p >= 2 dominates:
        # T >= 2n
        #
        # If some D_p are small, T/(D_p+1) dominates:
        # E.g., if D_p = 0, then k_p >= T, so T = Σ k_q >= T + Σ_{q≠p} 2 = T + 2(n-1)
        # => 0 >= 2(n-1), contradiction!
        #
        # More generally, the tightest constraint comes from the position with
        # the SMALLEST D_p.

        min_D = min(depths.values())
        max_D = max(depths.values())
        full_depth = (3*n*n - 4*n - 11) // 4

        # Lower bound on T from harmonic sum
        harmonic = sum(1.0 / (depths[p] + 1) for p in range(n))

        # If harmonic > 1: impossible
        # If harmonic <= 1: minimum T from k_p >= max(2, T/(D_p+1)):
        # T >= 2n (from k_p >= 2)
        # For minimum T, check if 2n satisfies all constraints:
        # k_p = 2 for all p => T = 2n
        # Constraint: T - k_p <= k_p * D_p => 2n - 2 <= 2 * D_p => D_p >= n - 1

        print(f"\nn={nv}: min_D={min_D}, max_D={max_D}, full={full_depth}, "
              f"harmonic={harmonic:.4f}")
        print(f"  Minimum cycle T=2n={2*n} requires: all D_p >= n-1 = {n-1}")
        print(f"  Positions where D_p < n-1:", end=" ")
        blocking = [p for p in range(n) if depths[p] < n - 1]
        if blocking:
            for p in blocking:
                print(f"P{p}(D={depths[p]})", end=" ")
            print()
        else:
            print("NONE — 2n-length cycle not ruled out")

        # What cycle length is actually achievable given the D_p constraints?
        # T >= 2n, and T <= k_p * (D_p + 1)
        # For T = 2n: k_p >= 2n/(D_p + 1)
        # Total: Σ k_p >= 2n * Σ 1/(D_p + 1) = 2n * harmonic
        # Need: Σ k_p = T = 2n
        # So: 2n >= 2n * harmonic => 1 >= harmonic (always true if harmonic <= 1)

    # ================================================================
    # PART 6: THE REAL CRITERION — DO ALL D_p GROW WITH n?
    # ================================================================
    print("\n" + "=" * 95)
    print("PART 6: FROZEN DEPTH GROWTH RATES")
    print("=" * 95)

    print(f"\n{'n':>3}", end="")
    for p in range(max(len(results[k]) for k in results)):
        print(f"  {'D_'+str(p):>6}", end="")
    print(f"  {'sum(1/(D+1))':>14}")
    print("-" * 100)

    for nv in sorted(results.keys()):
        depths = results[nv]
        n = nv
        harmonic = sum(1.0 / (depths[p] + 1) for p in range(n))
        print(f"{nv:>3}", end="")
        for p in range(n):
            print(f"  {depths[p]:>6}", end="")
        # Pad remaining columns
        for _ in range(max(len(results[k]) for k in results) - n):
            print(f"  {'':>6}", end="")
        print(f"  {harmonic:>14.6f}")

    # ================================================================
    # PART 7: KEY TEST — DOES FREEZING AN INTERIOR POSITION
    # MAKE THE GRAPH "MUCH SIMPLER"?
    # ================================================================
    print("\n" + "=" * 95)
    print("PART 7: INTERIOR FROZEN — STRUCTURAL ANALYSIS")
    print("=" * 95)

    for nv in [7, 8, 9]:
        ms, fs, good_set, bad_set = get_full_graph(nv)
        n = nv

        # When we freeze the center position, how many configs become "sinks"
        # (all bad successors require the frozen position)?
        center = n // 2
        configs_with_only_center_privs = 0
        configs_with_mixed_privs = 0
        configs_with_no_center_priv = 0

        for c in bad_set:
            has_center_priv = False
            has_non_center_priv = False
            for i in range(n):
                L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
                if fs[i](L, S, R) != S:
                    if i == center:
                        has_center_priv = True
                    else:
                        has_non_center_priv = True

            if has_center_priv and not has_non_center_priv:
                configs_with_only_center_privs += 1
            elif has_center_priv and has_non_center_priv:
                configs_with_mixed_privs += 1
            else:
                configs_with_no_center_priv += 1

        print(f"\nn={nv}, frozen P{center}:")
        print(f"  Only P{center} privileged: {configs_with_only_center_privs}")
        print(f"  P{center} + others privileged: {configs_with_mixed_privs}")
        print(f"  P{center} not privileged: {configs_with_no_center_priv}")
        print(f"  New sinks (when P{center} frozen): {configs_with_only_center_privs}")

    # ================================================================
    # PART 8: THE CRITICAL QUESTION — CAN WE PROVE FROZEN-DAG FOR ALL n?
    # ================================================================
    print("\n" + "=" * 95)
    print("PART 8: FROZEN-DAG PROOF APPROACH")
    print("=" * 95)

    # Key observation: when we freeze position p, we're looking at the
    # dynamics of n-1 positions with one position acting as a fixed
    # "environment variable" that never changes.
    #
    # For T_mid positions: freezing one of them means its neighbors see
    # a fixed left or right value. This makes their targets more constrained.
    #
    # HYPOTHESIS: the frozen-p system is equivalent to a "chain" system
    # (not a ring) where position p acts as a "wall".
    # A chain of T_mid processors with fixed boundaries should be easier
    # to analyze than a ring.

    # Test: does the frozen-p system decompose into two independent chains?
    # When position p is frozen, it splits the ring into two arcs:
    # Arc 1: positions (p+1, p+2, ..., p-1)  (going clockwise)
    # In this arc, position p is a "read-only" boundary.
    # Transitions in this arc can't create cycles because... can they?
    # Actually, the arc IS the whole ring minus p, which is a single connected chain.

    # But the key question is: can we prove the chain has the DAG property?
    # For a chain with fixed boundary values, the dynamics might be simpler.

    # Let's check: in the frozen-p system, do transitions at position i
    # only depend on neighbors in the chain (which don't include p, except
    # as a fixed boundary)?

    # For position i with i != p:
    # L = c[(i-1) % n], R = c[(i+1) % n]
    # If i-1 = p or i+1 = p, then one neighbor is fixed (= c[p], which doesn't change).
    # Otherwise, both neighbors are dynamic (in the chain).

    # So the frozen-p system IS a chain with:
    # - Fixed left boundary at c[p] (for position p+1)
    # - Fixed right boundary at c[p] (for position p-1)
    # - Position p-1's right neighbor is p, which is fixed
    # - Position p+1's left neighbor is p, which is fixed
    # But the VALUES at p might be any of {0,1,2} (for T_mid) or {0,1} (for binary)

    # Actually, c[p] is NOT fixed across configs — different bad configs have
    # different values of c[p]. So the "fixed boundary" has different values
    # for different configs. This means the chain dynamics are NOT the same
    # for all configs.

    # However, we can PARTITION by c[p]:
    # For each value v of c[p], the configs with c[p] = v form a sub-chain
    # with fixed boundary value v.

    print("\nTest: frozen P{center}, partitioned by c[center]:")
    for nv in [7, 8, 9]:
        ms, fs, good_set, bad_set = get_full_graph(nv)
        n = nv
        center = n // 2

        for v in range(ms[center]):
            partition = set(c for c in bad_set if c[center] == v)
            if not partition:
                continue

            # Build frozen-center graph within this partition
            in_deg = {c: 0 for c in partition}
            adj = {c: [] for c in partition}
            for c in partition:
                for i in range(n):
                    if i == center:
                        continue
                    L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
                    new_S = fs[i](L, S, R)
                    if new_S != S:
                        lst = list(c); lst[i] = new_S; succ = tuple(lst)
                        if succ in partition:
                            adj[c].append(succ)
                            in_deg[succ] += 1

            q = deque(c for c in partition if in_deg[c] == 0)
            count = 0
            max_depth = 0
            depth = {}
            topo = []
            while q:
                c = q.popleft()
                count += 1
                topo.append(c)
                for s in adj[c]:
                    in_deg[s] -= 1
                    if in_deg[s] == 0:
                        q.append(s)

            is_dag = (count == len(partition))

            if is_dag:
                for c in reversed(topo):
                    depth[c] = max((depth[s] + 1 for s in adj[c]), default=0)
                max_depth = max(depth.values()) if depth else 0

            print(f"  n={nv}, c[{center}]={v}: {len(partition)} configs, "
                  f"DAG? {'YES' if is_dag else 'NO'}, depth={max_depth}")


if __name__ == "__main__":
    main()
