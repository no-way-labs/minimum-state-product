#!/usr/bin/env python3
"""Convergence proof investigation — Part 2.

Deeper analysis:
1. Trace longest DAG paths and analyze structure
2. Analyze what makes "deep" configs hard to converge
3. Wave propagation analysis — can counter-propagating waves form cycles?
4. Boundary-conditioned potential functions
5. Amortized argument: track "work" created vs destroyed per transition
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import deque, defaultdict, Counter
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system


def get_bad_graph(n):
    """Build the bad-config graph."""
    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(c for c in all_configs if c not in good_set)

    # Build adjacency
    adj = {c: [] for c in bad_set}
    adj_rev = {c: [] for c in bad_set}
    exits = {c: [] for c in bad_set}  # bad→good transitions

    for c in bad_set:
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c)
                lst[i] = new_S
                succ = tuple(lst)
                if succ in bad_set:
                    adj[c].append((succ, i))
                    adj_rev[succ].append((c, i))
                else:
                    exits[c].append((succ, i))

    return ms, fs, good_set, bad_set, adj, adj_rev, exits


def compute_ranks(bad_set, adj):
    """Compute topological rank (longest path to sink) for each node."""
    # First compute in-degrees for Kahn's algorithm
    in_deg = {c: 0 for c in bad_set}
    adj_simple = {c: [] for c in bad_set}
    for c in bad_set:
        for succ, mover in adj[c]:
            adj_simple[c].append(succ)
            in_deg[succ] += 1

    q = deque(c for c in bad_set if in_deg[c] == 0)
    topo = []
    while q:
        c = q.popleft()
        topo.append(c)
        for s in adj_simple[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)

    # Compute rank = longest path to a sink (config with all successors in good set)
    rank = {}
    for c in reversed(topo):
        succs_in_bad = [s for s in adj_simple[c]]
        if not succs_in_bad:
            rank[c] = 0
        else:
            rank[c] = max(rank[s] + 1 for s in succs_in_bad)
    return rank, topo


def trace_longest_path(start, adj, rank):
    """Trace the longest path from start following highest-rank successors."""
    path = [start]
    movers = []
    current = start
    while True:
        best_succ = None
        best_rank = -1
        best_mover = -1
        for succ, mover in adj[current]:
            if succ in rank and rank[succ] > best_rank:
                best_succ = succ
                best_rank = rank[succ]
                best_mover = mover
        if best_succ is None or best_rank < 0:
            break
        path.append(best_succ)
        movers.append(best_mover)
        current = best_succ
    return path, movers


def main():
    # ================================================================
    # PART 1: LONGEST PATH ANALYSIS
    # ================================================================
    print("=" * 90)
    print("PART 1: LONGEST DAG PATH ANALYSIS")
    print("=" * 90)

    for nv in [5, 6, 7]:
        ms, fs, good_set, bad_set, adj, adj_rev, exits = get_bad_graph(nv)
        rank, topo = compute_ranks(bad_set, adj)
        max_rank = max(rank.values())

        # Find config(s) at maximum rank
        max_rank_configs = [c for c in bad_set if rank[c] == max_rank]

        print(f"\nn={nv}: max_depth={max_rank}, {len(max_rank_configs)} configs at max depth")

        # Trace longest path
        start = max_rank_configs[0]
        path, movers = trace_longest_path(start, adj, rank)
        print(f"  Longest path from {start}:")
        for i, c in enumerate(path[:30]):
            mv = movers[i] if i < len(movers) else -1
            r = rank.get(c, '?')
            # What does this config look like?
            if i < len(movers):
                print(f"    step {i:3d}: {c} rank={r} →[P{mv}]")
            else:
                print(f"    step {i:3d}: {c} rank={r} (end)")
                # Check exits
                if c in exits:
                    for succ, m in exits[c]:
                        if succ in good_set:
                            print(f"             → GOOD via P{m}: {succ}")
        if len(path) > 30:
            print(f"    ... ({len(path)} total steps)")
            # Print last few
            for i in range(max(30, len(path)-5), len(path)):
                c = path[i]
                mv = movers[i] if i < len(movers) else -1
                r = rank.get(c, '?')
                if i < len(movers):
                    print(f"    step {i:3d}: {c} rank={r} →[P{mv}]")
                else:
                    print(f"    step {i:3d}: {c} rank={r} (end)")

    # ================================================================
    # PART 2: WHAT MAKES DEEP CONFIGS HARD?
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 2: DEEP CONFIG CHARACTERIZATION")
    print("=" * 90)

    for nv in [6, 7, 8]:
        ms, fs, good_set, bad_set, adj, adj_rev, exits = get_bad_graph(nv)
        rank, topo = compute_ranks(bad_set, adj)
        max_rank = max(rank.values())

        # Partition by rank ranges
        quarters = [max_rank * i // 4 for i in range(5)]
        for qi in range(4):
            lo, hi = quarters[qi], quarters[qi + 1]
            configs_in_range = [c for c in bad_set if lo <= rank[c] < hi]
            if not configs_in_range:
                continue

            # Analyze: sum, frontier, count_2s, privilege count
            avg_sum = sum(sum(c) for c in configs_in_range) / len(configs_in_range)
            avg_frontier = sum(
                sum(1 for i in range(nv) if c[i] != c[(i+1) % nv])
                for c in configs_in_range
            ) / len(configs_in_range)
            avg_2s = sum(
                sum(1 for i in range(1, nv-1) if c[i] == 2)
                for c in configs_in_range
            ) / len(configs_in_range)

            # Average privilege count
            avg_priv = 0
            for c in configs_in_range:
                priv = 0
                for i in range(nv):
                    L = c[(i-1) % nv]
                    S = c[i]
                    R = c[(i+1) % nv]
                    if fs[i](L, S, R) != S:
                        priv += 1
                avg_priv += priv
            avg_priv /= len(configs_in_range)

            print(f"  n={nv} rank [{lo},{hi}): {len(configs_in_range)} configs, "
                  f"avg_sum={avg_sum:.2f}, avg_front={avg_frontier:.2f}, "
                  f"avg_2s={avg_2s:.2f}, avg_priv={avg_priv:.2f}")

    # ================================================================
    # PART 3: BOUNDARY VALUE ANALYSIS
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 3: RANK DISTRIBUTION BY BOUNDARY VALUES")
    print("=" * 90)

    for nv in [6, 7]:
        ms, fs, good_set, bad_set, adj, adj_rev, exits = get_bad_graph(nv)
        rank, topo = compute_ranks(bad_set, adj)

        # Group by boundary values (c[0], c[n-1])
        boundary_ranks = defaultdict(list)
        for c in bad_set:
            key = (c[0], c[nv-1])
            boundary_ranks[key].append(rank[c])

        print(f"\nn={nv}:")
        for key in sorted(boundary_ranks.keys()):
            ranks = boundary_ranks[key]
            print(f"  (c[0]={key[0]}, c[{nv-1}]={key[1]}): "
                  f"count={len(ranks)}, max_rank={max(ranks)}, "
                  f"avg_rank={sum(ranks)/len(ranks):.1f}")

    # ================================================================
    # PART 4: WAVE PROPAGATION ANALYSIS
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 4: WAVE PROPAGATION IN LONGEST PATHS")
    print("=" * 90)

    nv = 7
    ms, fs, good_set, bad_set, adj, adj_rev, exits = get_bad_graph(nv)
    rank, topo = compute_ranks(bad_set, adj)
    max_rank = max(rank.values())

    start = [c for c in bad_set if rank[c] == max_rank][0]
    path, movers = trace_longest_path(start, adj, rank)

    # Track per-position value changes along the path
    print(f"n={nv}: tracing {len(path)}-step path")
    print(f"\nMover sequence: {movers[:50]}{'...' if len(movers)>50 else ''}")

    # Count transitions by type along the path
    trans_types = Counter()
    for i in range(len(movers)):
        c = path[i]
        cp = path[i + 1]
        mv = movers[i]
        old_v = c[mv]
        new_v = cp[mv]
        L = c[(mv - 1) % nv]
        R = c[(mv + 1) % nv]
        trans_types[(mv, old_v, new_v)] += 1

    print(f"\nTransition types along longest path:")
    for k in sorted(trans_types.keys()):
        pos, old_v, new_v = k
        if pos == 0:
            tbl = "bot"
        elif pos == 1:
            tbl = "low"
        elif pos < nv - 2:
            tbl = "mid"
        elif pos == nv - 2:
            tbl = "high"
        else:
            tbl = "top"
        print(f"  P{pos} ({tbl}): {old_v}→{new_v} × {trans_types[k]}")

    # ================================================================
    # PART 5: "RIGHTWARD 1-FRONT" POTENTIAL
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 5: RIGHTWARD 1-FRONT POTENTIAL")
    print("=" * 90)

    # Idea: define the "1-front" as the rightmost position that has value ≥1
    # and the "2-front" as the leftmost position that has value 2.
    # These fronts should progress monotonically in the good cycle.

    for nv in [5, 6, 7, 8]:
        ms, fs, good_set, bad_set, adj, adj_rev, exits = get_bad_graph(nv)

        transitions = []
        for c in bad_set:
            for i in range(nv):
                L = c[(i - 1) % nv]
                S = c[i]
                R = c[(i + 1) % nv]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c)
                    lst[i] = new_S
                    succ = tuple(lst)
                    if succ in bad_set:
                        transitions.append((c, succ, i))

        def one_front(c):
            """Rightmost position with value >= 1, or -1 if all 0."""
            for i in range(nv - 1, -1, -1):
                if c[i] >= 1:
                    return i
            return -1

        def two_front(c):
            """Leftmost position with value 2 (among ternary), or n if none."""
            for i in range(1, nv - 1):
                if c[i] == 2:
                    return i
            return nv

        def rightward_1_count(c):
            """Count of positions i where c[i] >= 1, weighted by position."""
            return sum((i + 1) for i in range(nv) if c[i] >= 1)

        def leftward_2_count(c):
            """Count of ternary positions i with value 2, weighted by (n-i)."""
            return sum((nv - i) for i in range(1, nv - 1) if c[i] == 2)

        # Test: (rightward_1_count, leftward_2_count) lexicographic
        viol = 0
        for c, cp, mv in transitions:
            r1c = rightward_1_count(c)
            r1cp = rightward_1_count(cp)
            l2c = leftward_2_count(c)
            l2cp = leftward_2_count(cp)
            if (r1c, l2c) <= (r1cp, l2cp):
                viol += 1
        print(f"  n={nv}: lex(rightward_1, leftward_2): {viol} violations / {len(transitions)} "
              f"({100*viol/len(transitions):.1f}%)")

        # Test: weighted sum
        for a, b in [(1, 0), (0, 1), (1, 1), (2, 1), (1, 2), (3, 1), (1, 3)]:
            viol = 0
            for c, cp, mv in transitions:
                sc = a * rightward_1_count(c) + b * leftward_2_count(c)
                scp = a * rightward_1_count(cp) + b * leftward_2_count(cp)
                if sc <= scp:
                    viol += 1
            if viol < len(transitions) * 0.2:
                print(f"  n={nv}: {a}*R1 + {b}*L2: {viol} violations ({100*viol/len(transitions):.1f}%)")

    # ================================================================
    # PART 6: POSITION-WEIGHTED VALUE SUM
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 6: POSITION-WEIGHTED VALUE SUM")
    print("=" * 90)

    # In the good cycle, the 3 phases are:
    # Phase 1: values increase L→R (filling 1s)
    # Phase 2: values change to 2 R→L
    # Phase 3: values reset to 0 L→R
    # Try: Φ(c) = Σ w_i * c[i] where weights reflect the "ideal" flow direction

    for nv in [5, 6, 7, 8]:
        ms, fs, good_set, bad_set, adj, adj_rev, exits = get_bad_graph(nv)
        transitions = []
        for c in bad_set:
            for i in range(nv):
                L = c[(i-1) % nv]; S = c[i]; R = c[(i+1) % nv]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c); lst[i] = new_S; succ = tuple(lst)
                    if succ in bad_set:
                        transitions.append((c, succ, i))

        # Try various weight patterns
        best_viol = len(transitions)
        best_weights = None
        for w_type in ['linear', 'reverse', 'quadratic', 'v_shape', 'hat']:
            if w_type == 'linear':
                weights = [i for i in range(nv)]
            elif w_type == 'reverse':
                weights = [nv - 1 - i for i in range(nv)]
            elif w_type == 'quadratic':
                weights = [i * i for i in range(nv)]
            elif w_type == 'v_shape':
                mid = nv // 2
                weights = [abs(i - mid) for i in range(nv)]
            elif w_type == 'hat':
                mid = nv // 2
                weights = [mid - abs(i - mid) for i in range(nv)]

            viol = 0
            for c, cp, mv in transitions:
                sc = sum(weights[i] * c[i] for i in range(nv))
                scp = sum(weights[i] * cp[i] for i in range(nv))
                if sc <= scp:
                    viol += 1
            pct = 100 * viol / len(transitions) if transitions else 0
            if pct < 20:
                print(f"  n={nv} {w_type:>10}: {viol} violations ({pct:.1f}%)")
            if viol < best_viol:
                best_viol = viol
                best_weights = w_type
        print(f"  n={nv} best: {best_weights} with {best_viol} violations "
              f"({100*best_viol/len(transitions):.1f}%)")

    # ================================================================
    # PART 7: CYCLE IMPOSSIBILITY — FIRING SEQUENCE CONSTRAINTS
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 7: MINIMUM CYCLE REQUIREMENTS")
    print("=" * 90)

    # For a cycle to exist, each position that fires must fire ≥2 times
    # (since after one firing it's at its target, needs neighbor change to fire again).
    # Between two firings of position i, at least one neighbor must fire.
    # Track: what are the minimal "firing patterns" for a cycle?

    # At a single T_mid position i with current value S and neighbors (L,R):
    # Fire: S → T_mid(L,S,R) = S' ≠ S
    # For i to fire again: need T_mid(L', S', R') ≠ S' for some new L', R'
    # And for the cycle: must return S' → S eventually

    # So we need: S → S' (with neighbors L,R) and later S' → S'' (with L',R')
    # and eventually back to S.
    # With the no-2-cycle property: T_mid(L,S,R) = S' and T_mid(L,S',R) ≠ S
    # (because S' is a fixed point of f_{L,R}).
    # So to get S' → something ≠ S', must change neighbors.

    print("\nT_mid: for each value S, what (L,R) pairs make S a fixed point?")
    for S in range(3):
        fps = []
        for L in range(3):
            for R in range(3):
                if T_mid[(L, S, R)] == S:
                    fps.append((L, R))
        print(f"  S={S} is fixed point at: {fps}")

    print("\nT_mid: for each value S, what (L,R) pairs make S privileged (→ what)?")
    for S in range(3):
        privs = []
        for L in range(3):
            for R in range(3):
                out = T_mid[(L, S, R)]
                if out != S:
                    privs.append((L, R, out))
        print(f"  S={S} privileged at: {[(l,r,o) for l,r,o in privs]}")

    # For a cycle involving a single T_mid position with value oscillating:
    # Need S=0: 0 → ? with some (L,R), then ? → 0 with different (L',R')
    # Path 0→1→0: need L=1 for 0→1, then need (L',R') where 1→0
    #   1→0 requires (0,0), (0,2), or (2,1,1)→0 i.e. L'∈{0}, or (L'=2,R'=1)
    #   So L changes from 1 to 0 or 2: left neighbor must fire
    # Path 0→2→0: need (L=2,R=2) for 0→2, then (L',R') where 2→0
    #   2→0 requires R'∈{0,2} and various L: (0,0), (0,2), (1,0), (2,0)
    #   So can keep R=2 but change L, or change R
    # Path 0→1→2→0: 0→1 needs L=1; 1→2 needs R'=2; 2→0 needs various

    print("\n\nT_mid oscillation paths (for cycle feasibility):")
    for start_val in range(3):
        print(f"\n  Starting at S={start_val}:")
        # Find all possible "next values" and required neighbors
        for L in range(3):
            for R in range(3):
                out = T_mid[(L, start_val, R)]
                if out != start_val:
                    # Now from out, what transitions return to start_val?
                    for L2 in range(3):
                        for R2 in range(3):
                            out2 = T_mid[(L2, out, R2)]
                            if out2 == start_val:
                                print(f"    S={start_val}→{out} via (L={L},R={R}), "
                                      f"then {out}→{start_val} via (L={L2},R={R2})")
                                # What neighbor changes are needed?
                                l_change = L != L2
                                r_change = R != R2
                                print(f"      Requires: L {'changes' if l_change else 'same'} "
                                      f"({L}→{L2}), R {'changes' if r_change else 'same'} "
                                      f"({R}→{R2})")

    # ================================================================
    # PART 8: GLOBAL STATE ENERGY — PAIRWISE DISAGREEMENT
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 8: PAIRWISE DISAGREEMENT ENERGY")
    print("=" * 90)

    # Define energy based on pairs of adjacent values:
    # E(c) = Σ_{i} w(c[i], c[i+1])
    # where w is a penalty function for "bad" pairs

    # In the good cycle, adjacent pairs follow specific patterns.
    # Maybe we can define w to penalize non-good-cycle pairs.

    for nv in [6, 7]:
        ms, fs, good_set, bad_set, adj, adj_rev, exits = get_bad_graph(nv)
        transitions = []
        for c in bad_set:
            for i in range(nv):
                L = c[(i-1)%nv]; S = c[i]; R = c[(i+1)%nv]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c); lst[i] = new_S; succ = tuple(lst)
                    if succ in bad_set:
                        transitions.append((c, succ, i))

        # Collect all adjacent pairs that appear in good configs
        good_pairs = set()
        for c in good_set:
            for i in range(nv):
                good_pairs.add((i, c[i], c[(i+1) % nv]))

        def bad_pair_count(c):
            """Count adjacent pairs NOT appearing in any good config."""
            count = 0
            for i in range(nv):
                if (i, c[i], c[(i+1) % nv]) not in good_pairs:
                    count += 1
            return count

        viol = 0
        for c, cp, mv in transitions:
            if bad_pair_count(cp) >= bad_pair_count(c):
                viol += 1
        print(f"  n={nv}: bad_pair_count decrease: {viol} violations / {len(transitions)} "
              f"({100*viol/len(transitions):.1f}%)")

        # Try: position-pair specific penalty
        # For each position i, define penalty(c[i], c[i+1]) as the min distance
        # to any good-config pair at that position
        # Actually simpler: 0 if pair appears in good config, 1 if not
        # That's what bad_pair_count already does.

        # What about triples (c[i-1], c[i], c[i+1])?
        good_triples = set()
        for c in good_set:
            for i in range(nv):
                good_triples.add((i, c[(i-1)%nv], c[i], c[(i+1)%nv]))

        def bad_triple_count(c):
            count = 0
            for i in range(nv):
                if (i, c[(i-1)%nv], c[i], c[(i+1)%nv]) not in good_triples:
                    count += 1
            return count

        viol = 0
        for c, cp, mv in transitions:
            if bad_triple_count(cp) >= bad_triple_count(c):
                viol += 1
        print(f"  n={nv}: bad_triple_count decrease: {viol} violations / {len(transitions)} "
              f"({100*viol/len(transitions):.1f}%)")

    # ================================================================
    # PART 9: THE "SETTLED PREFIX" POTENTIAL
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 9: SETTLED PREFIX / SUFFIX POTENTIALS")
    print("=" * 90)

    # Idea: positions can be "settled" if their value matches what the good cycle
    # would prescribe given the boundary. Define the longest "settled prefix" from
    # the left and "settled suffix" from the right.
    #
    # In the good cycle, the bounce pattern means:
    # - During Phase 1 (filling 1s L→R): positions 0,1,...,k are at their target
    # - During Phase 2 (filling 2s R→L): positions n-1,...,k are at their target
    #
    # So maybe: count the longest prefix of "correct" values from left,
    # and the longest suffix from right, and use their sum as potential.

    # Actually, "correct" is hard to define since it depends on where in the cycle
    # we are. Instead, let's try: the longest prefix where each position is at
    # the fixed point of its table given its neighbors.

    for nv in [5, 6, 7, 8]:
        ms, fs, good_set, bad_set, adj, adj_rev, exits = get_bad_graph(nv)
        transitions = []
        for c in bad_set:
            for i in range(nv):
                L = c[(i-1)%nv]; S = c[i]; R = c[(i+1)%nv]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c); lst[i] = new_S; succ = tuple(lst)
                    if succ in bad_set:
                        transitions.append((c, succ, i))

        def settled_prefix(c):
            """Longest prefix of positions at their fixed point."""
            count = 0
            for i in range(nv):
                L = c[(i-1) % nv]; S = c[i]; R = c[(i+1) % nv]
                if fs[i](L, S, R) == S:  # at fixed point
                    count += 1
                else:
                    break
            return count

        def settled_suffix(c):
            """Longest suffix of positions at their fixed point."""
            count = 0
            for i in range(nv - 1, -1, -1):
                L = c[(i-1) % nv]; S = c[i]; R = c[(i+1) % nv]
                if fs[i](L, S, R) == S:
                    count += 1
                else:
                    break
            return count

        def n_settled(c):
            """Total count of settled (non-privileged) positions."""
            count = 0
            for i in range(nv):
                L = c[(i-1) % nv]; S = c[i]; R = c[(i+1) % nv]
                if fs[i](L, S, R) == S:
                    count += 1
            return count

        # Test: n_settled as potential (should increase)
        viol = 0
        for c, cp, mv in transitions:
            if n_settled(cp) <= n_settled(c):
                viol += 1
        print(f"  n={nv}: n_settled increase: {viol} violations / {len(transitions)} "
              f"({100*viol/len(transitions):.1f}%)")

        # Test: settled_prefix
        viol = 0
        for c, cp, mv in transitions:
            sp_c = settled_prefix(c)
            sp_cp = settled_prefix(cp)
            if sp_cp <= sp_c:
                viol += 1
        print(f"  n={nv}: settled_prefix increase: {viol} violations / {len(transitions)} "
              f"({100*viol/len(transitions):.1f}%)")

        # Test: (settled_prefix, settled_suffix) lex
        viol = 0
        for c, cp, mv in transitions:
            if (settled_prefix(cp), settled_suffix(cp)) <= (settled_prefix(c), settled_suffix(c)):
                viol += 1
        print(f"  n={nv}: lex(prefix, suffix) increase: {viol} violations / {len(transitions)} "
              f"({100*viol/len(transitions):.1f}%)")

        # Test: (n - priv_count, at_target) where at_target was from Part 3
        # n_settled IS n - priv_count, so this is the same as (n_settled, ...)

    # ================================================================
    # PART 10: HAMMING DISTANCE TO NEAREST GOOD
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 10: HAMMING DISTANCE TO NEAREST GOOD CONFIG")
    print("=" * 90)

    for nv in [5, 6, 7]:
        ms, fs, good_set, bad_set, adj, adj_rev, exits = get_bad_graph(nv)
        transitions = []
        for c in bad_set:
            for i in range(nv):
                L = c[(i-1)%nv]; S = c[i]; R = c[(i+1)%nv]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c); lst[i] = new_S; succ = tuple(lst)
                    if succ in bad_set:
                        transitions.append((c, succ, i))

        good_list = list(good_set)

        def min_hamming(c):
            return min(sum(1 for i in range(nv) if c[i] != g[i]) for g in good_list)

        # Compute distances
        ham_cache = {}
        for c in bad_set:
            ham_cache[c] = min_hamming(c)

        viol = 0
        for c, cp, mv in transitions:
            if ham_cache[cp] >= ham_cache[c]:
                viol += 1
        print(f"  n={nv}: min_hamming decrease: {viol} violations / {len(transitions)} "
              f"({100*viol/len(transitions):.1f}%)")


if __name__ == "__main__":
    main()
