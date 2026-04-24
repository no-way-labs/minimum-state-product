#!/usr/bin/env python3
"""CUP: Final convergence analysis.

Key structural results so far:
1. Every bad config has >= 1 privileged MIDDLE proc.
2. Bottom/top are self-disabling (cooldown).
3. Middle moves: frontier count Δ ∈ {-2, -1, 0}.
4. Top move: d_{n-2} → 1, d_{n-1} → 2 always.
5. Bottom toggle: c_0 flips.

New approach: Track the d-vector dynamics precisely.
Show that no periodic orbit exists in the d-vector space.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system
from collections import defaultdict


def sol3_v1_rules(ms, n):
    def make_bottom(m0):
        def f(L, S, R):
            if (S + 1) % m0 == R % m0:
                return (S - 1) % m0
            return S
        return f
    def make_top(m_top):
        def f(L, S, R):
            if L % m_top == R % m_top and (L % m_top + 1) % m_top != S:
                return (L % m_top + 1) % m_top
            return S
        return f
    def make_middle(m_i):
        def f(L, S, R):
            if (S + 1) % m_i == L % m_i:
                return L % m_i
            if (S + 1) % m_i == R % m_i:
                return R % m_i
            return S
        return f
    fs = [make_bottom(ms[0])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i]))
    fs.append(make_top(ms[n - 1]))
    return fs


def get_privileged(c, fs, n):
    priv = []
    for i in range(n):
        L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
        if fs[i](L, S, R) != S:
            priv.append(i)
    return priv


def apply_move(c, i, fs, n):
    L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
    lst = list(c); lst[i] = fs[i](L, S, R); return tuple(lst)


def frontier_count(c, n):
    return sum(1 for i in range(n) if (c[(i+1) % n] - c[i]) % 3 != 0)


def get_d_vector(c, n):
    return tuple((c[(i+1)%n] - c[i]) % 3 for i in range(n))


def check_top_reenable(max_n=8):
    """After top fires and the type-1 frontier propagates, how many
    middle moves before top can fire again?"""
    print("=" * 60)
    print("TOP RE-ENABLE ANALYSIS")
    print("=" * 60)
    for n in range(4, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(configs) - good_set

        # For each config where top is privileged:
        # After top fires, how many steps before top can fire again?
        # (Under any daemon strategy)
        min_reenable = float('inf')
        max_reenable = 0

        for c in configs:
            priv = get_privileged(c, fs, n)
            if n - 1 not in priv:
                continue

            # Fire top
            after_top = apply_move(c, n-1, fs, n)
            if after_top in good_set:
                continue

            # BFS: find shortest path to a config where top is privileged again
            visited = {after_top}
            frontier = [after_top]
            depth = 0
            found = False

            while frontier and depth < 3 * n:
                depth += 1
                next_frontier = []
                for cur in frontier:
                    priv_cur = get_privileged(cur, fs, n)
                    for p in priv_cur:
                        succ = apply_move(cur, p, fs, n)
                        if succ in visited or succ in good_set:
                            continue
                        if n - 1 in get_privileged(succ, fs, n):
                            # Found! Top is re-enabled
                            found = True
                            min_reenable = min(min_reenable, depth)
                            max_reenable = max(max_reenable, depth)
                            break
                        visited.add(succ)
                        next_frontier.append(succ)
                    if found:
                        break
                if found:
                    break
                frontier = next_frontier

        if min_reenable < float('inf'):
            print(f"  n={n}: Top re-enable: min={min_reenable}, max≤{max_reenable}")
        else:
            print(f"  n={n}: Top never re-enables from bad configs!")


def analyze_token_propagation_in_bad_paths(n):
    """For each bad→bad transition, classify as:
    - Shift: frontier moves 1 position
    - Annihilate: 2 frontiers destroyed
    - Create: bottom/top creates frontier(s)
    Track the TOKEN FLOW through the DAG."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # Compute worst-case rank
    rank = {}
    changed = True
    while changed:
        changed = False
        for c in bad_set:
            if c in rank:
                continue
            priv = get_privileged(c, fs, n)
            worst = 0
            all_resolved = True
            for p in priv:
                succ = apply_move(c, p, fs, n)
                if succ in good_set:
                    steps = 1
                elif succ in rank:
                    steps = 1 + rank[succ]
                else:
                    all_resolved = False
                    break
                worst = max(worst, steps)
            if all_resolved:
                rank[c] = worst
                changed = True

    # Trace the worst-case path from the max-rank config
    max_r = max(rank.values())
    max_config = [c for c, r in rank.items() if r == max_r][0]

    print(f"\nn={n}: Tracing worst-case path from {max_config} (rank={max_r})")

    c = max_config
    path = []
    while c in bad_set:
        priv = get_privileged(c, fs, n)
        # Choose the worst move (maximizes rank)
        best_p = None
        best_rank = -1
        for p in priv:
            succ = apply_move(c, p, fs, n)
            r = rank.get(succ, -1) if succ not in good_set else 0
            if r > best_rank:
                best_rank = r
                best_p = p

        succ = apply_move(c, best_p, fs, n)
        fc_before = frontier_count(c, n)
        fc_after = frontier_count(succ, n)
        delta_fc = fc_after - fc_before
        d_before = get_d_vector(c, n)

        mtype = "BOT" if best_p == 0 else ("TOP" if best_p == n-1 else "MID")
        path.append((c, best_p, mtype, delta_fc, d_before))

        c = succ

    # Analyze the path
    move_types = defaultdict(int)
    fc_changes = defaultdict(int)
    for _, p, mtype, dfc, _ in path:
        move_types[mtype] += 1
        fc_changes[(mtype, dfc)] += 1

    print(f"  Path length: {len(path)}")
    print(f"  Move types: {dict(move_types)}")
    print(f"  FC changes: {dict(sorted(fc_changes.items()))}")

    # Track frontier count along the path
    fcs = [frontier_count(max_config, n)]
    for _, _, _, dfc, _ in path:
        fcs.append(fcs[-1] + dfc)
    print(f"  FC trajectory (first 30): {fcs[:30]}")
    print(f"  Max FC: {max(fcs)}, Min FC: {min(fcs)}")

    # Show detailed path for small n
    if n <= 5:
        print(f"  Detailed path:")
        for step, (c, p, mt, dfc, d) in enumerate(path[:30]):
            print(f"    {step:2d}: {c} d={d} P{p}({mt}) Δfc={dfc:+d}")


def check_nontermination_candidate(n):
    """Look for configs that could potentially form cycles.
    A candidate: a config c with a move to c' where rank(c') >= rank(c) - 1
    AND c' has a move to c'' with rank >= rank(c) - 1, etc.

    This traces the 'hardest' execution paths."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # Compute rank
    rank = {}
    changed = True
    while changed:
        changed = False
        for c in bad_set:
            if c in rank:
                continue
            priv = get_privileged(c, fs, n)
            worst = 0
            all_resolved = True
            for p in priv:
                succ = apply_move(c, p, fs, n)
                if succ in good_set:
                    steps = 1
                elif succ in rank:
                    steps = 1 + rank[succ]
                else:
                    all_resolved = False
                    break
                worst = max(worst, steps)
            if all_resolved:
                rank[c] = worst
                changed = True

    # For each bad config, find the "tightest" cycle attempt:
    # the longest path that stays within a small rank range
    max_r = max(rank.values())

    # Count how many configs are within rank r..r-2 of max
    top_configs = [c for c, r in rank.items() if r >= max_r - 5]
    print(f"\nn={n}: {len(top_configs)} configs within 5 of max rank {max_r}")

    # Check connectivity among top configs
    top_set = set(top_configs)
    edges = 0
    for c in top_configs:
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ in top_set:
                edges += 1
    print(f"  Edges among top configs: {edges}")


def prove_no_cycles_via_X(max_n=9):
    """Check: does X = Σc_i strictly decrease on every bad→bad move
    when restricted to same-fc configs?

    I.e., for configs with the same frontier count, does X decrease?"""
    print("\n" + "=" * 60)
    print("X-MONOTONICITY WITHIN SAME FRONTIER COUNT")
    print("=" * 60)
    for n in range(3, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(configs) - good_set

        # For bad→bad moves with Δfc=0: does X strictly change?
        same_fc_moves = 0
        x_same_fc_violations = 0

        for c in bad_set:
            fc = frontier_count(c, n)
            X = sum(c)
            priv = get_privileged(c, fs, n)
            for p in priv:
                succ = apply_move(c, p, fs, n)
                if succ in bad_set:
                    fc_s = frontier_count(succ, n)
                    if fc_s == fc:
                        same_fc_moves += 1
                        X_s = sum(succ)
                        if X_s >= X:  # We'd want X to decrease
                            x_same_fc_violations += 1

        print(f"  n={n}: same-fc bad→bad: {same_fc_moves}, "
              f"X non-decreasing: {x_same_fc_violations}")


def check_multivariate_potential(max_n=8):
    """Try Φ = (fc, -interior_fc, something).
    Interior frontiers: positions 1..n-3.
    Boundary frontiers: positions 0, n-2, n-1."""
    print("\n" + "=" * 60)
    print("INTERIOR vs BOUNDARY FRONTIER POTENTIAL")
    print("=" * 60)
    for n in range(4, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(configs) - good_set

        def interior_fc(c):
            """Count frontiers at interior positions 1..n-3."""
            count = 0
            for i in range(1, n - 2):
                if (c[(i+1) % n] - c[i]) % 3 != 0:
                    count += 1
            return count

        def boundary_fc(c):
            """Count frontiers at boundary positions 0, n-2, n-1."""
            count = 0
            for i in [0, n-2, n-1]:
                if (c[(i+1) % n] - c[i]) % 3 != 0:
                    count += 1
            return count

        # Try: Φ = (total_fc, interior_fc) lexicographic
        def phi_lex(c):
            return (frontier_count(c, n), interior_fc(c))

        # Try: Φ = n * total_fc + interior_fc
        def phi_weighted(c):
            return n * frontier_count(c, n) + interior_fc(c)

        # Try: Φ = n * total_fc - boundary_fc
        def phi_weighted2(c):
            return n * frontier_count(c, n) - boundary_fc(c)

        # Try: Φ = total_fc * (n-2) + Σ min(pos, n-2-pos) for each frontier
        def phi_central_weight(c):
            fc = frontier_count(c, n)
            w = 0
            for i in range(n):
                d = (c[(i+1) % n] - c[i]) % 3
                if d != 0:
                    w += min(i, n - 1 - i)  # distance to nearest boundary
            return fc * (n * n) + w

        for name, phi in [("lex(fc,ifc)", phi_lex),
                          ("n*fc+ifc", phi_weighted),
                          ("n*fc-bfc", phi_weighted2),
                          ("fc²+central", phi_central_weight)]:
            violations = 0
            for c in bad_set:
                priv = get_privileged(c, fs, n)
                phi_c = phi(c)
                for p in priv:
                    succ = apply_move(c, p, fs, n)
                    if succ in bad_set:
                        phi_s = phi(succ)
                        if phi_s >= phi_c:
                            violations += 1
            status = "✓" if violations == 0 else f"✗ {violations}"
            print(f"  n={n} {name}: {status}")


def check_augmented_state_potential(max_n=8):
    """The d-vector + c_0 fully determines the config (up to constant shift).
    Try: Φ(d, c_0) = (fc, f(d, c_0)) for various f.

    Key insight: after top move, d_{n-2}=1, d_{n-1}=2 always.
    So the top sets 2 specific d-values. This is a "reset" operation.
    Can we use this to show progress?"""
    print("\n" + "=" * 60)
    print("AUGMENTED STATE POTENTIAL (d-vector + c_0)")
    print("=" * 60)
    for n in range(4, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(configs) - good_set

        # Track top-move count in worst-case path
        # If top fires ≤ constant times in any bad path, that's useful

        rank = {}
        parent = {}
        changed = True
        while changed:
            changed = False
            for c in bad_set:
                if c in rank:
                    continue
                priv = get_privileged(c, fs, n)
                worst = 0
                worst_p = None
                all_resolved = True
                for p in priv:
                    succ = apply_move(c, p, fs, n)
                    if succ in good_set:
                        steps = 1
                    elif succ in rank:
                        steps = 1 + rank[succ]
                    else:
                        all_resolved = False
                        break
                    if steps > worst:
                        worst = steps
                        worst_p = p
                if all_resolved:
                    rank[c] = worst
                    parent[c] = worst_p
                    changed = True

        # Trace worst-case path and count boundary moves
        max_r = max(rank.values())
        start = [c for c, r in rank.items() if r == max_r][0]

        c = start
        bot_count = 0
        top_count = 0
        mid_count = 0
        while c in bad_set:
            p = parent[c]
            if p == 0:
                bot_count += 1
            elif p == n - 1:
                top_count += 1
            else:
                mid_count += 1
            c = apply_move(c, p, fs, n)

        total = bot_count + top_count + mid_count
        print(f"  n={n}: rank={max_r}, path_len={total}, "
              f"bot={bot_count}, top={top_count}, mid={mid_count}, "
              f"ratio mid/boundary={(mid_count/(bot_count+top_count+0.01)):.1f}")


def prove_convergence_small_n():
    """For n=3,4: provide complete convergence proofs by exhaustive case analysis.
    Show that these form the base cases for an inductive argument."""
    print("\n" + "=" * 60)
    print("EXHAUSTIVE CONVERGENCE FOR n=3,4")
    print("=" * 60)

    for n in [3, 4]:
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(configs) - good_set

        print(f"\nn={n}: {len(bad_set)} bad configs")

        # For each bad config, show ALL possible successor paths
        rank = {}
        changed = True
        while changed:
            changed = False
            for c in bad_set:
                if c in rank:
                    continue
                priv = get_privileged(c, fs, n)
                worst = 0
                all_resolved = True
                for p in priv:
                    succ = apply_move(c, p, fs, n)
                    if succ in good_set:
                        steps = 1
                    elif succ in rank:
                        steps = 1 + rank[succ]
                    else:
                        all_resolved = False
                        break
                    worst = max(worst, steps)
                if all_resolved:
                    rank[c] = worst
                    changed = True

        for c in sorted(bad_set, key=lambda x: rank.get(x, 0)):
            priv = get_privileged(c, fs, n)
            d = get_d_vector(c, n)
            fc = frontier_count(c, n)
            moves = []
            for p in priv:
                succ = apply_move(c, p, fs, n)
                sr = 'G' if succ in good_set else str(rank[succ])
                mt = 'B' if p == 0 else ('T' if p == n-1 else 'M')
                moves.append(f"P{p}({mt})→r{sr}")
            print(f"  r{rank[c]:2d}: {c} d={d} fc={fc} → {', '.join(moves)}")


if __name__ == "__main__":
    check_top_reenable(7)
    prove_no_cycles_via_X(9)
    check_multivariate_potential(8)
    check_augmented_state_potential(9)
    prove_convergence_small_n()

    print("\n" + "=" * 60)
    print("WORST-CASE PATH ANALYSIS")
    print("=" * 60)
    for nv in [4, 5, 6]:
        analyze_token_propagation_in_bad_paths(nv)
