#!/usr/bin/env python3
"""Convergence proof investigation — Part 6.

STRATEGY: Prove DAG for open chain with fixed boundaries.

When both c[0] and c[n-1] are fixed (both boundaries frozen):
- The system is an OPEN CHAIN: positions 1,...,n-2 fire, boundaries are fixed
- No wrap-around information flow
- 1-wave propagates rightward, 2-wave propagates leftward
- These counter-propagating waves can't interfere cyclically

Goal: Find a potential function that works within each boundary partition.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import deque, defaultdict, Counter
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system


def get_chain_graph(n, v0, vn):
    """Build the bad-config graph for the chain with fixed boundaries.
    Only interior positions (1,...,n-2) fire. Boundaries c[0]=v0, c[n-1]=vn are fixed."""
    ms, fs = build_system(n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(c for c in all_configs if c not in good_set
                  and c[0] == v0 and c[n-1] == vn)

    transitions = []
    for c in bad_set:
        for i in range(1, n - 1):  # Interior only
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    transitions.append((c, succ, i))

    return ms, fs, good_set, bad_set, transitions


def main():
    # ================================================================
    # PART 1: POTENTIAL FUNCTIONS FOR OPEN CHAIN
    # ================================================================
    print("=" * 90)
    print("PART 1: POTENTIAL FUNCTIONS FOR CHAIN (fixed boundaries)")
    print("=" * 90)

    for nv in [6, 7, 8, 9]:
        ms, fs = build_system(nv)
        n = nv

        for v0 in range(2):
            for vn in range(2):
                ms, fs, good_set, bad_set, transitions = get_chain_graph(n, v0, vn)
                if not transitions:
                    continue

                # Test various potentials for the chain
                def frontier(c):
                    return sum(1 for i in range(n) if c[i] != c[(i+1) % n])

                def total_sum(c):
                    return sum(c)

                def n_priv(c):
                    count = 0
                    for i in range(1, n-1):
                        L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                        if fs[i](L, S, R) != S:
                            count += 1
                    return count

                def at_target(c):
                    count = 0
                    for i in range(1, n-1):
                        L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                        if fs[i](L, S, R) == S:
                            count += 1
                    return count

                # Left-weighted sum: positions with smaller index count more
                def left_weighted(c):
                    return sum((n - i) * c[i] for i in range(1, n-1))

                # "Wave potential": count rightward-compatible 1-values
                # plus leftward-compatible 2-values
                def wave_potential(c):
                    score = 0
                    # Rightward 1-front: longest prefix of 1s from left
                    for i in range(1, n-1):
                        if c[i] >= 1:
                            score += (n - i)
                        else:
                            break
                    # Leftward 2-front: longest suffix of 2s from right
                    for i in range(n-2, 0, -1):
                        if c[i] >= 2:
                            score += i
                        else:
                            break
                    return score

                # "Phase potential": where in the 3-phase cycle is this config?
                # Phase 1: filling 1s L→R (sum increases)
                # Phase 2: filling 2s R→L (sum increases more)
                # Phase 3: resetting 0s L→R (sum decreases)
                def phase_sum(c):
                    # Weighted sum where value 1 contributes positively,
                    # value 2 contributes even more
                    return sum(c[i] + (1 if c[i] == 2 else 0) for i in range(1, n-1))

                # "Mismatch with neighbors": sum of |c[i] - c[i-1]| + |c[i] - c[i+1]|
                def neighbor_mismatch(c):
                    return sum(abs(c[i] - c[(i-1)%n]) + abs(c[i] - c[(i+1)%n])
                                for i in range(1, n-1))

                results = {}
                for name, func, want_decrease in [
                    ('frontier', frontier, True),
                    ('sum', total_sum, True),
                    ('n_priv', n_priv, True),
                    ('at_target', at_target, False),  # want increase
                    ('left_weighted', left_weighted, True),
                    ('wave_potential', wave_potential, False),
                    ('neighbor_mismatch', neighbor_mismatch, True),
                    ('3*n_priv - sum', lambda c: 3 * n_priv(c) - total_sum(c), True),
                ]:
                    viol = 0
                    for c, cp, mv in transitions:
                        if want_decrease:
                            if func(cp) >= func(c):
                                viol += 1
                        else:
                            if func(cp) <= func(c):
                                viol += 1
                    pct = 100 * viol / len(transitions) if transitions else 0
                    results[name] = (viol, pct)

                # Only print if we have non-trivial transitions
                best_name = min(results, key=lambda k: results[k][0])
                best_viol, best_pct = results[best_name]
                if best_pct < 30:
                    print(f"  n={nv}, b=({v0},{vn}): {len(transitions)} trans, "
                          f"best={best_name} ({best_viol}, {best_pct:.1f}%)")

    # ================================================================
    # PART 2: IS THE CHAIN SIMPLER THAN THE RING?
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 2: CHAIN vs RING COMPARISON")
    print("=" * 90)

    for nv in [6, 7, 8, 9, 10]:
        ms, fs = build_system(nv)
        n = nv

        # Chain: freeze both boundaries, check DAG depth
        for v0, vn in [(0,0), (1,1), (0,1), (1,0)]:
            ms, fs, good_set, bad_set, transitions = get_chain_graph(n, v0, vn)
            if not bad_set:
                continue

            # Compute depth
            adj = defaultdict(list)
            in_deg = {c: 0 for c in bad_set}
            for c, cp, mv in transitions:
                adj[c].append(cp)
                in_deg[cp] += 1

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
            depth = max(rank.values()) if rank else 0

            full_depth = (3*n*n - 4*n - 11) // 4
            print(f"  n={nv}, ({v0},{vn}): chain_depth={depth}, "
                  f"full_depth≈{full_depth}, ratio={depth/full_depth:.3f}")

    # ================================================================
    # PART 3: WHAT'S SPECIAL ABOUT THE CHAIN — ESCAPE STRUCTURE
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 3: CHAIN ESCAPE STRUCTURE")
    print("=" * 90)

    for nv in [6, 7, 8]:
        ms, fs = build_system(nv)
        n = nv

        for v0, vn in [(0,0), (1,1)]:
            ms, fs, good_set, bad_set, transitions = get_chain_graph(n, v0, vn)
            if not bad_set:
                continue

            # For each bad config, count transitions to good vs bad
            exit_counts = Counter()  # number of good-exits
            for c in bad_set:
                good_exits = 0
                bad_exits = 0
                for i in range(1, n-1):
                    L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                    new_S = fs[i](L, S, R)
                    if new_S != S:
                        lst = list(c); lst[i] = new_S; succ = tuple(lst)
                        if succ in good_set:
                            good_exits += 1
                        elif succ in bad_set:
                            bad_exits += 1
                        else:
                            # Goes to a bad config in different partition
                            # (shouldn't happen since boundaries are fixed)
                            pass
                exit_counts[(good_exits, bad_exits)] += 1

            print(f"\n  n={nv}, ({v0},{vn}): {len(bad_set)} bad configs")
            print(f"  Exit distribution (good_exits, bad_exits): count")
            for k in sorted(exit_counts.keys()):
                ge, be = k
                print(f"    ({ge} good, {be} bad): {exit_counts[k]} configs")

    # ================================================================
    # PART 4: CHAIN DYNAMICS — TRACK INFORMATION FLOW
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 4: INFORMATION FLOW IN CHAIN TRANSITIONS")
    print("=" * 90)

    # For each transition in the chain, classify the "information source":
    # Did the mover's transition depend more on the LEFT or RIGHT neighbor?

    for nv in [6, 7]:
        ms, fs = build_system(nv)
        n = nv

        for v0, vn in [(1,1)]:  # Focus on one partition
            ms, fs, good_set, bad_set, transitions = get_chain_graph(n, v0, vn)
            if not transitions:
                continue

            print(f"\nn={nv}, ({v0},{vn}): {len(transitions)} chain transitions")

            # For each transition, determine:
            # 1. The value change at the mover
            # 2. Whether the transition is "left-caused" or "right-caused"
            # A transition is "left-caused" if the LEFT neighbor value determines
            # the output (i.e., changing R wouldn't change the outcome)
            # "right-caused" if changing L wouldn't change the outcome

            for mv_pos in range(1, n-1):
                left_caused = 0
                right_caused = 0
                both_caused = 0
                total = 0

                for c, cp, mv in transitions:
                    if mv != mv_pos:
                        continue
                    total += 1

                    L = c[(mv-1)%n]; S = c[mv]; R = c[(mv+1)%n]
                    out = fs[mv](L, S, R)

                    # Test: would different L give same output?
                    L_matters = False
                    R_matters = False
                    for L2 in range(ms[(mv-1)%n]):
                        if L2 != L:
                            out2 = fs[mv](L2, S, R)
                            if out2 != out:
                                L_matters = True
                                break
                    for R2 in range(ms[(mv+1)%n]):
                        if R2 != R:
                            out2 = fs[mv](L, S, R2)
                            if out2 != out:
                                R_matters = True
                                break

                    if L_matters and R_matters:
                        both_caused += 1
                    elif L_matters:
                        left_caused += 1
                    elif R_matters:
                        right_caused += 1
                    else:
                        left_caused += 1  # Constant output, but triggered by privileged

                if total > 0:
                    tbl = 'low' if mv_pos == 1 else \
                          'mid' if mv_pos < n-2 else 'high'
                    print(f"  P{mv_pos}({tbl}): {total} trans — "
                          f"L-caused={left_caused}, R-caused={right_caused}, "
                          f"both={both_caused}")

    # ================================================================
    # PART 5: THE "LEFT-SUFFIX" POTENTIAL FOR THE CHAIN
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 5: LEFT-SUFFIX AND RIGHT-PREFIX POTENTIALS")
    print("=" * 90)

    # Key idea: in an open chain, define:
    # left_settled(c) = length of longest suffix from the LEFT where each
    #   position is at its fixed point
    # right_settled(c) = similar from the RIGHT
    #
    # If the chain dynamics progress from boundaries inward (waves),
    # then one of these should be monotone.

    for nv in [6, 7, 8, 9, 10]:
        ms, fs = build_system(nv)
        n = nv

        for v0, vn in [(0,0), (1,1), (0,1), (1,0)]:
            ms_c, fs_c, good_set, bad_set, transitions = get_chain_graph(n, v0, vn)
            if not transitions:
                continue

            def left_settled(c):
                """Longest settled prefix from position 1."""
                count = 0
                for i in range(1, n-1):
                    L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                    if fs_c[i](L, S, R) == S:
                        count += 1
                    else:
                        break
                return count

            def right_settled(c):
                """Longest settled suffix from position n-2."""
                count = 0
                for i in range(n-2, 0, -1):
                    L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                    if fs_c[i](L, S, R) == S:
                        count += 1
                    else:
                        break
                return count

            def total_settled(c):
                return sum(1 for i in range(1, n-1)
                           if fs_c[i](c[(i-1)%n], c[i], c[(i+1)%n]) == c[i])

            def lex_lr(c):
                return (left_settled(c), right_settled(c))

            def lex_rl(c):
                return (right_settled(c), left_settled(c))

            def lex_total_right(c):
                return (total_settled(c), right_settled(c))

            viol_left = sum(1 for c, cp, mv in transitions
                           if left_settled(cp) <= left_settled(c))
            viol_right = sum(1 for c, cp, mv in transitions
                            if right_settled(cp) <= right_settled(c))
            viol_total = sum(1 for c, cp, mv in transitions
                            if total_settled(cp) <= total_settled(c))
            viol_lex_lr = sum(1 for c, cp, mv in transitions
                             if lex_lr(cp) <= lex_lr(c))
            viol_lex_tr = sum(1 for c, cp, mv in transitions
                             if lex_total_right(cp) <= lex_total_right(c))

            T = len(transitions)
            best = min(viol_left, viol_right, viol_total, viol_lex_lr, viol_lex_tr)
            best_name = ['left', 'right', 'total', 'lex(L,R)', 'lex(T,R)'][
                [viol_left, viol_right, viol_total, viol_lex_lr, viol_lex_tr].index(best)]
            pct = 100 * best / T
            if pct < 35:
                print(f"  n={nv}, ({v0},{vn}): best={best_name} "
                      f"({best}/{T}, {pct:.1f}%)")

    # ================================================================
    # PART 6: FOCUS ON THE PROBLEMATIC TRANSITIONS
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 6: ANALYSIS OF PROBLEMATIC TRANSITIONS (chain)")
    print("=" * 90)

    # For the best potential so far (total_settled), analyze the violations
    nv = 7
    ms, fs = build_system(nv)
    n = nv

    for v0, vn in [(1, 1)]:
        ms_c, fs_c, good_set, bad_set, transitions = get_chain_graph(n, v0, vn)
        if not transitions:
            continue

        def total_settled(c):
            return sum(1 for i in range(1, n-1)
                       if fs_c[i](c[(i-1)%n], c[i], c[(i+1)%n]) == c[i])

        violations = []
        for c, cp, mv in transitions:
            ts_c = total_settled(c)
            ts_cp = total_settled(cp)
            if ts_cp <= ts_c:
                violations.append((c, cp, mv, ts_c, ts_cp))

        print(f"\nn={nv}, ({v0},{vn}): {len(violations)} violations of total_settled ↑")
        print(f"Violations by mover position:")
        by_mover = Counter()
        for c, cp, mv, ts_c, ts_cp in violations:
            by_mover[mv] += 1
        for mv in sorted(by_mover.keys()):
            tbl = 'low' if mv == 1 else 'mid' if mv < n-2 else 'high'
            print(f"  P{mv} ({tbl}): {by_mover[mv]}")

        # Show some violations
        print(f"\nSample violations:")
        for c, cp, mv, ts_c, ts_cp in violations[:10]:
            change = cp[mv] - c[mv] if cp[mv] > c[mv] else cp[mv] - c[mv]
            # Which positions changed settled status?
            gained = []
            lost = []
            for i in range(1, n-1):
                was = fs_c[i](c[(i-1)%n], c[i], c[(i+1)%n]) == c[i]
                now = fs_c[i](cp[(i-1)%n], cp[i], cp[(i+1)%n]) == cp[i]
                if not was and now:
                    gained.append(i)
                elif was and not now:
                    lost.append(i)
            print(f"  {c} →[P{mv}] {cp}: settled {ts_c}→{ts_cp}, "
                  f"gained={gained}, lost={lost}")

    # ================================================================
    # PART 7: THE "WEIGHTED SETTLED" POTENTIAL
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 7: WEIGHTED SETTLED COUNT")
    print("=" * 90)

    # The mover always settles (+w_mover). But it can unsettle neighbors
    # (-w_neighbor). If we weight positions so that the mover's contribution
    # always outweighs the neighbors' loss, we have a potential.
    #
    # From Part 5 of clb_convergence_proof2.py:
    # - Mover (rel=0): always settles
    # - rel=-1 (left neighbor): net more settles than unsettles
    # - rel=+1 (right neighbor): net more settles than unsettles
    #
    # The problem was wrap-around. But in the CHAIN (no wrap-around),
    # only immediate neighbors can be affected.

    for nv in [6, 7, 8, 9, 10]:
        ms, fs = build_system(nv)
        n = nv

        for v0, vn in [(0,0), (1,1), (0,1), (1,0)]:
            ms_c, fs_c, good_set, bad_set, transitions = get_chain_graph(n, v0, vn)
            if not transitions:
                continue

            # Try different weight patterns for the settled count
            best_viol = len(transitions)
            best_weights = None

            for w_pattern in ['uniform', 'linear_left', 'linear_right',
                              'quadratic', 'center_heavy', 'boundary_heavy',
                              'position_n', 'position_n2']:
                if w_pattern == 'uniform':
                    w = [1] * n
                elif w_pattern == 'linear_left':
                    w = [n - i for i in range(n)]
                elif w_pattern == 'linear_right':
                    w = [i + 1 for i in range(n)]
                elif w_pattern == 'quadratic':
                    w = [(i + 1) * (n - i) for i in range(n)]
                elif w_pattern == 'center_heavy':
                    mid = n // 2
                    w = [n - abs(i - mid) for i in range(n)]
                elif w_pattern == 'boundary_heavy':
                    mid = n // 2
                    w = [abs(i - mid) + 1 for i in range(n)]
                elif w_pattern == 'position_n':
                    w = [n] * n  # All same weight n
                elif w_pattern == 'position_n2':
                    w = [n * n] * n  # All same weight n²

                def weighted_settled(c, weights=w):
                    total = 0
                    for i in range(1, n-1):
                        if fs_c[i](c[(i-1)%n], c[i], c[(i+1)%n]) == c[i]:
                            total += weights[i]
                    return total

                viol = sum(1 for c, cp, mv in transitions
                           if weighted_settled(cp) <= weighted_settled(c))

                if viol < best_viol:
                    best_viol = viol
                    best_weights = w_pattern

            pct = 100 * best_viol / len(transitions)
            if pct < 35:
                print(f"  n={nv}, ({v0},{vn}): best weight={best_weights} "
                      f"({best_viol}/{len(transitions)}, {pct:.1f}%)")

    # ================================================================
    # PART 8: BOUNDARY FIRING ANALYSIS — DOES P0 EVER NEED P_{n-1}?
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 8: BOUNDARY FIRING INDEPENDENCE")
    print("=" * 90)

    # Key question: in the full bad graph, when P0 fires, does the transition
    # ever change a value that P_{n-1} "needs"? If the boundaries are
    # essentially independent, the ring dynamics decouple.

    for nv in [6, 7, 8]:
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        # When P0 fires, it changes c[0]. This affects:
        # P1 (whose L = c[0]) and P_{n-1} (whose R = c[0])
        # P1 is adjacent, P_{n-1} is wrap-around.
        #
        # Question: when P0 fires in a bad→bad transition, does P_{n-1}'s
        # privilege status change?

        p0_fires_pn_changes = 0
        p0_fires_total = 0
        for c in bad_set:
            L = c[(0-1)%n]; S = c[0]; R = c[(0+1)%n]
            new_S = fs[0](L, S, R)
            if new_S != S:
                lst = list(c); lst[0] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    p0_fires_total += 1
                    # Check P_{n-1}'s privilege status before and after
                    Ln = c[(n-2)]; Sn = c[n-1]; Rn = c[0]  # R of P_{n-1} is c[0]
                    priv_before = (fs[n-1](Ln, Sn, Rn) != Sn)
                    Rn_new = new_S
                    priv_after = (fs[n-1](Ln, Sn, Rn_new) != Sn)
                    if priv_before != priv_after:
                        p0_fires_pn_changes += 1

        # Similarly, when P_{n-1} fires, check if P0's status changes
        pn_fires_p0_changes = 0
        pn_fires_total = 0
        for c in bad_set:
            i = n - 1
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    pn_fires_total += 1
                    L0 = c[n-1]; S0 = c[0]; R0 = c[1]
                    priv_before = (fs[0](L0, S0, R0) != S0)
                    L0_new = new_S
                    priv_after = (fs[0](L0_new, S0, R0) != S0)
                    if priv_before != priv_after:
                        pn_fires_p0_changes += 1

        print(f"  n={nv}: P0 fires (bad→bad): {p0_fires_total}, "
              f"P{n-1} status changes: {p0_fires_pn_changes} "
              f"({100*p0_fires_pn_changes/p0_fires_total:.1f}%)")
        print(f"  n={nv}: P{n-1} fires (bad→bad): {pn_fires_total}, "
              f"P0 status changes: {pn_fires_p0_changes} "
              f"({100*pn_fires_p0_changes/pn_fires_total:.1f}%)")

    # ================================================================
    # PART 9: EXHAUSTIVE SMALL POTENTIAL SEARCH FOR CHAIN
    # ================================================================
    print("\n" + "=" * 90)
    print("PART 9: EXHAUSTIVE POTENTIAL SEARCH (chain, n=6)")
    print("=" * 90)

    nv = 6
    ms, fs = build_system(nv)
    n = nv

    for v0, vn in [(1, 1)]:
        ms_c, fs_c, good_set, bad_set, transitions = get_chain_graph(n, v0, vn)
        if not transitions:
            continue

        configs = list(bad_set)
        T = len(transitions)

        # For each config, compute all features
        def features(c):
            feats = []
            # Per-position features
            for i in range(1, n-1):
                L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                feats.append(c[i])  # value
                feats.append(1 if fs_c[i](L, S, R) == S else 0)  # settled
                feats.append(1 if c[i] >= 1 else 0)  # >=1
                feats.append(1 if c[i] == 2 else 0)  # ==2
            # Aggregate features
            feats.append(sum(c[1:n-1]))  # interior sum
            feats.append(sum(1 for i in range(1,n-1) if c[i] >= 1))  # nonzero count
            feats.append(sum(1 for i in range(1,n-1) if c[i] == 2))  # two count
            feats.append(sum(1 for i in range(1,n-1)
                            if fs_c[i](c[(i-1)%n], c[i], c[(i+1)%n]) == c[i]))  # settled count
            return tuple(feats)

        # Try: config VALUE tuple as lexicographic ordering
        # Lex ordering on the config values
        viol = 0
        for c, cp, mv in transitions:
            if c[1:n-1] <= cp[1:n-1]:
                viol += 1
        print(f"  Config values lex↑: {viol}/{T} ({100*viol/T:.1f}%)")

        viol = 0
        for c, cp, mv in transitions:
            if c[1:n-1] >= cp[1:n-1]:
                viol += 1
        print(f"  Config values lex↓: {viol}/{T} ({100*viol/T:.1f}%)")

        # Try: reverse config values lex
        viol = 0
        for c, cp, mv in transitions:
            if c[1:n-1][::-1] <= cp[1:n-1][::-1]:
                viol += 1
        print(f"  Config values rev_lex↑: {viol}/{T} ({100*viol/T:.1f}%)")

        viol = 0
        for c, cp, mv in transitions:
            if c[1:n-1][::-1] >= cp[1:n-1][::-1]:
                viol += 1
        print(f"  Config values rev_lex↓: {viol}/{T} ({100*viol/T:.1f}%)")

        # Try: settled positions as a binary vector, lex ordering
        def settled_vec(c):
            return tuple(1 if fs_c[i](c[(i-1)%n], c[i], c[(i+1)%n]) == c[i] else 0
                        for i in range(1, n-1))

        viol = 0
        for c, cp, mv in transitions:
            if settled_vec(cp) <= settled_vec(c):
                viol += 1
        print(f"  Settled vector lex↑: {viol}/{T} ({100*viol/T:.1f}%)")

        viol = 0
        for c, cp, mv in transitions:
            if settled_vec(cp)[::-1] <= settled_vec(c)[::-1]:
                viol += 1
        print(f"  Settled vector rev_lex↑: {viol}/{T} ({100*viol/T:.1f}%)")

        # Try: (settled_count, something) lex
        def settled_count(c):
            return sum(1 for i in range(1, n-1)
                       if fs_c[i](c[(i-1)%n], c[i], c[(i+1)%n]) == c[i])

        for name2, func2, dir2 in [
            ('sum', lambda c: sum(c[1:n-1]), True),
            ('-sum', lambda c: -sum(c[1:n-1]), True),
            ('settled_vec_lex', settled_vec, False),
            ('settled_vec_revlex', lambda c: settled_vec(c)[::-1], False),
        ]:
            viol = 0
            for c, cp, mv in transitions:
                sc = (settled_count(c), func2(c))
                scp = (settled_count(cp), func2(cp))
                if dir2:
                    if (-sc[0], sc[1]) <= (-scp[0], scp[1]):
                        viol += 1
                else:
                    if (-sc[0], sc[1]) >= (-scp[0], scp[1]):
                        viol += 1
            pct = 100 * viol / T
            print(f"  lex(-settled, {name2}): {viol}/{T} ({pct:.1f}%)")


if __name__ == "__main__":
    main()
