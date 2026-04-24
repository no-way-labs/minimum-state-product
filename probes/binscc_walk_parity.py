#!/usr/bin/env python3
"""binscc_walk_parity.py — Check ternary parity for P1-avoidable walks.

For P1-avoidable walks on {0,1}^3 (3 consecutive binary P0,P1,P2),
the ternary distribution in the gaps is heavily constrained by
ring-adjacency. Check whether the ternary parity constraint
(each ternary fires ≡ 0 mod m_p times) can be satisfied.

If no avoidable walk satisfies ternary parity → P1 overlap is FORCED
for all realizable cycles with 3 consecutive binary processors.
"""

from itertools import product as cartesian
from collections import defaultdict, Counter
import sys


def flip(vertex, coord):
    v = list(vertex)
    v[coord] = 1 - v[coord]
    return tuple(v)


RING_ADJ = {(0,1), (1,0), (1,2), (2,1)}


def enumerate_binary_sequences(max_k=12):
    results = []
    def dfs(seq, parity, counts):
        k = len(seq)
        if k > max_k:
            return
        if all(p == 0 for p in parity) and all(c >= 2 for c in counts):
            results.append(tuple(seq))
        remaining = max_k - k
        odd_coords = sum(1 for p in parity if p == 1)
        deficit = sum(max(0, 2 - c) for c in counts)
        if remaining < max(odd_coords, deficit):
            return
        for c in range(3):
            new_parity = list(parity)
            new_parity[c] = 1 - new_parity[c]
            new_counts = list(counts)
            new_counts[c] += 1
            dfs(seq + [c], new_parity, new_counts)
    dfs([], [0,0,0], [0,0,0])
    return results


def analyze_walk(seq):
    k = len(seq)
    walk = [(0,0,0)]
    for i in range(k):
        walk.append(flip(walk[-1], seq[i]))
    mover_set = set()
    for i in range(k):
        if seq[i] == 1:
            mover_set.add(walk[i])
    binary_nonmover = set()
    for i in range(k):
        if seq[i] in (0, 2):
            binary_nonmover.add(walk[i])
    gap_vertices = {}
    for i in range(k):
        gap_vertices[i] = walk[i+1]
    ring_adj_gaps = set()
    for i in range(k):
        pair = (seq[i], seq[(i+1) % k])
        if pair in RING_ADJ:
            ring_adj_gaps.add(i)
    return {
        'walk': walk, 'k': k, 'seq': seq,
        'mover_set': mover_set,
        'binary_nonmover': binary_nonmover,
        'gap_vertices': gap_vertices,
        'ring_adj_gaps': ring_adj_gaps,
        'must_overlap_binary': mover_set & binary_nonmover,
    }


def gap_parity_and_min(b_prev, b_next, n_ternary):
    """For a gap between binary firing b_prev and b_next:
    Return (min_s, parity) where s must satisfy s >= min_s and s % 2 == parity.

    Binary processors at positions 0,1,2.
    Ternary processors at positions 3,...,n-1 (n_ternary = n-3 of them).
    Ternary line: P3-P4-...-P_{n-1} (= P_{2+n_ternary}).

    P0's ternary neighbor: P_{n-1} = P_{2+n_ternary} (rightmost on ternary line)
    P2's ternary neighbor: P3 (leftmost on ternary line)

    Gap start endpoint on ternary line:
      b_prev = 0 → start at P_{n-1} (position n_ternary - 1 on 0-indexed ternary line)
      b_prev = 2 → start at P3 (position 0)
      b_prev = 1 → impossible (P1 can only connect to P0 or P2)

    Gap end endpoint:
      b_next = 0 → end at P_{n-1} (position n_ternary - 1)
      b_next = 2 → end at P3 (position 0)
      b_next = 1 → impossible

    Walk from position start to position end on line of n_ternary vertices.
    Distance d = |end - start|.
    Walk length s (# ternary movers).
    For walk of s movers: s-1 transitions, net displacement = end - start.
    s-1 >= d, and (s-1) ≡ d mod 2.
    So s >= d+1, and s ≡ (d+1) mod 2.

    But wait: if start == end, walk returns to same point.
    Distance = 0. s-1 >= 0, (s-1) ≡ 0 mod 2 → s odd.
    Min s = 1 (just fire the endpoint).

    If start != end: d = n_ternary - 1 (for P0↔P2 gap).
    s >= d+1 = n_ternary, s ≡ (d+1) mod 2 = n_ternary mod 2.
    """
    if b_prev == 1 or b_next == 1:
        return None  # impossible gap (P1 has no ternary neighbor)

    # Positions on ternary line (0-indexed, P3=0, P_{n-1}=n_ternary-1)
    if b_prev == 0:
        start = n_ternary - 1  # P_{n-1}
    else:  # b_prev == 2
        start = 0  # P3

    if b_next == 0:
        end = n_ternary - 1
    else:  # b_next == 2
        end = 0

    d = abs(end - start)

    if d == 0:
        # Same endpoint, walk returns. min s=1, s must be odd.
        return (1, 1)  # (min_s, parity: 1=odd)
    else:
        # Cross the ternary line. min s = d+1, parity = (d+1) % 2
        min_s = d + 1
        parity = min_s % 2
        return (min_s, parity)


def ternary_fire_profile(start_pos, end_pos, s, n_ternary):
    """Enumerate all possible ternary fire count vectors for a walk
    from start_pos to end_pos of length s on a line of n_ternary vertices.

    Returns list of tuples (f_0, f_1, ..., f_{n_ternary-1}) giving
    how many times each ternary processor fires.

    This is expensive for large s, so we use dynamic programming.
    State: (current_position, step_count, fire_counts_tuple).
    """
    # For large s, this is too expensive. Use DP with aggregated states.
    # Actually, we need the exact fire counts mod 3 for each processor.
    # So track: (current_position, fire_counts_mod_3_tuple).

    if s == 0:
        if start_pos == end_pos:
            return [tuple(0 for _ in range(n_ternary))]
        return []

    # DP: state = (position, fire_counts_mod3)
    # Initial state: position = start_pos, all fire counts = 0
    initial = (start_pos, tuple(0 for _ in range(n_ternary)))
    current = {initial}

    for step in range(s):
        next_states = set()
        for pos, fire_mod3 in current:
            # Fire at position pos, then move to adjacent position
            new_fire = list(fire_mod3)
            new_fire[pos] = (new_fire[pos] + 1) % 3
            new_fire_t = tuple(new_fire)

            # After firing, the new position is where we move to.
            # Wait: in the mover word, the mover fires (at current position),
            # then the next mover is at an adjacent position.
            # So we fire at `pos`, then the next step fires at a neighbor.
            if step < s - 1:
                # Move to adjacent positions
                for next_pos in [pos - 1, pos + 1]:
                    if 0 <= next_pos < n_ternary:
                        next_states.add((next_pos, new_fire_t))
            else:
                # Last step: must end at end_pos
                next_states.add((pos, new_fire_t))

        current = next_states

    # Filter: must end at end_pos
    result_mods = set()
    for pos, fire_mod3 in current:
        if pos == end_pos:
            result_mods.add(fire_mod3)

    return result_mods


def check_gap_ternary_profiles(b_prev, b_next, s, n_ternary):
    """Get all possible mod-3 fire profiles for a gap.

    Returns set of tuples, each giving (fire_count mod 3) for each ternary proc.
    """
    if b_prev == 0:
        start = n_ternary - 1
    else:
        start = 0

    if b_next == 0:
        end = n_ternary - 1
    else:
        end = 0

    return ternary_fire_profile(start, end, s, n_ternary)


def is_p1_avoidable(analysis, n):
    """Check if P1 overlap can be avoided (ignoring ternary parity)."""
    if analysis['must_overlap_binary']:
        return False

    k = analysis['k']
    seq = analysis['seq']
    mover_set = analysis['mover_set']
    gap_vertices = analysis['gap_vertices']
    n_ternary = n - 3

    # Check each gap
    for i in range(k):
        if gap_vertices[i] in mover_set:
            # Must have s=0 for this gap
            pair = (seq[i], seq[(i+1) % k])
            if pair not in RING_ADJ:
                return False  # can't have s=0
            # Also check if the gap can have s=0 with the mover word constraint
            # P1's neighbors are P0 and P2, so P1→P0 and P1→P2 are ring-adj.
            # But we also need the gap to be traversable without ternary.
            # For binary pairs, s=0 is always OK if ring-adjacent.

    return True


def check_ternary_parity(seq, n, verbose=False):
    """For a P1-avoidable binary firing sequence, check if ternary parity
    (each ternary fires ≡ 0 mod 3) can be satisfied.

    Returns: (feasible, details)
    """
    k = len(seq)
    ell = 3 * n - 2  # cycle length (may vary, but use standard)
    T = ell - k  # total ternary firings
    n_ternary = n - 3

    if T < n_ternary:
        return False, "not enough ternary for fairness"

    analysis = analyze_walk(seq)
    mover_set = analysis['mover_set']
    gap_vertices = analysis['gap_vertices']

    # Classify gaps
    gaps = []
    for i in range(k):
        b_prev = seq[i]
        b_next = seq[(i+1) % k]
        is_must_zero = gap_vertices[i] in mover_set

        if is_must_zero:
            # Must have s=0
            if (b_prev, b_next) not in RING_ADJ:
                return False, f"gap {i} must be zero but not ring-adj"
            gaps.append({'type': 'zero', 's': 0, 'profiles': {tuple(0 for _ in range(n_ternary))}})
        elif (b_prev, b_next) in RING_ADJ:
            # Can have s=0 or s>0
            gaps.append({'type': 'flex_ringadj', 'b_prev': b_prev, 'b_next': b_next})
        else:
            # Must have s>0, with parity constraints
            result = gap_parity_and_min(b_prev, b_next, n_ternary)
            if result is None:
                return False, f"gap {i} has P1 as endpoint (impossible)"
            min_s, parity = result
            gaps.append({'type': 'required', 'min_s': min_s, 'parity': parity,
                         'b_prev': b_prev, 'b_next': b_next})

    # Compute minimum ternary needed
    required_min = sum(g['min_s'] for g in gaps if g['type'] == 'required')
    if required_min > T:
        return False, f"min ternary {required_min} > budget {T}"

    # The extra ternary budget
    extra = T - required_min

    # Now we need to check if there's a distribution of ternary firings
    # such that each ternary processor fires ≡ 0 mod 3.
    #
    # Approach: for small n_ternary and small number of gaps, we can
    # enumerate possible gap sizes and check.
    # But this is exponential. Instead, use DP on gap-by-gap profiles.

    # For each gap, compute possible mod-3 profiles for each feasible s.
    # Then check if the product of profiles has a combination where
    # the sum mod 3 is all zeros.

    # For required gaps: s = min_s, min_s+2, min_s+4, ...
    # For flex_ringadj gaps: s = 0, or s = min_s_if_nonzero, ...
    # For zero gaps: s = 0

    # To keep it tractable, limit the max s per gap.
    max_extra_per_gap = min(extra, 12)  # limit search

    # Compute profiles gap by gap
    gap_profiles_list = []
    ternary_used = [0]  # mutable counter

    for i, g in enumerate(gaps):
        if g['type'] == 'zero':
            gap_profiles_list.append({tuple(0 for _ in range(n_ternary))})
        elif g['type'] == 'required':
            profiles = set()
            b_prev = g['b_prev']
            b_next = g['b_next']
            min_s = g['min_s']
            parity = g['parity']
            # Try s = min_s, min_s+2, ..., up to reasonable max
            for delta in range(0, max_extra_per_gap + 1, 2):
                s = min_s + delta
                if s > T:
                    break
                p = check_gap_ternary_profiles(b_prev, b_next, s, n_ternary)
                profiles.update(p)
            gap_profiles_list.append(profiles)
        elif g['type'] == 'flex_ringadj':
            profiles = set()
            # s=0: no ternary fires
            profiles.add(tuple(0 for _ in range(n_ternary)))
            # s>0: need valid walk. But what are the constraints?
            # Flex ringadj means b_prev, b_next are ring-adjacent binary.
            # If s>0, the ternary walk must go from a ternary neighbor
            # of b_prev to a ternary neighbor of b_next.
            # For (b_prev, b_next) in {(0,1),(1,0),(1,2),(2,1)}:
            # P1→P0: ternary must start/end adjacent to P1 — but P1 has
            #   no ternary neighbor! So s=0 only.
            # P0→P1: same — P1's neighbors are P0, P2 (binary). s=0 only.
            # P1→P2: same. s=0 only.
            # P2→P1: same. s=0 only.
            # So ALL ring-adj flex gaps must have s=0!
            gap_profiles_list.append(profiles)

    if verbose:
        for i, (g, p) in enumerate(zip(gaps, gap_profiles_list)):
            print(f"  Gap {i} ({g['type']}): {len(p)} profiles")

    # Now check: is there a selection of one profile per gap such that
    # the sum mod 3 is all zeros?
    # DP: state = current sum mod 3 (tuple of n_ternary values)

    current_states = {tuple(0 for _ in range(n_ternary))}

    for i, profiles in enumerate(gap_profiles_list):
        next_states = set()
        for state in current_states:
            for profile in profiles:
                new_state = tuple((s + p) % 3 for s, p in zip(state, profile))
                next_states.add(new_state)
        current_states = next_states
        if not current_states:
            return False, f"no feasible state after gap {i}"

    target = tuple(0 for _ in range(n_ternary))
    if target in current_states:
        return True, f"feasible with {len(current_states)} final states"
    else:
        return False, f"target not reachable, {len(current_states)} final states"


if __name__ == "__main__":
    print("=" * 78)
    print("TERNARY PARITY CHECK FOR P1-AVOIDABLE WALKS")
    print("=" * 78)

    all_seqs = enumerate_binary_sequences(max_k=12)
    print(f"Total binary sequences: {len(all_seqs)}")

    for n in [5, 7, 9]:
        ell = 3 * n - 2
        n_ternary = n - 3
        print(f"\n{'='*60}")
        print(f"n={n}, ℓ={ell}, ternary procs={n_ternary}")
        print(f"{'='*60}")

        avoidable = []
        for seq in all_seqs:
            k = len(seq)
            T = ell - k
            if T < 0 or T < n_ternary:
                continue

            analysis = analyze_walk(seq)
            if not is_p1_avoidable(analysis, n):
                continue

            avoidable.append(seq)

        print(f"P1-avoidable walks: {len(avoidable)}")

        feasible = 0
        infeasible = 0
        infeasible_reasons = Counter()

        for seq in avoidable:
            ok, reason = check_ternary_parity(seq, n)
            if ok:
                feasible += 1
                if feasible <= 5:
                    print(f"\n  FEASIBLE: seq={seq}")
                    print(f"    k={len(seq)}, T={ell-len(seq)}")
                    check_ternary_parity(seq, n, verbose=True)
            else:
                infeasible += 1
                infeasible_reasons[reason.split(':')[0].split(',')[0]] += 1

        print(f"\nResults: feasible={feasible}, infeasible={infeasible}")
        if infeasible_reasons:
            for r, c in infeasible_reasons.most_common():
                print(f"  {r}: {c}")

        if feasible == 0:
            print(f"\n  *** P1 OVERLAP FORCED for n={n} ***")
            print(f"  All {len(avoidable)} avoidable walks fail ternary parity.")
        else:
            print(f"\n  WARNING: {feasible} walks survive ternary parity.")

    # ================================================================
    # For surviving walks: check if they can actually produce cycles
    # ================================================================
    print(f"\n{'='*78}")
    print("DETAILED CHECK OF SURVIVING WALKS")
    print("=" * 78)

    for n in [5, 7, 9]:
        ell = 3 * n - 2
        n_ternary = n - 3

        surviving = []
        for seq in enumerate_binary_sequences(max_k=12):
            k = len(seq)
            T = ell - k
            if T < 0 or T < n_ternary:
                continue
            analysis = analyze_walk(seq)
            if not is_p1_avoidable(analysis, n):
                continue
            ok, _ = check_ternary_parity(seq, n)
            if ok:
                surviving.append(seq)

        if surviving:
            print(f"\nn={n}: {len(surviving)} surviving walks")
            # Check if each ternary fires ≥ 1 (fairness)
            # The ternary parity mod 3 check already ensures fires ≡ 0 mod 3.
            # Fires ≥ 1 means fires ≥ 3 (since must be ≥ 1 and ≡ 0 mod 3).
            # With T total ternary fires and n_ternary processors, each ≥ 3:
            # need T ≥ 3 * n_ternary.
            for seq in surviving[:10]:
                k = len(seq)
                T = ell - k
                can_fair = T >= 3 * n_ternary
                print(f"  seq={seq}, k={k}, T={T}, "
                      f"3*n_t={3*n_ternary}, fairness={'OK' if can_fair else 'FAIL'}")
                if can_fair:
                    # Additional: check all binary processors simultaneously
                    analysis = analyze_walk(seq)
                    walk = analysis['walk']
                    ms = analysis['mover_set']

                    # P0 overlap (binary subspace only)
                    p0_m = set(walk[i] for i in range(k) if seq[i] == 0)
                    p0_nm = set(walk[i] for i in range(k) if seq[i] != 0)
                    p0_ov = p0_m & p0_nm

                    # P2 overlap
                    p2_m = set(walk[i] for i in range(k) if seq[i] == 2)
                    p2_nm = set(walk[i] for i in range(k) if seq[i] != 2)
                    p2_ov = p2_m & p2_nm

                    print(f"    P0 binary overlap: {bool(p0_ov)}")
                    print(f"    P1 binary overlap: {bool(analysis['must_overlap_binary'])}")
                    print(f"    P2 binary overlap: {bool(p2_ov)}")

                    # Full ternary-nonmover check for P1
                    # The ternary stays add nonmover vertices. For the walk
                    # to be P1-clean, mover vertices must not be ternary-stay vertices.
                    # The avoidability check already ensured this IS achievable.
                    # But P0 and P2 also get ternary-stay nonmover vertices,
                    # and their full context includes ternary state (c_{n-1} for P0,
                    # c_3 for P2), so the binary subspace check is necessary but
                    # not sufficient for them.
        else:
            print(f"\nn={n}: No surviving walks — P1 overlap FORCED!")
