"""
Turnaround Binary Provider Proof
=================================
Investigate: when ALL binary procs have turnaround firing patterns,
does a provider (ternary proc t where one neighbor fires 0 and the
other is binary with even fires >= 2) still exist?

Turnaround binary b: both firings arrive and depart from the SAME side.
E.g., both fires have walk arriving from LEFT and departing to LEFT.

Key insight to explore: if b's turnarounds both go LEFT, then right(b)
is never directly connected to b through b's firings. What does this
imply for the phases of right(b)?
"""

from itertools import product as iterproduct
import sys

def enumerate_good_cycles(n, ms):
    """
    Enumerate good cycles for ring of n processors with state counts ms.
    A good cycle visits each (proc, state) pair exactly once as mover.
    Uses mover word representation.
    """
    total_fires = sum(ms)

    # Generate all possible mover sequences (which proc fires at each step)
    # This is too expensive for large n. Use walk-based generation.
    # A "mover word" is a sequence of processor indices of length sum(ms).
    # Each proc p appears exactly ms[p] times.
    # Consecutive movers must be adjacent (ring adjacency).

    # For computational feasibility, we'll use DFS with adjacency constraint.
    from collections import Counter

    remaining = list(ms)
    cycle_len = sum(ms)
    results = []

    def neighbors(p):
        return [(p - 1) % n, (p + 1) % n]

    def dfs(path, remaining):
        if len(path) == cycle_len:
            # Check: last mover adjacent to first (cycle)
            if path[0] in neighbors(path[-1]):
                results.append(tuple(path))
            return

        last = path[-1]
        for nb in neighbors(last):
            if remaining[nb] > 0:
                remaining[nb] -= 1
                path.append(nb)
                dfs(path, remaining)
                path.pop()
                remaining[nb] += 1

    # Start from each processor
    for start in range(n):
        if remaining[start] > 0:
            remaining[start] -= 1
            dfs([start], remaining)
            remaining[start] += 1

    # Remove rotational duplicates
    unique = set()
    for cyc in results:
        # canonical = min rotation
        rotations = [cyc[i:] + cyc[:i] for i in range(len(cyc))]
        canon = min(rotations)
        unique.add(canon)

    return [list(c) for c in unique]


def classify_binary_firing(mover_word, b, n):
    """
    Classify binary proc b's firing pattern in the mover word.
    Returns 'passthrough' or 'turnaround' and details.

    Binary proc fires exactly 2 times. For each firing:
    - arrival direction: which neighbor was the previous mover
    - departure direction: which neighbor is the next mover

    Turnaround: both fires arrive+depart from same side.
    Passthrough: at least one fire has different arrival/departure sides.
    """
    cycle_len = len(mover_word)
    fires = [i for i in range(cycle_len) if mover_word[i] == b]
    assert len(fires) == 2, f"Binary proc {b} fires {len(fires)} times"

    left = (b - 1) % n
    right = (b + 1) % n

    fire_info = []
    for idx in fires:
        prev_mover = mover_word[(idx - 1) % cycle_len]
        next_mover = mover_word[(idx + 1) % cycle_len]

        # Arrival side
        if prev_mover == left:
            arr = 'L'
        elif prev_mover == right:
            arr = 'R'
        else:
            arr = '?'  # not adjacent (shouldn't happen in valid walk)

        # Departure side
        if next_mover == left:
            dep = 'L'
        elif next_mover == right:
            dep = 'R'
        else:
            dep = '?'

        fire_info.append((arr, dep))

    # Turnaround: both fires have arr==dep
    is_turnaround = all(arr == dep for arr, dep in fire_info)

    # Passthrough: at least one fire has arr != dep
    is_passthrough = any(arr != dep for arr, dep in fire_info)

    return {
        'fires': fires,
        'fire_info': fire_info,
        'turnaround': is_turnaround,
        'passthrough': is_passthrough,
    }


def get_winding_number(mover_word, n):
    """
    Compute winding number of the walk around the ring.
    Each step from proc p to proc (p+1)%n counts +1 (CW),
    each step from proc p to proc (p-1)%n counts -1 (CCW).
    Winding = net / n.
    """
    net = 0
    cycle_len = len(mover_word)
    for i in range(cycle_len):
        curr = mover_word[i]
        nxt = mover_word[(i + 1) % cycle_len]
        if nxt == (curr + 1) % n:
            net += 1
        elif nxt == (curr - 1) % n:
            net -= 1
    return net // n


def count_cw_steps(mover_word, n):
    """Count clockwise steps in the walk."""
    cw = 0
    cycle_len = len(mover_word)
    for i in range(cycle_len):
        curr = mover_word[i]
        nxt = mover_word[(i + 1) % cycle_len]
        if nxt == (curr + 1) % n:
            cw += 1
    return cw


def get_firing_counts(mover_word, n):
    """Get firing count per processor."""
    fc = [0] * n
    for p in mover_word:
        fc[p] += 1
    return fc


def find_phases(mover_word, proc, n):
    """
    Find all phases of proc in the mover word.
    A phase of proc t is a maximal consecutive segment of the mover word
    where t does NOT fire. It starts just after t fires and ends just before
    t fires again (or wraps around).

    Returns list of phases, each phase is list of (step_index, mover_proc).
    """
    cycle_len = len(mover_word)
    fires = [i for i in range(cycle_len) if mover_word[i] == proc]

    if len(fires) == 0:
        return [[(i, mover_word[i]) for i in range(cycle_len)]]

    phases = []
    for k in range(len(fires)):
        start = (fires[k] + 1) % cycle_len
        end = fires[(k + 1) % len(fires)]

        phase = []
        i = start
        while i != end:
            phase.append((i, mover_word[i]))
            i = (i + 1) % cycle_len
        phases.append(phase)

    return phases


def check_provider(mover_word, n, ms):
    """
    Check if there exists a provider: proc t (ternary, ms[t]>=3) with
    a TernaryPhase where one neighbor fires 0 (silent) and the other
    is binary (ms=2) with even fires >= 2 (active).

    Returns (True, details) or (False, None).
    """
    binary_procs = [p for p in range(n) if ms[p] == 2]
    ternary_procs = [p for p in range(n) if ms[p] >= 3]

    for t in ternary_procs:
        left = (t - 1) % n
        right = (t + 1) % n

        phases = find_phases(mover_word, t, n)

        for phase_idx, phase in enumerate(phases):
            phase_movers = [m for (_, m) in phase]
            left_fires = phase_movers.count(left)
            right_fires = phase_movers.count(right)

            # Check: one neighbor silent (0 fires), other binary with even fires >= 2
            if left_fires == 0 and right in binary_procs and right_fires >= 2 and right_fires % 2 == 0:
                return True, {'proc': t, 'phase': phase_idx, 'silent': left, 'active': right, 'active_fires': right_fires}
            if right_fires == 0 and left in binary_procs and left_fires >= 2 and left_fires % 2 == 0:
                return True, {'proc': t, 'phase': phase_idx, 'silent': right, 'active': left, 'active_fires': left_fires}

    return False, None


def check_provider_relaxed(mover_word, n, ms):
    """
    More relaxed provider: any ternary proc t with a phase where
    one neighbor fires 0 and the other is binary with fires >= 2.
    (Drop even requirement to see if basic structure holds.)
    """
    binary_procs = [p for p in range(n) if ms[p] == 2]
    ternary_procs = [p for p in range(n) if ms[p] >= 3]

    for t in ternary_procs:
        left = (t - 1) % n
        right = (t + 1) % n

        phases = find_phases(mover_word, t, n)

        for phase_idx, phase in enumerate(phases):
            phase_movers = [m for (_, m) in phase]
            left_fires = phase_movers.count(left)
            right_fires = phase_movers.count(right)

            if left_fires == 0 and right in binary_procs and right_fires >= 2:
                return True, {'proc': t, 'phase': phase_idx, 'silent': left, 'active': right, 'active_fires': right_fires}
            if right_fires == 0 and left in binary_procs and left_fires >= 2:
                return True, {'proc': t, 'phase': phase_idx, 'silent': right, 'active': left, 'active_fires': left_fires}

    return False, None


def analyze_turnaround_structure(mover_word, b, n):
    """
    For turnaround binary b, analyze which side both excursions go to,
    and what happens with the neighbor on the opposite side.
    """
    info = classify_binary_firing(mover_word, b, n)
    if not info['turnaround']:
        return None

    # Determine excursion direction
    directions = [dep for (arr, dep) in info['fire_info']]

    left = (b - 1) % n
    right = (b + 1) % n

    if all(d == 'L' for d in directions):
        excursion_side = 'L'
        isolated_neighbor = right
    elif all(d == 'R' for d in directions):
        excursion_side = 'R'
        isolated_neighbor = left
    else:
        # Mixed turnaround: one goes L, other goes R
        # Both are turnarounds (arr==dep) but different sides
        excursion_side = 'mixed'
        isolated_neighbor = None

    return {
        'binary': b,
        'excursion_side': excursion_side,
        'isolated_neighbor': isolated_neighbor,
        'fire_info': info['fire_info'],
    }


# ============================================================
# MAIN ANALYSIS
# ============================================================

def main():
    # Start with small n where we can enumerate
    # n=5, ms with 3 binary

    print("=" * 70)
    print("TURNAROUND BINARY PROVIDER ANALYSIS")
    print("=" * 70)

    # n=5 is too small (need n>=9), but let's start small to understand structure
    # Then move to targeted analysis at n=9

    for n in [5, 6, 7]:
        # 3 binary procs, rest ternary, sub-threshold product
        # sub-threshold: product < 4 * 3^(n-2)
        threshold = 4 * 3**(n-2)

        # ms with 3 binary (state=2) and (n-3) ternary (state=3)
        ms_base = [2, 2, 2] + [3] * (n - 3)
        prod = 1
        for m in ms_base:
            prod *= m

        print(f"\n{'='*60}")
        print(f"n={n}, ms={ms_base}, product={prod}, threshold={threshold}")
        print(f"Sub-threshold: {prod < threshold}")
        print(f"{'='*60}")

        if prod >= threshold:
            print("NOT sub-threshold, skipping")
            continue

        # Enumerate all good cycles
        print("Enumerating good cycles...")
        cycles = enumerate_good_cycles(n, ms_base)
        print(f"Total good cycles: {len(cycles)}")

        # Filter: zero winding, cwSteps > 0, all fc >= 2
        filtered = []
        for cyc in cycles:
            winding = get_winding_number(cyc, n)
            if winding != 0:
                continue
            cw = count_cw_steps(cyc, n)
            if cw == 0:
                continue
            fc = get_firing_counts(cyc, n)
            if any(f < 2 for f in fc):
                continue
            filtered.append(cyc)

        print(f"Zero-winding, cw>0, all fc>=2: {len(filtered)}")

        # Among filtered, find those where ALL binary procs are turnaround
        all_turnaround_cycles = []
        for cyc in filtered:
            binary_procs = [p for p in range(n) if ms_base[p] == 2]
            all_ta = True
            for b in binary_procs:
                info = classify_binary_firing(cyc, b, n)
                if not info['turnaround']:
                    all_ta = False
                    break
            if all_ta:
                all_turnaround_cycles.append(cyc)

        print(f"All-turnaround cycles: {len(all_turnaround_cycles)}")

        if len(all_turnaround_cycles) == 0:
            print("No all-turnaround cycles found!")
            continue

        # For all-turnaround cycles, check provider existence
        provider_found = 0
        provider_missing = 0

        # Also check which proc q has fc >= 3
        has_fc3 = 0

        for cyc in all_turnaround_cycles:
            fc = get_firing_counts(cyc, n)
            if not any(f >= 3 for f in fc):
                continue
            has_fc3 += 1

            found, details = check_provider(cyc, n, ms_base)
            if found:
                provider_found += 1
            else:
                # Try relaxed
                found_r, details_r = check_provider_relaxed(cyc, n, ms_base)
                provider_missing += 1
                if provider_missing <= 3:
                    print(f"\n  NO PROVIDER: cycle={cyc}")
                    print(f"    fc={fc}")
                    # Show turnaround structure
                    for b in [p for p in range(n) if ms_base[p] == 2]:
                        ta = analyze_turnaround_structure(cyc, b, n)
                        print(f"    Binary {b}: {ta}")
                    # Show all phases of ternary procs
                    for t in [p for p in range(n) if ms_base[p] >= 3]:
                        phases = find_phases(cyc, t, n)
                        print(f"    Ternary {t} phases:")
                        for pi, phase in enumerate(phases):
                            phase_movers = [m for (_, m) in phase]
                            left = (t-1) % n
                            right = (t+1) % n
                            lf = phase_movers.count(left)
                            rf = phase_movers.count(right)
                            print(f"      Phase {pi}: movers={phase_movers}, left({left})={lf}, right({right})={rf}")
                    if found_r:
                        print(f"    RELAXED provider: {details_r}")

        print(f"\nWith fc>=3: {has_fc3}")
        print(f"Provider found: {provider_found}")
        print(f"Provider missing: {provider_missing}")

    # ============================================================
    # KEY STRUCTURAL ANALYSIS
    # ============================================================
    print("\n\n" + "=" * 70)
    print("STRUCTURAL ANALYSIS: Turnaround → Isolated Neighbor")
    print("=" * 70)

    # For each all-turnaround cycle, analyze the isolated neighbor structure
    n = 5
    ms_base = [2, 2, 2, 3, 3]

    cycles = enumerate_good_cycles(n, ms_base)
    filtered = []
    for cyc in cycles:
        winding = get_winding_number(cyc, n)
        if winding != 0:
            continue
        cw = count_cw_steps(cyc, n)
        if cw == 0:
            continue
        fc = get_firing_counts(cyc, n)
        if any(f < 2 for f in fc):
            continue
        if not any(f >= 3 for f in fc):
            continue
        filtered.append(cyc)

    all_ta = []
    for cyc in filtered:
        binary_procs = [p for p in range(n) if ms_base[p] == 2]
        ok = True
        for b in binary_procs:
            info = classify_binary_firing(cyc, b, n)
            if not info['turnaround']:
                ok = False
                break
        if ok:
            all_ta.append(cyc)

    print(f"n={n}, all-turnaround with fc>=3: {len(all_ta)}")

    for cyc in all_ta[:10]:
        fc = get_firing_counts(cyc, n)
        print(f"\nCycle: {cyc}, fc={fc}")
        binary_procs = [p for p in range(n) if ms_base[p] == 2]
        for b in binary_procs:
            ta = analyze_turnaround_structure(cyc, b, n)
            print(f"  Binary {b}: excursion={ta['excursion_side']}, isolated_nbr={ta['isolated_neighbor']}, fire_info={ta['fire_info']}")

            # Check: in phases of isolated neighbor, how many times does b fire?
            if ta['isolated_neighbor'] is not None:
                iso = ta['isolated_neighbor']
                phases = find_phases(cyc, iso, n)
                for pi, phase in enumerate(phases):
                    phase_movers = [m for (_, m) in phase]
                    b_fires_in_phase = phase_movers.count(b)
                    print(f"    Phase {pi} of isolated nbr {iso}: b fires {b_fires_in_phase} times, movers={phase_movers}")


if __name__ == '__main__':
    main()
