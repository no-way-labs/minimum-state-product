#!/usr/bin/env python3
"""
RA13: Zero-winding fc≥3 phase analysis.

For ZW good cycles with some fc(q) ≥ 3, check:
1. Is the fc≥3 proc always ternary? Can it be binary (fc≥4)?
2. Does the fc≥3 proc always have a binary neighbor?
3. Extract phases at fc≥3 proc. Check (J,K) patterns.
4. Does every cycle have a DISPATCHABLE phase?
   Dispatchable = even-even (J%2=K%2=0), one-sided (J=0,K≥2 or K=0,J≥2),
   both-silent (J=0,K=0), or traversal-return territory.

We enumerate ALL good cycles for sub-threshold multisets with ≥3 binary.
"""

from itertools import product as iterproduct
from collections import defaultdict
import sys


def get_sub_threshold_multisets(n):
    """Get all multisets with ≥3 binary, product < 4*3^(n-2)."""
    threshold = 4 * (3 ** (n - 2))
    results = []
    # Generate multisets: each m_i ≥ 2
    # For small n, enumerate
    if n > 7:
        # For n=9, just use canonical: (2,2,2,3,3,3,3,3,3) etc
        # Actually let's be smarter - enumerate multisets with ≥3 entries = 2
        # and rest ≥ 3, product < threshold
        from itertools import combinations_with_replacement
        # positions of binary procs don't matter for enumeration, just count
        # We need sorted multisets
        def gen_ms(pos, current, prod):
            if pos == n:
                if prod < threshold and sum(1 for x in current if x == 2) >= 3:
                    results.append(tuple(current))
                return
            remaining = n - pos
            for m in range(2, threshold // prod + 1 if prod > 0 else 10):
                if m > 10:
                    break
                new_prod = prod * m
                if new_prod * (2 ** (remaining - 1)) >= threshold and m > 2:
                    # Even all remaining = 2 won't help if current is too big
                    # Actually we need new_prod * 2^(remaining-1) < threshold
                    pass
                if new_prod >= threshold:
                    break
                # Ensure sorted (non-decreasing)
                if current and m < current[-1]:
                    continue
                gen_ms(pos + 1, current + [m], new_prod)
        gen_ms(0, [], 1)
    else:
        def gen_ms(pos, current, prod):
            if pos == n:
                if prod < threshold and sum(1 for x in current if x == 2) >= 3:
                    results.append(tuple(current))
                return
            for m in range(2, min(threshold // max(prod, 1) + 1, 20)):
                new_prod = prod * m
                if new_prod >= threshold:
                    break
                if current and m < current[-1]:
                    continue
                gen_ms(pos + 1, current + [m], new_prod)
        gen_ms(0, [], 1)
    return results


def all_good_cycles_zw(ms, max_cycles=50000):
    """
    Enumerate good cycles for ring with state sizes ms.
    A good cycle visits distinct configs, each proc fires exactly fc(p) times,
    and returns to start.

    We do DFS on the configuration graph.
    A "good cycle" = Hamiltonian cycle on the set of good configs?
    No - a good cycle is any cycle in the config graph where:
    - All configs are distinct
    - Every proc fires ≥ 1 time (actually ≥ 2 for sub-threshold)
    - The cycle is a valid sequence of single-proc moves

    Actually, let me think about what a "good cycle" means in context:
    A good cycle is a cyclic sequence of configurations c_0, c_1, ..., c_{L-1}
    where:
    - Each c_i is distinct
    - At each step, exactly one proc fires (mover)
    - The mover changes its state
    - c_0 follows c_{L-1}

    For ZW: totalDisplacement = 0 (sum of mover directions = 0)

    This is expensive. Let me use a smarter approach.
    """
    n = len(ms)
    P = 1
    for m in ms:
        P *= m

    # For small P, enumerate all configs and build transition graph
    if P > 5000:
        return []  # Too large

    # Build all configs
    ranges = [list(range(m)) for m in ms]
    all_configs = list(iterproduct(*ranges))
    config_to_idx = {c: i for i, c in enumerate(all_configs)}

    # Build adjacency: config -> list of (next_config, mover, direction)
    # direction: +1 = CW (mover index increases), -1 = CCW, 0 = stay?
    # Actually: mover fires, changing c[p] to some new value
    # Direction is determined by the mover position relative to previous mover
    #
    # Wait - "direction" in the ring walk sense:
    # The mover at step t is proc p_t. The displacement is p_t - p_{t-1} mod n.
    # CW = +1, CCW = -1, stay = 0.
    # Total displacement = sum of (p_t - p_{t-1}) mod n...
    # Actually it's simpler: the "winding" is about the walk of mover positions.

    # Let me just enumerate cycles via DFS with tracking.
    # This is too expensive for large P.

    # Instead: let me just find cycles by random walk + checking,
    # or use a structured approach.

    # Actually, for the phase analysis, I don't need ALL cycles.
    # I need a representative sample of ZW cycles with fc ≥ 3.
    # Let me use random simulation.

    return None  # Signal to use random approach


def find_zw_cycles_random(ms, num_samples=10000, max_cycle_len=200):
    """Find ZW good cycles by random walk on config graph."""
    import random
    n = len(ms)
    P = 1
    for m in ms:
        P *= m

    cycles_found = []

    for _ in range(num_samples):
        # Random starting config
        config = tuple(random.randrange(m) for m in ms)
        visited = {config: 0}  # config -> step index
        path = [config]
        movers = []

        for step in range(1, max_cycle_len):
            # Choose random mover and new value
            p = random.randrange(n)
            old_val = config[p]
            new_val = random.choice([v for v in range(ms[p]) if v != old_val])
            config = list(config)
            config[p] = new_val
            config = tuple(config)
            movers.append(p)

            if config in visited:
                # Found a cycle!
                cycle_start = visited[config]
                cycle_configs = path[cycle_start:]
                cycle_movers = movers[cycle_start:]

                # Check ZW and fc
                if len(cycle_configs) < 2 * n:
                    break

                fc = defaultdict(int)
                for m in cycle_movers:
                    fc[m] += 1

                # Check all procs fire
                if len(fc) < n:
                    break

                # Check ZW: compute displacement
                L = len(cycle_movers)
                total_disp = 0
                for i in range(L):
                    disp = (cycle_movers[i] - cycle_movers[i-1]) % n
                    if disp > n // 2:
                        disp -= n
                    elif disp == n // 2 and n % 2 == 0:
                        # Ambiguous, skip
                        pass
                    total_disp += disp

                # Hmm, displacement is tricky. Let me use a different ZW definition.
                # Zero winding = the mover sequence, viewed as a walk on Z_n,
                # has winding number 0.
                # Winding number = (number of CW wraps) - (number of CCW wraps)
                # A CW wrap = when mover goes from n-1 to 0 (or crosses the 0/n-1 boundary CW)

                cw_wraps = 0
                ccw_wraps = 0
                for i in range(L):
                    curr = cycle_movers[i]
                    prev = cycle_movers[i-1]  # wraps to last for i=0
                    diff = curr - prev
                    if diff > n // 2:
                        ccw_wraps += 1
                    elif diff < -n // 2:
                        cw_wraps += 1
                    # For diff exactly n//2 with even n, ambiguous

                winding = cw_wraps - ccw_wraps

                if winding == 0 and max(fc.values()) >= 3:
                    # Check no safe processor
                    mover_set = set(fc.keys())
                    no_safe = True
                    for p in range(n):
                        neighbors = {(p-1) % n, p, (p+1) % n}
                        if not neighbors & mover_set:
                            no_safe = False
                            break

                    if no_safe:
                        cycle_key = frozenset(cycle_configs)
                        cycles_found.append({
                            'configs': cycle_configs,
                            'movers': cycle_movers,
                            'fc': dict(fc),
                            'winding': winding,
                            'cw_wraps': cw_wraps,
                            'ccw_wraps': ccw_wraps,
                            'length': L,
                        })
                break

            visited[config] = step
            path.append(config)

    return cycles_found


def analyze_phases(cycle_info, ms):
    """
    For each proc q with fc(q) ≥ 3, extract phases and (J,K) patterns.

    A "phase" at proc q = the segment between consecutive firings of q.
    If q fires fc times, there are fc phases.
    In each phase, J = number of times left(q) fires, K = number of times right(q) fires.
    """
    n = len(ms)
    movers = cycle_info['movers']
    fc = cycle_info['fc']
    L = len(movers)

    results = {}

    for q in range(n):
        if fc.get(q, 0) < 3:
            continue

        # Find firing positions of q
        fire_pos = [i for i, m in enumerate(movers) if m == q]
        num_phases = len(fire_pos)

        left_q = (q - 1) % n
        right_q = (q + 1) % n

        phases = []
        for phase_idx in range(num_phases):
            start = fire_pos[phase_idx]
            end = fire_pos[(phase_idx + 1) % num_phases]

            # Count fires of left and right in this phase (exclusive of endpoints)
            J = 0  # left fires
            K = 0  # right fires

            pos = (start + 1) % L
            while pos != end:
                if movers[pos] == left_q:
                    J += 1
                if movers[pos] == right_q:
                    K += 1
                pos = (pos + 1) % L

            phases.append((J, K))

        results[q] = {
            'fc': fc[q],
            'ms_q': ms[q],
            'ms_left': ms[left_q],
            'ms_right': ms[right_q],
            'phases': phases,
            'is_binary': ms[q] == 2,
            'left_is_binary': ms[left_q] == 2,
            'right_is_binary': ms[right_q] == 2,
        }

    return results


def is_dispatchable(J, K):
    """Check if a (J,K) phase pattern is dispatchable."""
    # Both-silent
    if J == 0 and K == 0:
        return 'both-silent'
    # Even-even (includes (0,0))
    if J % 2 == 0 and K % 2 == 0:
        return 'even-even'
    # One-sided with ≥2
    if J == 0 and K >= 2:
        return 'one-sided-right'
    if K == 0 and J >= 2:
        return 'one-sided-left'
    # One-sided with 1
    if J == 0 and K == 1:
        return 'traversal(0,1)'
    if K == 0 and J == 1:
        return 'traversal(1,0)'
    return None


def main():
    print("=" * 70)
    print("RA13: Zero-Winding fc≥3 Phase Analysis")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n{'='*60}")
        print(f"n = {n}")
        print(f"{'='*60}")

        multisets = get_sub_threshold_multisets(n)
        print(f"Sub-threshold multisets with ≥3 binary: {len(multisets)}")

        if not multisets:
            continue

        # For each multiset, try all rotations
        total_zw_fc3 = 0
        total_dispatchable = 0
        total_not_dispatchable = 0
        fc3_at_binary = 0
        fc3_at_ternary = 0
        fc3_with_binary_neighbor = 0

        phase_pattern_counts = defaultdict(int)
        non_dispatchable_examples = []

        for ms_sorted in multisets[:10]:  # Limit multisets
            # Try several rotations/permutations
            from itertools import permutations
            seen_perms = set()
            perm_list = []
            for perm in permutations(ms_sorted):
                if perm not in seen_perms:
                    seen_perms.add(perm)
                    perm_list.append(perm)
                if len(perm_list) > 20:
                    break

            for ms in perm_list[:10]:  # Limit permutations
                P = 1
                for m in ms:
                    P *= m
                if P > 3000:
                    continue

                cycles = find_zw_cycles_random(ms, num_samples=5000)

                for cyc in cycles:
                    phase_info = analyze_phases(cyc, ms)

                    for q, info in phase_info.items():
                        total_zw_fc3 += 1

                        if info['is_binary']:
                            fc3_at_binary += 1
                        else:
                            fc3_at_ternary += 1

                        if info['left_is_binary'] or info['right_is_binary']:
                            fc3_with_binary_neighbor += 1

                        # Check if ANY phase is dispatchable
                        has_dispatchable = False
                        for J, K in info['phases']:
                            d = is_dispatchable(J, K)
                            if d:
                                has_dispatchable = True
                                phase_pattern_counts[d] += 1
                                break  # One is enough

                        if has_dispatchable:
                            total_dispatchable += 1
                        else:
                            total_not_dispatchable += 1
                            if len(non_dispatchable_examples) < 5:
                                non_dispatchable_examples.append({
                                    'ms': ms,
                                    'q': q,
                                    'info': info,
                                    'cycle_len': cyc['length'],
                                    'fc': cyc['fc'],
                                })

        print(f"\nTotal fc≥3 procs in ZW cycles: {total_zw_fc3}")
        print(f"  At binary proc: {fc3_at_binary}")
        print(f"  At ternary proc: {fc3_at_ternary}")
        print(f"  With binary neighbor: {fc3_with_binary_neighbor}")
        print(f"\nDispatchable: {total_dispatchable}/{total_zw_fc3}")
        print(f"Not dispatchable: {total_not_dispatchable}/{total_zw_fc3}")
        print(f"\nPhase pattern counts (first dispatchable found):")
        for pat, cnt in sorted(phase_pattern_counts.items(), key=lambda x: -x[1]):
            print(f"  {pat}: {cnt}")

        if non_dispatchable_examples:
            print(f"\nNon-dispatchable examples:")
            for ex in non_dispatchable_examples:
                print(f"  ms={ex['ms']}, q={ex['q']}, fc(q)={ex['info']['fc']}")
                print(f"    phases (J,K): {ex['info']['phases']}")
                print(f"    ms[q]={ex['info']['ms_q']}, left={ex['info']['ms_left']}, right={ex['info']['ms_right']}")


if __name__ == '__main__':
    main()
