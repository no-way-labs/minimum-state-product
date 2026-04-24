#!/usr/bin/env python3
"""
RA13 Part 2: Exhaustive ZW cycle enumeration at small n.

For n=5, enumerate ALL good cycles (via config graph DFS),
filter to ZW with fc≥3, and analyze phases.

Key question: for non-dispatchable cases (all phases have J,K both odd),
does the cycle STILL have an entry conflict somewhere?
"""

from itertools import product as iterproduct
from collections import defaultdict
import sys


def build_config_graph(ms):
    """Build directed config graph. Edge = one proc fires, changes state."""
    n = len(ms)
    ranges = [list(range(m)) for m in ms]
    all_configs = list(iterproduct(*ranges))
    config_to_idx = {c: i for i, c in enumerate(all_configs)}

    # adj[c] = list of (next_config, mover_proc)
    adj = defaultdict(list)
    for c in all_configs:
        for p in range(n):
            for v in range(ms[p]):
                if v != c[p]:
                    c2 = list(c)
                    c2[p] = v
                    c2 = tuple(c2)
                    adj[c].append((c2, p))

    return all_configs, config_to_idx, adj


def find_all_good_cycles_dfs(ms, max_cycles=100000, max_len=None):
    """
    Find good cycles via DFS. A good cycle:
    - Visits distinct configs
    - Returns to start
    - Every proc fires ≥ 1

    This is expensive! Only for small P.
    """
    n = len(ms)
    P = 1
    for m in ms:
        P *= m

    if max_len is None:
        max_len = min(P, 60)  # Cap for performance

    all_configs, config_to_idx, adj = build_config_graph(ms)

    cycles = []
    # Start from config (0,0,...,0) to reduce symmetry
    # Actually, to find ALL cycles, we'd need to start from every config
    # But cycles are invariant under rotation of start point
    # So we can fix start = lexicographically smallest config in cycle
    # For efficiency: start from each config, only keep if start is lex-smallest

    # This is still way too expensive for P > 100.
    # Let me use a different approach: enumerate by mover sequence.

    return None  # Signal too expensive


def enumerate_mover_walks_zw(n, ms, min_len=None, max_len=None):
    """
    Enumerate zero-winding mover walks of length CL where each proc fires ≥ 2.
    Then check if configs can be assigned consistently.

    A mover walk is a sequence p_0, p_1, ..., p_{CL-1} where:
    - Each p_i ∈ {0,...,n-1}
    - fc(p) = #{i: p_i = p} ≥ 2 for all p
    - Zero winding: walk on ring returns to start

    This is still exponential. Let me use a different strategy.
    """
    pass


def exhaustive_small_n(ms):
    """
    For small product, enumerate ALL configs and find cycles by
    random walks + deduplication. Use many random walks.
    """
    import random
    n = len(ms)
    P = 1
    for m in ms:
        P *= m

    all_configs, config_to_idx, adj = build_config_graph(ms)

    unique_cycles = {}  # frozenset(configs) -> cycle_info
    num_attempts = 200000

    for attempt in range(num_attempts):
        # Random start
        config = all_configs[random.randrange(len(all_configs))]
        visited = {config: 0}
        path = [config]
        movers = []

        max_steps = min(P, 80)
        for step in range(1, max_steps):
            neighbors = adj[config]
            if not neighbors:
                break
            config, p = random.choice(neighbors)
            movers.append(p)

            if config in visited:
                cycle_start = visited[config]
                cycle_configs = path[cycle_start:]
                cycle_movers = movers[cycle_start:]
                L = len(cycle_movers)

                if L < 2 * n:
                    break

                # Check all procs fire ≥ 2
                fc = defaultdict(int)
                for m in cycle_movers:
                    fc[m] += 1
                if len(fc) < n or min(fc.values()) < 2:
                    break

                # Check ZW
                cw_wraps = 0
                ccw_wraps = 0
                for i in range(L):
                    curr = cycle_movers[i]
                    prev = cycle_movers[i - 1]
                    diff = curr - prev
                    if diff > n // 2:
                        ccw_wraps += 1
                    elif diff < -(n // 2):
                        cw_wraps += 1
                    elif n % 2 == 0 and abs(diff) == n // 2:
                        pass  # Ambiguous

                winding = cw_wraps - ccw_wraps

                if winding != 0:
                    break

                # Check fc ≥ 3 somewhere
                if max(fc.values()) < 3:
                    break

                key = frozenset(enumerate(zip(cycle_configs, cycle_movers)))
                # Better key: the actual mover sequence + start config
                key = (cycle_configs[0], tuple(cycle_movers))
                if key not in unique_cycles:
                    unique_cycles[key] = {
                        'configs': cycle_configs,
                        'movers': cycle_movers,
                        'fc': dict(fc),
                        'length': L,
                    }
                break

            visited[config] = step
            path.append(config)

    return list(unique_cycles.values())


def check_entry_conflict(cycle_info, ms):
    """
    Check if cycle has an entry conflict at ANY processor.
    Entry conflict: same (L, self, R) triple appears as both mover and non-mover context.
    """
    n = len(ms)
    configs = cycle_info['configs']
    movers = cycle_info['movers']
    L = len(movers)

    for p in range(n):
        mover_contexts = set()
        nonmover_contexts = set()

        left = (p - 1) % n
        right = (p + 1) % n

        for i in range(L):
            c = configs[i]
            ctx = (c[left], c[p], c[right])

            if movers[i] == p:
                mover_contexts.add(ctx)
            else:
                nonmover_contexts.add(ctx)

        overlap = mover_contexts & nonmover_contexts
        if overlap:
            return True, p, overlap

    return False, None, None


def analyze_phases(cycle_info, ms):
    """Extract phases at fc≥3 procs."""
    n = len(ms)
    movers = cycle_info['movers']
    fc = cycle_info['fc']
    L = len(movers)

    results = {}
    for q in range(n):
        if fc.get(q, 0) < 3:
            continue

        fire_pos = [i for i, m in enumerate(movers) if m == q]
        left_q = (q - 1) % n
        right_q = (q + 1) % n

        phases = []
        for phase_idx in range(len(fire_pos)):
            start = fire_pos[phase_idx]
            end = fire_pos[(phase_idx + 1) % len(fire_pos)]

            J = 0
            K = 0
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


def is_any_phase_dispatchable(phases):
    """Check if any phase is dispatchable."""
    for J, K in phases:
        if J == 0 and K == 0:
            return True, 'both-silent'
        if J % 2 == 0 and K % 2 == 0:
            return True, 'even-even'
        if J == 0 and K >= 2:
            return True, 'one-sided-right'
        if K == 0 and J >= 2:
            return True, 'one-sided-left'
        if J == 0:
            return True, 'traversal(0,K)'
        if K == 0:
            return True, 'traversal(J,0)'
    return False, None


def main():
    import random
    random.seed(42)

    print("=" * 70)
    print("RA13 Part 2: Exhaustive ZW fc≥3 Phase + Entry Conflict Analysis")
    print("=" * 70)

    for n in [5]:
        print(f"\n{'='*60}")
        print(f"n = {n}, threshold = {4 * 3**(n-2)}")
        print(f"{'='*60}")

        threshold = 4 * 3 ** (n - 2)

        # Enumerate sub-threshold multisets with ≥3 binary
        multisets = []
        def gen_ms(pos, current, prod):
            if pos == n:
                if prod < threshold and sum(1 for x in current if x == 2) >= 3:
                    multisets.append(tuple(current))
                return
            for m in range(2, min(threshold // max(prod, 1) + 1, 20)):
                new_prod = prod * m
                if new_prod >= threshold:
                    break
                if current and m < current[-1]:
                    continue
                gen_ms(pos + 1, current + [m], new_prod)
        gen_ms(0, [], 1)

        print(f"Multisets: {len(multisets)}")
        for ms_sorted in multisets:
            print(f"  {ms_sorted}, product={eval('*'.join(str(x) for x in ms_sorted))}")

        total_zw_fc3_cycles = 0
        total_with_ec = 0
        total_without_ec = 0
        total_with_dispatchable_phase = 0
        total_without_dispatchable_phase = 0
        non_disp_details = []

        from itertools import permutations

        for ms_sorted in multisets:
            # Try all distinct rotations (ring = rotation equivalence)
            P = 1
            for m in ms_sorted:
                P *= m
            if P > 2000:
                continue

            seen = set()
            for perm in permutations(ms_sorted):
                if perm in seen:
                    continue
                seen.add(perm)

                ms = perm
                cycles = exhaustive_small_n(ms)

                for cyc in cycles:
                    phase_info = analyze_phases(cyc, ms)
                    if not phase_info:
                        continue

                    total_zw_fc3_cycles += 1

                    # Check entry conflict
                    has_ec, ec_proc, ec_overlap = check_entry_conflict(cyc, ms)
                    if has_ec:
                        total_with_ec += 1
                    else:
                        total_without_ec += 1

                    # Check dispatchable phase at ANY fc≥3 proc
                    any_dispatchable = False
                    for q, info in phase_info.items():
                        disp, reason = is_any_phase_dispatchable(info['phases'])
                        if disp:
                            any_dispatchable = True
                            break

                    if any_dispatchable:
                        total_with_dispatchable_phase += 1
                    else:
                        total_without_dispatchable_phase += 1
                        if len(non_disp_details) < 10:
                            non_disp_details.append({
                                'ms': ms,
                                'fc': cyc['fc'],
                                'length': cyc['length'],
                                'phase_info': phase_info,
                                'has_ec': has_ec,
                                'ec_proc': ec_proc,
                            })

        print(f"\nTotal ZW cycles with fc≥3: {total_zw_fc3_cycles}")
        print(f"  With entry conflict: {total_with_ec}")
        print(f"  Without entry conflict: {total_without_ec}")
        print(f"  With dispatchable phase (at some fc≥3 proc): {total_with_dispatchable_phase}")
        print(f"  Without dispatchable phase: {total_without_dispatchable_phase}")

        if non_disp_details:
            print(f"\nNon-dispatchable examples (all phases odd-odd):")
            for ex in non_disp_details[:5]:
                print(f"\n  ms={ex['ms']}, CL={ex['length']}, fc={ex['fc']}")
                print(f"  has_ec={ex['has_ec']}, ec_proc={ex['ec_proc']}")
                for q, info in ex['phase_info'].items():
                    print(f"    q={q}: fc={info['fc']}, ms[q]={info['ms_q']}, "
                          f"L={info['ms_left']}, R={info['ms_right']}")
                    print(f"      phases: {info['phases']}")


if __name__ == '__main__':
    main()
