#!/usr/bin/env python3
"""
Investigate entry conflict in mixed phases where the "sorry" case holds:
- left²(t) fires immediately before first left(t) fire
- right²(t) fires immediately before first right(t) fire
- All consecutive movers are ring-adjacent

Ring: n=9, ms=[2,3,2,3,2,3,3,3,3], t=1 (ternary), lt=0 (binary), rt=2 (binary).

Strategy: Generate random good cycles, filter for ¬EC + mixed phases with the
sorry pattern, then check EVERY processor for entry conflict to find what
construction closes the sorry.
"""
import random
from itertools import product as iterproduct
from collections import defaultdict

random.seed(42)

def ring_adj(a, b, n):
    return (a - b) % n <= 1 or (b - a) % n <= 1

def has_entry_conflict_at(configs, movers, p, n):
    """Check if processor p has an entry conflict."""
    CL = len(configs)
    mover_triples = set()
    nonmover_triples = set()
    for k in range(CL):
        L = configs[k][(p-1)%n]
        S = configs[k][p]
        R = configs[k][(p+1)%n]
        triple = (L, S, R)
        if movers[k] == p:
            mover_triples.add(triple)
        else:
            nonmover_triples.add(triple)
    overlap = mover_triples & nonmover_triples
    return overlap

def has_any_ec(configs, movers, n):
    for p in range(n):
        if has_entry_conflict_at(configs, movers, p, n):
            return True
    return False

def find_mixed_phase_sorry_cases(n, ms, t, num_trials=2000000):
    """Find good cycles with mixed phases matching the sorry pattern."""
    lt = (t - 1) % n
    rt = (t + 1) % n
    llt = (t - 2) % n  # left²(t)
    rrt = (t + 2) % n  # right²(t)

    stats = defaultdict(int)
    sorry_cases = []

    for trial in range(num_trials):
        # Random transition system
        sys_f = {}
        for i in range(n):
            f = {}
            for L in range(ms[(i-1)%n]):
                for S in range(ms[i]):
                    for R in range(ms[(i+1)%n]):
                        f[(L, S, R)] = random.randint(0, ms[i] - 1)
            sys_f[i] = f

        config = tuple(random.randint(0, ms[i]-1) for i in range(n))
        history = [config]
        history_movers = []
        config_to_step = {config: 0}

        found = False
        for step in range(3000):
            privs = [i for i in range(n)
                     if sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])] != config[i]]
            if not privs:
                break
            p = random.choice(privs)
            nc = list(config)
            nc[p] = sys_f[p][(config[(p-1)%n], config[p], config[(p+1)%n])]
            config = tuple(nc)

            if config in config_to_step:
                cs = config_to_step[config]
                cycle_configs = history[cs:]
                cycle_movers = history_movers[cs:] + [p]
                CL = len(cycle_configs)

                if CL >= 2 * n:
                    stats['cycles'] += 1

                    # Check all consecutive movers are ring-adjacent
                    all_adj = all(ring_adj(cycle_movers[k], cycle_movers[(k+1)%CL], n)
                                  for k in range(CL))
                    if not all_adj:
                        stats['has_nonadj'] += 1
                        # If there's a non-adjacent pair, gap1_ec fires -> EC exists
                        break

                    # Check for entry conflict
                    ec = has_any_ec(cycle_configs, cycle_movers, n)
                    if ec:
                        stats['ec'] += 1
                        break

                    stats['noec_alladj'] += 1

                    # Find mixed phases for processor t
                    # A t-phase is an interval [a, s) where t fires at step s,
                    # doesn't fire in [a, s), and moverAt(a) ≠ t
                    t_fires = [k for k in range(CL) if cycle_movers[k] == t]
                    if len(t_fires) < 2:
                        stats['few_t_fires'] += 1
                        break

                    for idx in range(len(t_fires)):
                        s = t_fires[idx]
                        # Previous t-fire
                        prev_t = t_fires[(idx - 1) % len(t_fires)]
                        # Phase is (prev_t, s] in cyclic sense,
                        # but interior = steps after prev_t+1 up to s-1
                        # Actually: phase [a, s) where a = prev_t + 1
                        a = (prev_t + 1) % CL

                        # Collect movers in [a, s) cyclically
                        phase_movers = []
                        k = a
                        while k != s:
                            phase_movers.append((k, cycle_movers[k]))
                            k = (k + 1) % CL

                        if len(phase_movers) < 2:
                            continue

                        # Count L and R fires
                        L_fires = [(k, m) for k, m in phase_movers if m == lt]
                        R_fires = [(k, m) for k, m in phase_movers if m == rt]

                        J = len(L_fires)
                        K = len(R_fires)

                        if J >= 1 and K >= 1:
                            stats['mixed_phases'] += 1

                            # Check sorry pattern:
                            # First L fire, first R fire
                            fL = L_fires[0][0]
                            fR = R_fires[0][0]

                            # Step before fL
                            prev_fL = (fL - 1) % CL
                            # Step before fR
                            prev_fR = (fR - 1) % CL

                            # Sorry case: mover at prev_fL = llt, mover at prev_fR = rrt
                            mover_prev_fL = cycle_movers[prev_fL]
                            mover_prev_fR = cycle_movers[prev_fR]

                            if mover_prev_fL == llt and mover_prev_fR == rrt:
                                stats['sorry_pattern'] += 1
                                sorry_cases.append({
                                    'configs': cycle_configs,
                                    'movers': cycle_movers,
                                    'sys_f': sys_f,
                                    't': t,
                                    'phase_a': a,
                                    'phase_s': s,
                                    'fL': fL,
                                    'fR': fR,
                                    'J': J,
                                    'K': K,
                                    'phase_movers': phase_movers,
                                })
                                if len(sorry_cases) >= 500:
                                    return stats, sorry_cases
                break
            history.append(config)
            history_movers.append(p)
            config_to_step[config] = step + 1

    return stats, sorry_cases


def analyze_sorry_cases(sorry_cases, n, ms):
    """For each sorry case, check EVERY processor for EC."""
    ec_processor_counts = defaultdict(int)
    ec_details = []
    no_ec_cases = []

    for case in sorry_cases:
        configs = case['configs']
        movers = case['movers']
        t = case['t']
        CL = len(configs)

        found_ec = False
        for p in range(n):
            overlap = has_entry_conflict_at(configs, movers, p, n)
            if overlap:
                ec_processor_counts[p] += len(overlap)
                found_ec = True
                ec_details.append({
                    'processor': p,
                    'overlaps': overlap,
                    'case': case,
                })

        if not found_ec:
            no_ec_cases.append(case)

    return ec_processor_counts, ec_details, no_ec_cases


def main():
    n = 9
    # t=1 (ternary, m=3), lt=0 (binary, m=2), rt=2 (binary, m=2)
    ms = [2, 3, 2, 3, 2, 3, 3, 3, 3]
    t = 1

    print(f"Ring: n={n}, ms={ms}, t={t}")
    print(f"  lt={0}, rt={2}, llt={8}, rrt={3}")
    print(f"Searching for good cycles with mixed-phase sorry pattern...")
    print()

    stats, sorry_cases = find_mixed_phase_sorry_cases(n, ms, t, num_trials=2000000)

    print("=== Search Statistics ===")
    for k, v in sorted(stats.items()):
        print(f"  {k}: {v}")
    print(f"  sorry cases found: {len(sorry_cases)}")
    print()

    if not sorry_cases:
        print("No sorry cases found. Trying with relaxed criteria...")
        return

    print("=== Analyzing sorry cases for EC at each processor ===")
    ec_counts, ec_details, no_ec_cases = analyze_sorry_cases(sorry_cases, n, ms)

    print(f"Cases with EC found: {len(sorry_cases) - len(no_ec_cases)}/{len(sorry_cases)}")
    print(f"Cases with NO EC: {len(no_ec_cases)}")
    print()

    print("EC by processor:")
    for p in range(n):
        cnt = ec_counts.get(p, 0)
        print(f"  proc {p} (m={ms[p]}): {cnt} EC overlaps")
    print()

    if no_ec_cases:
        print("WARNING: Found cases with NO entry conflict!")
        case = no_ec_cases[0]
        print(f"  Phase: [{case['phase_a']}, {case['phase_s']})")
        print(f"  Phase movers: {[m for _, m in case['phase_movers']]}")
        print(f"  All movers: {case['movers']}")
    else:
        print("ALL sorry cases have EC somewhere!")
        # Find which processor is ALWAYS the EC location
        always_ec = []
        for p in range(n):
            all_have = True
            for case in sorry_cases:
                overlap = has_entry_conflict_at(case['configs'], case['movers'], p, n)
                if not overlap:
                    all_have = False
                    break
            if all_have:
                always_ec.append(p)

        print(f"Processors with EC in ALL cases: {always_ec}")

    # Detailed analysis of first few cases
    print("\n=== Detailed analysis of first 5 sorry cases ===")
    for i, case in enumerate(sorry_cases[:5]):
        configs = case['configs']
        movers = case['movers']
        CL = len(configs)
        t = case['t']
        lt = (t-1) % n
        rt = (t+1) % n

        print(f"\n--- Case {i+1}: cycle length {CL}, J={case['J']}, K={case['K']} ---")
        print(f"  Phase [{case['phase_a']}, {case['phase_s']})")
        print(f"  Phase movers: {[m for _, m in case['phase_movers']]}")

        # Show EC at each processor
        for p in range(n):
            overlap = has_entry_conflict_at(configs, movers, p, n)
            if overlap:
                # Find the specific mover/nonmover steps
                for triple in overlap:
                    mover_steps = [k for k in range(CL) if movers[k] == p and
                                   (configs[k][(p-1)%n], configs[k][p], configs[k][(p+1)%n]) == triple]
                    nonmover_steps = [k for k in range(CL) if movers[k] != p and
                                      (configs[k][(p-1)%n], configs[k][p], configs[k][(p+1)%n]) == triple]
                    print(f"  EC at proc {p}: triple={triple}, mover_steps={mover_steps[:3]}, nonmover_steps={nonmover_steps[:3]}")

if __name__ == '__main__':
    main()
