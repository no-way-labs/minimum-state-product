#!/usr/bin/env python3
"""
Find full good cycles that contain a sorry-pattern mixed phase.

The sorry pattern for the phase alone doesn't produce EC (100% confirmed).
We need the FULL cycle to check if EC arises from interaction between phases.

Strategy: Generate random valid systems with random daemon, find good cycles,
filter for ones containing sorry-pattern phases.

But the first script showed all cycles have non-adjacent pairs at n=9.
This means gap1_ec fires for ALL random cycles at n=9.

KEY INSIGHT: Under ¬EC, ALL consecutive movers must be ring-adjacent.
This is an extreme structural constraint. Maybe the sorry case is about
showing that the full-adjacent constraint + mixed phase + cycle closure
forces some EC somewhere else in the cycle.

Let me try smaller n first where ¬EC cycles might exist.
Also try exhaustive enumeration at small n.
"""
import random
from itertools import product as iterproduct
from collections import defaultdict

random.seed(42)

def ring_adj(a, b, n):
    return min((a - b) % n, (b - a) % n) == 1

def has_ec_at(configs, movers, p, n, ms):
    """Check EC at processor p."""
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
    return bool(mover_triples & nonmover_triples)

def has_any_ec(configs, movers, n, ms):
    for p in range(n):
        if has_ec_at(configs, movers, p, n, ms):
            return True
    return False

def find_noec_cycles(n, ms, num_trials=2000000, max_cycles=1000):
    """Find good cycles with no EC."""
    results = []
    stats = defaultdict(int)

    for trial in range(num_trials):
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

                if CL >= n:
                    stats['cycles'] += 1

                    all_adj = all(ring_adj(cycle_movers[k], cycle_movers[(k+1)%CL], n)
                                  for k in range(CL))
                    if all_adj:
                        stats['all_adj'] += 1
                    else:
                        stats['has_nonadj'] += 1

                    ec = has_any_ec(cycle_configs, cycle_movers, n, ms)
                    if ec:
                        stats['ec'] += 1
                    else:
                        stats['noec'] += 1
                        if not all_adj:
                            stats['noec_nonadj'] += 1
                        else:
                            stats['noec_alladj'] += 1
                            results.append((cycle_configs, cycle_movers, sys_f))
                            if len(results) >= max_cycles:
                                return stats, results
                break
            history.append(config)
            history_movers.append(p)
            config_to_step[config] = step + 1

    return stats, results


def check_sorry_in_cycle(configs, movers, n, t):
    """Check if a cycle has a sorry-pattern mixed phase at processor t."""
    lt = (t - 1) % n
    rt = (t + 1) % n
    llt = (t - 2) % n
    rrt = (t + 2) % n
    CL = len(configs)

    t_fires = [k for k in range(CL) if movers[k] == t]
    if len(t_fires) < 1:
        return False, None

    for idx in range(len(t_fires)):
        s = t_fires[idx]
        prev_t = t_fires[(idx - 1) % len(t_fires)]
        a = (prev_t + 1) % CL

        # Collect phase movers
        phase = []
        k = a
        while k != s:
            phase.append((k, movers[k]))
            k = (k + 1) % CL

        if len(phase) < 2:
            continue

        L_fires = [(k, m) for k, m in phase if m == lt]
        R_fires = [(k, m) for k, m in phase if m == rt]

        if len(L_fires) >= 1 and len(R_fires) >= 1:
            fL = L_fires[0][0]
            fR = R_fires[0][0]

            # Check sorry-L: mover before first L fire = llt
            prev_fL = (fL - 1) % CL
            if movers[prev_fL] == llt:
                return True, {'type': 'sorry-L', 's': s, 'a': a, 'fL': fL, 'fR': fR}

            # Check sorry-R: mover before first R fire = rrt
            prev_fR = (fR - 1) % CL
            if movers[prev_fR] == rrt:
                return True, {'type': 'sorry-R', 's': s, 'a': a, 'fL': fL, 'fR': fR}

    return False, None


def main():
    # Try multiple ring sizes and configurations
    test_configs = [
        (5, [2, 3, 2, 3, 3]),
        (5, [3, 3, 2, 3, 2]),
        (6, [2, 3, 2, 3, 3, 3]),
        (7, [2, 3, 2, 3, 3, 3, 3]),
        (9, [2, 3, 2, 3, 2, 3, 3, 3, 3]),
    ]

    for n, ms in test_configs:
        print(f"=== n={n}, ms={ms} ===")
        stats, noec_cycles = find_noec_cycles(n, ms, num_trials=500000, max_cycles=500)

        print(f"Stats: {dict(stats)}")
        print(f"No-EC all-adjacent cycles: {len(noec_cycles)}")

        if noec_cycles:
            # Check for sorry patterns at every possible t
            sorry_count = 0
            for configs, movers, sys_f in noec_cycles:
                for t in range(n):
                    if ms[t] >= 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2:
                        found, info = check_sorry_in_cycle(configs, movers, n, t)
                        if found:
                            sorry_count += 1
                            CL = len(configs)
                            print(f"  Sorry pattern at t={t}: {info}")
                            print(f"    Cycle len={CL}, movers={movers}")
                            break

            print(f"  Sorry patterns found: {sorry_count}/{len(noec_cycles)}")

        print()


if __name__ == '__main__':
    main()
