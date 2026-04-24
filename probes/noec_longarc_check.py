#!/usr/bin/env python3
"""Exhaustive check: at n=9 sub-threshold, do ¬EC good cycles with
≥3 non-consecutive binary and a ternary pivot have mixed phases?

Also: what is the phase structure of ¬EC cycles?"""
import random
from itertools import product as iterproduct

random.seed(42)

def ring_dist(a, b, n):
    return min((a - b) % n, (b - a) % n)

def has_entry_conflict(configs, movers, n):
    CL = len(configs)
    for p in range(n):
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
        if mover_triples & nonmover_triples:
            return True
    return False

def check_noec_phases(n, ms, num_trials=2000000):
    noec_count = 0
    mixed_count = 0
    phase_info = []

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
                    ec = has_entry_conflict(cycle_configs, cycle_movers, n)
                    if not ec:
                        noec_count += 1
                        # Analyze phases at pivots with binary neighbors
                        for t in range(n):
                            lt, rt = (t-1)%n, (t+1)%n
                            if ms[t] < 3 or ms[lt] != 2 or ms[rt] != 2:
                                continue
                            fires = [k for k in range(CL) if cycle_movers[k] == t]
                            F = len(fires)
                            if F < 1:
                                continue
                            for idx in range(F):
                                s = fires[idx]
                                prev = fires[(idx-1) % F]
                                if prev < s:
                                    pm = cycle_movers[prev+1:s]
                                else:
                                    pm = cycle_movers[prev+1:] + cycle_movers[:s]
                                J = sum(1 for m in pm if m == lt)
                                K = sum(1 for m in pm if m == rt)
                                if J >= 1 and K >= 1:
                                    mixed_count += 1
                                    if noec_count <= 20:
                                        phase_info.append({
                                            't': t, 'J': J, 'K': K,
                                            'pm': pm, 'CL': CL
                                        })
                                # Record phase J,K for statistics
                                if noec_count <= 10:
                                    phase_info.append({
                                        't': t, 'J': J, 'K': K,
                                        'pm_len': len(pm), 'CL': CL,
                                        'mixed': J>=1 and K>=1
                                    })
                break
            history.append(config)
            history_movers.append(p)
            config_to_step[config] = step + 1

    return noec_count, mixed_count, phase_info

# Test multiple multisets at n=9
multisets = [
    [2,2,2,3,3,3,3,3,3],
    [2,3,2,3,2,3,3,3,3],
    [3,2,3,2,3,3,3,2,3],
    [2,2,3,3,2,3,3,3,3],
]

for ms in multisets:
    n = len(ms)
    print(f"n={n} ms={ms}")
    noec, mixed, info = check_noec_phases(n, ms, 1000000)
    print(f"  ¬EC cycles: {noec}, mixed phases: {mixed}")
    if noec > 0 and info:
        for item in info[:10]:
            if isinstance(item.get('pm'), list):
                print(f"    MIXED t={item['t']} J={item['J']} K={item['K']} movers={item['pm'][:15]}")
            else:
                if not item.get('mixed', False):
                    print(f"    phase t={item['t']} J={item['J']} K={item['K']} len={item['pm_len']} CL={item['CL']}")
    print()
