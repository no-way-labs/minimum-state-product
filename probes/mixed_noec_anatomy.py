#!/usr/bin/env python3
"""Find and analyze actual ¬EC cycles with mixed phases at n=5.
Understand the walk structure — these are NOT long arcs."""
import random

random.seed(42)

def ring_dist(a, b, n):
    return min((a - b) % n, (b - a) % n)

def has_entry_conflict(configs, movers, n):
    CL = len(configs)
    for p in range(n):
        mt = set()
        nmt = set()
        for k in range(CL):
            triple = (configs[k][(p-1)%n], configs[k][p], configs[k][(p+1)%n])
            if movers[k] == p:
                mt.add(triple)
            else:
                nmt.add(triple)
        if mt & nmt:
            return True
    return False

n = 5
ms_list = [
    [2, 3, 2, 3, 2],
    [2, 2, 3, 2, 3],
    [3, 2, 2, 3, 2],
]

found = 0
for ms in ms_list:
    print(f"\nms={ms}")
    for trial in range(500000):
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

        for step in range(2000):
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
                        # Check for mixed phases
                        for t in range(n):
                            lt, rt = (t-1)%n, (t+1)%n
                            if ms[t] < 3 or ms[lt] != 2 or ms[rt] != 2:
                                continue
                            fires = [k for k in range(CL) if cycle_movers[k] == t]
                            F = len(fires)
                            if F < 1:
                                continue
                            for idx in range(F):
                                s_step = fires[idx]
                                prev = fires[(idx-1) % F]
                                if prev < s_step:
                                    pm = cycle_movers[prev+1:s_step]
                                else:
                                    pm = cycle_movers[prev+1:] + cycle_movers[:s_step]
                                J = sum(1 for m in pm if m == lt)
                                K = sum(1 for m in pm if m == rt)
                                if J >= 1 and K >= 1:
                                    found += 1
                                    # Analyze the walk
                                    print(f"\n  MIXED PHASE ¬EC #{found}:")
                                    print(f"    CL={CL}, t={t}, lt={lt}, rt={rt}")
                                    print(f"    J={J}, K={K}, phase_len={len(pm)}")
                                    print(f"    phase movers: {pm}")
                                    print(f"    full cycle movers: {list(cycle_movers)}")

                                    # Check adjacency in phase
                                    adj_pairs = []
                                    nonadj_pairs = []
                                    for i in range(len(pm)-1):
                                        d = ring_dist(pm[i], pm[i+1], n)
                                        if d > 1:
                                            nonadj_pairs.append((i, pm[i], pm[i+1], d))
                                        else:
                                            adj_pairs.append((i, pm[i], pm[i+1]))
                                    print(f"    all phase pairs adjacent: {len(nonadj_pairs) == 0}")
                                    if nonadj_pairs:
                                        print(f"    NON-ADJ pairs: {nonadj_pairs}")

                                    # Check which procs fire in phase
                                    from collections import Counter
                                    fire_counts = Counter(pm)
                                    print(f"    fire counts in phase: {dict(fire_counts)}")

                                    # Is it a straight arc or backtracking?
                                    positions = []
                                    for m in pm:
                                        # Position on ring\{t} path
                                        d = (m - lt) % n
                                        if d == 0:
                                            positions.append(0)
                                        else:
                                            positions.append((lt - m) % n)
                                    print(f"    path positions: {positions}")

                                    if found >= 5:
                                        break
                            if found >= 5:
                                break
                break
            history.append(config)
            history_movers.append(p)
            config_to_step[config] = step + 1

        if found >= 5:
            break
    if found >= 5:
        break

if found == 0:
    print("\nNo mixed phase ¬EC cycles found!")
