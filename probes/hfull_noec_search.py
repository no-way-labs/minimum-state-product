#!/usr/bin/env python3
"""Exhaustive search: can hfull + ¬EC coexist at n=9 (or n>=9)?

hfull: every processor fires at least once in the good cycle.
¬EC: no entry conflict at any processor.

Under ¬EC, gap1_ec says consecutive movers must be ring-adjacent.
So movers form a ring-adjacent walk. For hfull, this walk must visit
every processor. We search for such cycles.

Approach:
1. Random system + random daemon: find good cycles, check EC + hfull.
2. Targeted: generate ring-adjacent mover walks that cover all procs,
   then try to build configs consistent with ¬EC.
"""
import random
from itertools import product as iterproduct
from collections import Counter

random.seed(42)

def ring_dist(a, b, n):
    return min((a - b) % n, (b - a) % n)

def has_entry_conflict(configs, movers, n):
    """Check EC at any processor."""
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

def is_ring_adjacent_walk(movers, n):
    """Check all consecutive movers are ring-adjacent."""
    CL = len(movers)
    for k in range(CL):
        if ring_dist(movers[k], movers[(k+1)%CL], n) > 1:
            return False
    return True

def fire_counts(movers, n):
    fc = [0]*n
    for m in movers:
        fc[m] += 1
    return fc

def search_random(n, ms, num_trials=500000, max_steps=3000):
    """Random system + random daemon search."""
    noec_count = 0
    noec_hfull = 0
    noec_stats = []  # (CL, fc, adj)

    for trial in range(num_trials):
        # Random transition function
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

        for step in range(max_steps):
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

                ec = has_entry_conflict(cycle_configs, cycle_movers, n)
                if not ec:
                    noec_count += 1
                    fc = fire_counts(cycle_movers, n)
                    hfull = all(f > 0 for f in fc)
                    adj = is_ring_adjacent_walk(cycle_movers, n)
                    noec_stats.append((CL, fc, adj, hfull))
                    if hfull:
                        noec_hfull += 1
                break

            config_to_step[config] = step + 1
            history.append(config)
            history_movers.append(p)

    return noec_count, noec_hfull, noec_stats

def main():
    for n in [5, 7, 9]:
        if n == 5:
            ms_list = [[2,3,2,3,2]]
        elif n == 7:
            ms_list = [[2,3,2,3,2,3,3]]
        else:
            ms_list = [
                [2,3,2,3,2,3,3,3,3],
                [2,3,2,3,3,2,3,3,3],
            ]

        for ms in ms_list:
            print(f"\n{'='*60}")
            print(f"n={n}, ms={ms}, product={eval('*'.join(str(x) for x in ms))}")
            print(f"Threshold = 4*3^{n-2} = {4*3**(n-2)}")
            print(f"Sub-threshold: {eval('*'.join(str(x) for x in ms)) < 4*3**(n-2)}")
            print(f"{'='*60}")

            noec, noec_hfull, stats = search_random(n, ms, num_trials=200000 if n <= 7 else 300000)
            print(f"¬EC cycles found: {noec}")
            print(f"¬EC + hfull cycles: {noec_hfull}")

            if stats:
                # Analyze
                cl_dist = Counter(s[0] for s in stats)
                adj_count = sum(1 for s in stats if s[2])
                print(f"Ring-adjacent walk: {adj_count}/{len(stats)} ({100*adj_count/len(stats):.1f}%)")
                print(f"CL distribution: {dict(sorted(cl_dist.items())[:10])}")

                # Fire count analysis
                max_procs = max(sum(1 for f in s[1] if f > 0) for s in stats)
                min_procs = min(sum(1 for f in s[1] if f > 0) for s in stats)
                avg_procs = sum(sum(1 for f in s[1] if f > 0) for s in stats) / len(stats)
                print(f"Procs that fire: min={min_procs}, max={max_procs}, avg={avg_procs:.1f}")

                # Show some examples
                for s in stats[:5]:
                    cl, fc, adj, hf = s
                    active = [i for i in range(n) if fc[i] > 0]
                    print(f"  CL={cl}, fc={fc}, active={active}, adj={adj}, hfull={hf}")

if __name__ == '__main__':
    main()
