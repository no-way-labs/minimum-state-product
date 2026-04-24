#!/usr/bin/env python3
"""Key question: In good cycles WITHOUT entry conflict, are all
consecutive movers ring-adjacent? If yes, then gap1_ec never fires
under ¬EC, and the non-adjacent pair approach is a dead end.

Also check: do ¬EC cycles have mixed phases?"""
import random
from itertools import product as iterproduct

random.seed(42)

def ring_dist(a, b, n):
    return min((a - b) % n, (b - a) % n)

def has_entry_conflict(configs, movers, sys_f, n, ms):
    """Check if the good cycle has an entry conflict at any processor."""
    CL = len(configs)
    for p in range(n):
        # Collect boundary triples at mover steps and non-mover steps
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
        # EC if any mover triple matches a non-mover triple
        if mover_triples & nonmover_triples:
            return True
    return False

def find_cycles_with_ec_check(n, ms, num_trials=500000):
    """Find good cycles and check EC status."""
    results = {'ec': [], 'noec': []}

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
                    ec = has_entry_conflict(cycle_configs, cycle_movers, sys_f, n, ms)
                    key = 'ec' if ec else 'noec'
                    if len(results[key]) < 5000:
                        results[key].append((cycle_configs, cycle_movers))
                break
            history.append(config)
            history_movers.append(p)
            config_to_step[config] = step + 1

    return results

# Check n=9
print("=" * 60)
print("n=9 ms=[2,2,2,3,3,3,3,3,3]")
n, ms = 9, [2,2,2,3,3,3,3,3,3]
results = find_cycles_with_ec_check(n, ms, 500000)
print(f"  Cycles with EC: {len(results['ec'])}")
print(f"  Cycles without EC: {len(results['noec'])}")

# For ¬EC cycles: check if all consecutive movers are ring-adjacent
noec_all_adj = 0
noec_has_nonadj = 0
noec_mixed_phases = 0
for configs, movers in results['noec']:
    CL = len(movers)
    all_adj = all(ring_dist(movers[k], movers[(k+1) % CL], n) <= 1 for k in range(CL))
    if all_adj:
        noec_all_adj += 1
    else:
        noec_has_nonadj += 1

    # Check for mixed phases
    for t in range(n):
        lt, rt = (t-1)%n, (t+1)%n
        fires = [k for k in range(CL) if movers[k] == t]
        F = len(fires)
        if F < 1:
            continue
        for idx in range(F):
            s = fires[idx]
            prev = fires[(idx-1) % F]
            if prev < s:
                pm = movers[prev+1:s]
            else:
                pm = movers[prev+1:] + movers[:s]
            J = sum(1 for m in pm if m == lt)
            K = sum(1 for m in pm if m == rt)
            if J >= 1 and K >= 1:
                noec_mixed_phases += 1

print(f"\n  ¬EC cycles with ALL adjacent movers: {noec_all_adj}")
print(f"  ¬EC cycles with some non-adjacent: {noec_has_nonadj}")
print(f"  ¬EC cycles with mixed phases: {noec_mixed_phases}")

# For EC cycles: how many have non-adjacent pairs?
ec_has_nonadj = 0
for configs, movers in results['ec']:
    CL = len(movers)
    has_nonadj = any(ring_dist(movers[k], movers[(k+1) % CL], n) > 1 for k in range(CL))
    if has_nonadj:
        ec_has_nonadj += 1
print(f"\n  EC cycles with non-adjacent pairs: {ec_has_nonadj} / {len(results['ec'])}")

# Check n=5 too
print("\n" + "=" * 60)
print("n=5 ms=[2,2,3,2,3]")
n, ms = 5, [2,2,3,2,3]
results5 = find_cycles_with_ec_check(n, ms, 300000)
print(f"  Cycles with EC: {len(results5['ec'])}")
print(f"  Cycles without EC: {len(results5['noec'])}")

noec5_mixed = 0
noec5_all_adj = 0
for configs, movers in results5['noec']:
    CL = len(movers)
    all_adj = all(ring_dist(movers[k], movers[(k+1) % CL], n) <= 1 for k in range(CL))
    if all_adj:
        noec5_all_adj += 1
    for t in range(n):
        lt, rt = (t-1)%n, (t+1)%n
        fires = [k for k in range(CL) if movers[k] == t]
        F = len(fires)
        if F < 1:
            continue
        for idx in range(F):
            s = fires[idx]
            prev = fires[(idx-1) % F]
            if prev < s:
                pm = movers[prev+1:s]
            else:
                pm = movers[prev+1:] + movers[:s]
            J = sum(1 for m in pm if m == lt)
            K = sum(1 for m in pm if m == rt)
            if J >= 1 and K >= 1:
                noec5_mixed += 1

print(f"  ¬EC all-adjacent: {noec5_all_adj} / {len(results5['noec'])}")
print(f"  ¬EC mixed phases: {noec5_mixed}")
