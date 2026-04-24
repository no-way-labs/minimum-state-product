#!/usr/bin/env python3
"""
Exhaustive check at n=5: find ALL ¬EC all-adjacent good cycles,
then check for sorry-pattern mixed phases.
"""
import random
from itertools import product as iterproduct
from collections import defaultdict

def find_all_noec_alladj_cycles(n, ms, max_trials=10000000):
    """Exhaustive random search for ¬EC all-adjacent good cycles."""
    random.seed(42)
    results = []
    seen_cycles = set()
    stats = defaultdict(int)

    for trial in range(max_trials):
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

                    all_adj = all(
                        min((cycle_movers[k] - cycle_movers[(k+1)%CL]) % n,
                            (cycle_movers[(k+1)%CL] - cycle_movers[k]) % n) <= 1
                        for k in range(CL))
                    if not all_adj:
                        stats['nonadj'] += 1
                        break

                    has_ec = False
                    for p2 in range(n):
                        mt_set = set()
                        nmt_set = set()
                        for k in range(CL):
                            tr = (cycle_configs[k][(p2-1)%n], cycle_configs[k][p2], cycle_configs[k][(p2+1)%n])
                            if cycle_movers[k] == p2:
                                mt_set.add(tr)
                            else:
                                nmt_set.add(tr)
                        if mt_set & nmt_set:
                            has_ec = True
                            break
                    if has_ec:
                        stats['ec'] += 1
                        break

                    stats['noec'] += 1

                    # Normalize cycle for dedup
                    key = tuple(cycle_movers)
                    if key not in seen_cycles:
                        seen_cycles.add(key)
                        results.append((cycle_configs, cycle_movers, sys_f))

                break
            history.append(config)
            history_movers.append(p)
            config_to_step[config] = step + 1

    return stats, results


def analyze_phases(n, ms, configs, movers, t):
    """Analyze all phases at processor t."""
    lt = (t - 1) % n
    rt = (t + 1) % n
    llt = (t - 2) % n
    rrt = (t + 2) % n
    l3t = (t - 3) % n
    CL = len(configs)

    t_fires = [k for k in range(CL) if movers[k] == t]
    if len(t_fires) < 1:
        return []

    phase_info = []
    for idx in range(len(t_fires)):
        s = t_fires[idx]
        prev_t = t_fires[(idx-1) % len(t_fires)]
        a = (prev_t + 1) % CL

        phase = []
        k = a
        while k != s:
            phase.append((k, movers[k]))
            k = (k + 1) % CL

        J = sum(1 for _, m in phase if m == lt)
        K = sum(1 for _, m in phase if m == rt)
        procs = set(m for _, m in phase)

        # Detailed analysis for mixed phases
        info = {
            'a': a, 's': s, 'phase': phase,
            'J': J, 'K': K, 'procs': procs,
            'first_mover': movers[a] if phase else None,
        }

        if J >= 1 and K >= 1:
            info['type'] = 'mixed'
            # Check sorry structure
            fL = None
            fR = None
            for k, m in phase:
                if m == lt and fL is None:
                    fL = k
                if m == rt and fR is None:
                    fR = k
            info['fL'] = fL
            info['fR'] = fR

            # Check LL adjacent to fL
            if fL is not None:
                fL_prev = (fL - 1) % CL
                info['mover_before_fL'] = movers[fL_prev]
                info['llt_before_fL'] = movers[fL_prev] == llt

            if fR is not None:
                fR_prev = (fR - 1) % CL
                info['mover_before_fR'] = movers[fR_prev]
                info['rrt_before_fR'] = movers[fR_prev] == rrt

            # Full walk?
            info['is_fullwalk'] = len(procs) == n - 1 and t not in procs
        elif J >= 1:
            info['type'] = 'one-sided-L'
        elif K >= 1:
            info['type'] = 'one-sided-R'
        else:
            info['type'] = 'empty'

        phase_info.append(info)

    return phase_info


def main():
    n = 5
    ms = [2, 3, 2, 3, 3]

    print(f"n={n}, ms={ms}")
    print("Finding all ¬EC all-adjacent good cycles...")

    stats, results = find_all_noec_alladj_cycles(n, ms, max_trials=5000000)
    print(f"Stats: {dict(stats)}")
    print(f"Unique ¬EC all-adj cycles: {len(results)}")

    # Analyze ALL phases in ALL cycles
    sorry_count = 0
    mixed_count = 0
    for ci, (configs, movers, sys_f) in enumerate(results):
        CL = len(configs)
        for t in range(n):
            if ms[t] < 3:
                continue
            if ms[(t-1)%n] != 2 or ms[(t+1)%n] != 2:
                continue

            phases = analyze_phases(n, ms, configs, movers, t)
            for pi, info in enumerate(phases):
                if info['type'] == 'mixed':
                    mixed_count += 1
                    movers_in_phase = [m for _, m in info['phase']]
                    # Check sorry conditions
                    is_sorry = False
                    llt = (t-2)%n
                    rrt = (t+2)%n
                    l3t = (t-3)%n
                    r3t = (t+3)%n

                    if info.get('llt_before_fL'):
                        # Check if l3t fires before first LL
                        # Find first LL fire
                        fLL = None
                        for k, m in info['phase']:
                            if m == llt:
                                fLL = k
                                break
                        if fLL is not None:
                            # Check l3t in [a, fLL)
                            found_l3t = False
                            k = info['a']
                            while k != fLL:
                                if movers[k] == l3t:
                                    found_l3t = True
                                    break
                                k = (k + 1) % CL
                            if found_l3t:
                                is_sorry = True

                    if info.get('rrt_before_fR'):
                        fRR = None
                        for k, m in info['phase']:
                            if m == rrt:
                                fRR = k
                                break
                        if fRR is not None:
                            found_r3t = False
                            k = info['a']
                            while k != fRR:
                                if movers[k] == r3t:
                                    found_r3t = True
                                    break
                                k = (k + 1) % CL
                            if found_r3t:
                                is_sorry = True

                    if is_sorry:
                        sorry_count += 1
                        print(f"\n  SORRY case: cycle #{ci}, t={t}, phase {pi}")
                        print(f"    Phase movers: {movers_in_phase}")
                        print(f"    Full movers: {movers}")
                        print(f"    Info: {info}")

    print(f"\nTotal mixed phases in ¬EC cycles: {mixed_count}")
    print(f"Total sorry-pattern phases: {sorry_count}")


if __name__ == '__main__':
    main()
