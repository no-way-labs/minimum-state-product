#!/usr/bin/env python3
"""Check: in every mixed phase (J>=1, K>=1) at ANY pivot t,
between the first L-fire and first R-fire, is there ALWAYS a
non-adjacent consecutive mover pair?

Good cycle = cycle of distinct configs where each step has exactly one
processor change (mover). We enumerate via random transition + random
daemon (not requiring unique privilege).

Also: does t ever fire inside its own phase?
"""
import random
from itertools import product as iterproduct

random.seed(42)

def ring_dist(a, b, n):
    return min((a - b) % n, (b - a) % n)

def find_good_cycles_daemon(ms, n, num_trials=300000):
    """Find good cycles via random daemon (any privileged proc can move)."""
    cycles_found = set()
    results = []
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
        visited = {}
        for step in range(1500):
            if config in visited:
                start = visited[config]
                cl = step - start
                c = config
                movers = []
                ok = True
                for s in range(cl):
                    c_next_list = list(c)
                    # Reconstruct: we stored the history, need to recover movers
                    # Actually we need to store history with movers
                    ok = False
                    break
                break
            visited[config] = step
            # Pick random privileged processor
            privs = [i for i in range(n)
                     if sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])] != config[i]]
            if not privs:
                break
            p = random.choice(privs)
            nc = list(config)
            nc[p] = sys_f[p][(config[(p-1)%n], config[p], config[(p+1)%n])]
            config = tuple(nc)

    # Better approach: store history with movers
    cycles_found = set()
    results = []
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

        for step in range(1500):
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
                cycle_movers = history_movers[cs:]
                cycle_movers.append(p)  # the move that brought us back

                # Wait, step cs..step: movers at indices cs..step
                # history_movers[cs] = mover from history[cs] to history[cs+1]
                # The last mover (p) goes from history[step] to config = history[cs]
                # So cycle movers = history_movers[cs:] + [p]
                # But history_movers has len = step (0-indexed moves)
                cycle_movers_full = history_movers[cs:] + [p]
                CL = len(cycle_configs)

                if CL == len(cycle_movers_full) and CL >= n:
                    mkey = tuple(cycle_movers_full)
                    if mkey not in cycles_found:
                        cycles_found.add(mkey)
                        results.append(cycle_movers_full)
                break

            history.append(config)
            history_movers.append(p)
            config_to_step[config] = step + 1

    return results


def analyze_phases(movers, n):
    CL = len(movers)
    total_mixed = 0
    has_nonadj_count = 0
    counterexamples = []
    t_in_interior_count = 0
    total_phases = 0

    for t in range(n):
        lt, rt = (t-1) % n, (t+1) % n
        fires = [k for k in range(CL) if movers[k] == t]
        F = len(fires)
        if F < 1:
            continue

        for idx in range(F):
            s = fires[idx]
            prev = fires[(idx - 1) % F]
            if F == 1:
                if prev < s:
                    pm = movers[prev+1:s]
                else:
                    pm = movers[prev+1:] + movers[:s]
            else:
                if prev < s:
                    pm = movers[prev+1:s]
                else:
                    pm = movers[prev+1:] + movers[:s]

            total_phases += 1
            J = sum(1 for m in pm if m == lt)
            K = sum(1 for m in pm if m == rt)
            if J < 1 or K < 1:
                continue

            total_mixed += 1

            if t in pm:
                t_in_interior_count += 1

            first_L = next(i for i, m in enumerate(pm) if m == lt)
            first_R = next(i for i, m in enumerate(pm) if m == rt)

            if first_L < first_R:
                seg = pm[first_L:first_R+1]
            else:
                seg = pm[first_R:first_L+1]

            has_nonadj = any(ring_dist(seg[i], seg[i+1], n) > 1
                           for i in range(len(seg) - 1))

            if has_nonadj:
                has_nonadj_count += 1
            else:
                counterexamples.append({
                    't': t, 'lt': lt, 'rt': rt, 'J': J, 'K': K,
                    'seg': seg, 'pm': pm, 'CL': CL
                })

    return total_phases, total_mixed, has_nonadj_count, counterexamples, t_in_interior_count


test_cases = [
    (5, [2, 2, 3, 2, 3]),
    (5, [2, 2, 2, 3, 3]),
    (5, [3, 2, 2, 3, 2]),
    (7, [2, 2, 3, 2, 3, 3, 3]),
    (7, [3, 2, 2, 3, 2, 2, 3]),
    (7, [2, 2, 2, 3, 3, 3, 3]),
    (9, [2, 2, 2, 3, 3, 3, 3, 3, 3]),
    (9, [3, 3, 2, 2, 3, 2, 2, 3, 3]),
]

grand_phases = 0
grand_mixed = 0
grand_nonadj = 0
grand_cex = []
grand_tint = 0

for n, ms in test_cases:
    trials = 500000 if n <= 5 else (300000 if n <= 7 else 200000)
    print(f"n={n} ms={ms} ... ", end="", flush=True)
    cycles = find_good_cycles_daemon(ms, n, trials)
    tp = tm = tn = ti = 0
    cex_local = []
    for movers in cycles:
        a, b, c, d, e = analyze_phases(movers, n)
        tp += a; tm += b; tn += c; cex_local.extend(d); ti += e
    pct = tn * 100 // max(tm, 1)
    print(f"cycles={len(cycles)}, phases={tp}, mixed={tm}, nonadj={tn} ({pct}%), t_int={ti}, cex={len(cex_local)}")
    grand_phases += tp; grand_mixed += tm; grand_nonadj += tn
    grand_cex.extend(cex_local[:5]); grand_tint += ti

print(f"\nGRAND: phases={grand_phases}, mixed={grand_mixed}, nonadj={grand_nonadj}, t_int={grand_tint}")
print(f"Counterexamples: {len(grand_cex)}")

if grand_mixed == 0:
    print("\nNO MIXED PHASES FOUND AT ALL!")
    print("Mixed phases may not exist in good cycles with these multisets.")
    print("The claim is VACUOUSLY TRUE.")
elif grand_cex:
    print("\nCOUNTEREXAMPLES (claim FALSE):")
    for cx in grand_cex[:10]:
        n_local = cx['CL']  # approximate
        print(f"  t={cx['t']} lt={cx['lt']} rt={cx['rt']} J={cx['J']} K={cx['K']}")
        print(f"  segment: {cx['seg']}")
        print(f"  phase: {cx['pm']}")
else:
    print(f"\nCONFIRMED: all {grand_mixed} mixed phases have non-adjacent pair.")
