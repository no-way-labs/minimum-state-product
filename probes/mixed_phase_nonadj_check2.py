#!/usr/bin/env python3
"""Refined check: mixed phase non-adjacency.

Q1: Unrestricted pivots -- claim is FALSE (confirmed above).
Q2: Restrict to sandwiched ternary pivot (ms[t]>=3, ms[lt]=ms[rt]=2) -- ?
Q3: Anatomy of counterexamples.
"""
import random

random.seed(42)

def ring_dist(a, b, n):
    return min((a - b) % n, (b - a) % n)

def find_good_cycles_daemon(ms, n, num_trials):
    results = []
    cycles_found = set()
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
            if not privs: break
            p = random.choice(privs)
            nc = list(config)
            nc[p] = sys_f[p][(config[(p-1)%n], config[p], config[(p+1)%n])]
            config = tuple(nc)
            if config in config_to_step:
                cs = config_to_step[config]
                cycle_movers = history_movers[cs:] + [p]
                CL = len(history) - cs
                if CL == len(cycle_movers) and CL >= n:
                    mkey = tuple(cycle_movers)
                    if mkey not in cycles_found:
                        cycles_found.add(mkey)
                        results.append(cycle_movers)
                break
            history.append(config)
            history_movers.append(p)
            config_to_step[config] = step + 1
    return results


def analyze(movers, ms, n, sandwiched_only):
    CL = len(movers)
    total_mixed = 0
    nonadj_count = 0
    cex = []

    for t in range(n):
        lt, rt = (t-1) % n, (t+1) % n
        if sandwiched_only:
            if ms[t] < 3 or ms[lt] != 2 or ms[rt] != 2:
                continue

        fires = [k for k in range(CL) if movers[k] == t]
        F = len(fires)
        if F < 1: continue

        for idx in range(F):
            s = fires[idx]
            prev = fires[(idx - 1) % F]
            if prev < s:
                pm = movers[prev+1:s]
            else:
                pm = movers[prev+1:] + movers[:s]

            J = sum(1 for m in pm if m == lt)
            K = sum(1 for m in pm if m == rt)
            if J < 1 or K < 1: continue
            total_mixed += 1

            first_L = next(i for i, m in enumerate(pm) if m == lt)
            first_R = next(i for i, m in enumerate(pm) if m == rt)
            if first_L < first_R:
                seg = pm[first_L:first_R+1]
            else:
                seg = pm[first_R:first_L+1]

            has_nonadj = any(ring_dist(seg[i], seg[i+1], n) > 1 for i in range(len(seg) - 1))
            if has_nonadj:
                nonadj_count += 1
            elif len(cex) < 5:
                cex.append({'t': t, 'lt': lt, 'rt': rt, 'J': J, 'K': K,
                           'seg': seg, 'pm': pm, 'n': n, 'ms': ms})

    return total_mixed, nonadj_count, cex


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

for sandwiched_only in [False, True]:
    label = "SANDWICHED TERNARY ONLY" if sandwiched_only else "ALL PIVOTS"
    print(f"\n{'='*60}")
    print(f"  {label}")
    print(f"{'='*60}")

    grand_mixed = grand_nonadj = 0
    grand_cex = []

    for n, ms in test_cases:
        trials = 500000 if n <= 5 else (300000 if n <= 7 else 200000)
        cycles = find_good_cycles_daemon(ms, n, trials)
        tm = tn = 0
        cex_local = []
        for movers in cycles:
            a, b, c = analyze(movers, ms, n, sandwiched_only)
            tm += a; tn += b; cex_local.extend(c)

        pct = tn * 100 // max(tm, 1)
        fail = tm - tn
        print(f"n={n} ms={ms}: cyc={len(cycles)}, mixed={tm}, nonadj={tn} ({pct}%), FAIL={fail}")
        grand_mixed += tm; grand_nonadj += tn
        grand_cex.extend(cex_local[:3])

    fail = grand_mixed - grand_nonadj
    pct = grand_nonadj * 100 // max(grand_mixed, 1)
    print(f"\nTOTAL: mixed={grand_mixed}, nonadj={grand_nonadj} ({pct}%), FAIL={fail}")
    if grand_cex:
        print(f"\nSample counterexamples:")
        for cx in grand_cex[:5]:
            dists = [ring_dist(cx['seg'][i], cx['seg'][i+1], cx['n']) for i in range(len(cx['seg'])-1)]
            print(f"  n={cx['n']} ms={cx['ms']} t={cx['t']} (lt={cx['lt']},rt={cx['rt']}) J={cx['J']} K={cx['K']}")
            print(f"    seg={cx['seg']}  dists={dists}")
            print(f"    phase={cx['pm']}")
    elif grand_mixed == 0:
        print("  No mixed phases found!")
    else:
        print("  CONFIRMED: claim holds.")
