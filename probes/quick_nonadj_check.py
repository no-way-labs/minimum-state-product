#!/usr/bin/env python3
"""Quick check: in mixed phases at n=9, is fR-fL always < n-2?
Also: does EVERY mixed phase have a non-adjacent consecutive pair?
Focus on n=9 only, with tight statistics."""
import random

random.seed(42)

def ring_dist(a, b, n):
    return min((a - b) % n, (b - a) % n)

def check_mixed_phases(n, ms, num_trials=500000):
    total_mixed = 0
    nonadj_count = 0
    gap_stats = []  # fR - fL values for mixed phases
    all_adj_examples = []

    for trial in range(num_trials):
        # Random transition functions
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
                cycle_movers = history_movers[cs:] + [p]
                CL = len(cycle_movers)

                if CL >= n:
                    # Analyze phases
                    for t in range(n):
                        lt, rt = (t-1) % n, (t+1) % n
                        fires = [k for k in range(CL) if cycle_movers[k] == t]
                        F = len(fires)
                        if F < 1:
                            continue
                        for idx in range(F):
                            s = fires[idx]
                            prev = fires[(idx - 1) % F]
                            if prev < s:
                                pm = cycle_movers[prev+1:s]
                            else:
                                pm = cycle_movers[prev+1:] + cycle_movers[:s]
                            J = sum(1 for m in pm if m == lt)
                            K = sum(1 for m in pm if m == rt)
                            if J < 1 or K < 1:
                                continue
                            total_mixed += 1

                            # Find first L and first R in phase movers
                            first_L = next(i for i, m in enumerate(pm) if m == lt)
                            first_R = next(i for i, m in enumerate(pm) if m == rt)
                            gap = abs(first_R - first_L)
                            gap_stats.append(gap)

                            # Check all consecutive pairs in phase for non-adjacent
                            has_nonadj = False
                            for i in range(len(pm) - 1):
                                if ring_dist(pm[i], pm[i+1], n) > 1:
                                    has_nonadj = True
                                    break
                            if has_nonadj:
                                nonadj_count += 1
                            else:
                                all_adj_examples.append({
                                    't': t, 'J': J, 'K': K,
                                    'gap': gap, 'pm_len': len(pm),
                                    'pm': pm[:20]
                                })
                break
            history.append(config)
            history_movers.append(p)
            config_to_step[config] = step + 1

    return total_mixed, nonadj_count, gap_stats, all_adj_examples

print("n=9 ms=[2,2,2,3,3,3,3,3,3]")
n, ms = 9, [2,2,2,3,3,3,3,3,3]
total, nonadj, gaps, adj_ex = check_mixed_phases(n, ms, 500000)
if gaps:
    print(f"  mixed phases: {total}, with non-adj pair: {nonadj} ({nonadj*100//max(total,1)}%)")
    print(f"  gap (fR-fL): min={min(gaps)}, max={max(gaps)}, mean={sum(gaps)/len(gaps):.1f}")
    print(f"  gaps < n-2={n-2}: {sum(1 for g in gaps if g < n-2)} / {len(gaps)}")
    print(f"  all-adjacent examples: {len(adj_ex)}")
    for ex in adj_ex[:5]:
        print(f"    t={ex['t']} J={ex['J']} K={ex['K']} gap={ex['gap']} len={ex['pm_len']} pm={ex['pm']}")
else:
    print(f"  NO MIXED PHASES FOUND (total tested: {total})")

# Also check n=7
print("\nn=7 ms=[2,2,3,2,3,3,3]")
n, ms = 7, [2,2,3,2,3,3,3]
total, nonadj, gaps, adj_ex = check_mixed_phases(n, ms, 300000)
if gaps:
    print(f"  mixed phases: {total}, with non-adj pair: {nonadj} ({nonadj*100//max(total,1)}%)")
    print(f"  gap (fR-fL): min={min(gaps)}, max={max(gaps)}, mean={sum(gaps)/len(gaps):.1f}")
    print(f"  gaps < n-2={n-2}: {sum(1 for g in gaps if g < n-2)} / {len(gaps)}")
    print(f"  all-adjacent examples: {len(adj_ex)}")
    for ex in adj_ex[:3]:
        print(f"    t={ex['t']} J={ex['J']} K={ex['K']} gap={ex['gap']} len={ex['pm_len']} pm={ex['pm']}")
else:
    print(f"  NO MIXED PHASES FOUND (total tested: {total})")
