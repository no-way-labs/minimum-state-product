#!/usr/bin/env python3
"""Diagnostic: WHERE is the non-adjacent pair in mixed phases with large gaps?"""
import random

random.seed(42)

def ring_dist(a, b, n):
    return min((a - b) % n, (b - a) % n)

def check_mixed_phases_detailed(n, ms, num_trials=500000):
    large_gap_count = 0
    nonadj_in_seg = 0  # non-adj between fL and fR
    nonadj_outside = 0  # non-adj elsewhere in phase
    examples = []

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
        history_movers = []
        config_to_step = {config: 0}
        history = [config]

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
                    for t in range(n):
                        lt, rt = (t-1)%n, (t+1)%n
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
                            if J < 1 or K < 1:
                                continue

                            first_L = next(i for i, m in enumerate(pm) if m == lt)
                            first_R = next(i for i, m in enumerate(pm) if m == rt)

                            if first_L < first_R:
                                seg = pm[first_L:first_R+1]
                            else:
                                seg = pm[first_R:first_L+1]

                            gap = abs(first_R - first_L)
                            if gap < n-2:
                                continue

                            large_gap_count += 1

                            # Check non-adj in segment [fL, fR]
                            seg_nonadj = any(ring_dist(seg[i], seg[i+1], n) > 1
                                           for i in range(len(seg)-1))
                            # Check non-adj in whole phase
                            phase_nonadj = any(ring_dist(pm[i], pm[i+1], n) > 1
                                             for i in range(len(pm)-1))

                            if seg_nonadj:
                                nonadj_in_seg += 1
                            elif phase_nonadj:
                                nonadj_outside += 1

                            if len(examples) < 10:
                                # Find WHERE the non-adj pair is
                                nonadj_pos = None
                                for i in range(len(pm)-1):
                                    if ring_dist(pm[i], pm[i+1], n) > 1:
                                        nonadj_pos = i
                                        break
                                examples.append({
                                    't': t, 'lt': lt, 'rt': rt,
                                    'J': J, 'K': K, 'gap': gap,
                                    'first_L': first_L, 'first_R': first_R,
                                    'nonadj_pos': nonadj_pos,
                                    'seg_nonadj': seg_nonadj,
                                    'pm': pm[:30],
                                    'pm_len': len(pm)
                                })
                break
            history.append(config)
            history_movers.append(p)
            config_to_step[config] = step + 1

    return large_gap_count, nonadj_in_seg, nonadj_outside, examples

print("n=9: Mixed phases with gap >= n-2 = 7")
n, ms = 9, [2,2,2,3,3,3,3,3,3]
total, in_seg, outside, examples = check_mixed_phases_detailed(n, ms, 500000)
print(f"  Large-gap phases: {total}")
print(f"  Non-adj IN segment [fL,fR]: {in_seg}")
print(f"  Non-adj OUTSIDE segment: {outside}")
print(f"  Neither (BUG): {total - in_seg - outside}")
for ex in examples[:5]:
    print(f"  t={ex['t']} lt={ex['lt']} rt={ex['rt']} J={ex['J']} K={ex['K']} gap={ex['gap']} pm_len={ex['pm_len']}")
    print(f"    first_L={ex['first_L']} first_R={ex['first_R']} nonadj_at={ex['nonadj_pos']} in_seg={ex['seg_nonadj']}")
    print(f"    movers: {ex['pm']}")
