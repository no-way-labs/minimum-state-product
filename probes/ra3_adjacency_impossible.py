#!/usr/bin/env python3
"""
Check: At n ≥ 7, do ALL good cycles (regardless of EC) have non-adjacent pairs?
If yes: gap1_ec fires on every cycle, giving EC on every cycle.
This would mean ¬EC is impossible at n ≥ 7, which is a MUCH simpler proof.

Alternatively: maybe all-adjacent cycles exist but always have EC.
Let's check both.
"""
import random
from collections import defaultdict

random.seed(42)

def check_all_adjacent(n, ms, num_trials=5000000):
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

        for step in range(5000):
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

                    if all_adj:
                        stats['all_adj'] += 1
                    else:
                        stats['has_nonadj'] += 1

                break
            history.append(config)
            history_movers.append(p)
            config_to_step[config] = step + 1

    return stats


def main():
    configs = [
        # n, ms, description
        (5, [2, 3, 2, 3, 3], "2 binary"),
        (5, [2, 3, 2, 2, 3], "3 binary"),
        (6, [2, 3, 2, 3, 3, 3], "2 binary"),
        (6, [2, 3, 2, 3, 2, 3], "3 binary"),
        (7, [2, 3, 2, 3, 3, 3, 3], "2 binary"),
        (7, [2, 3, 2, 3, 2, 3, 3], "3 binary"),
        (9, [2, 3, 2, 3, 3, 3, 3, 3, 3], "2 binary"),
        (9, [2, 3, 2, 3, 2, 3, 3, 3, 3], "3 binary"),
    ]

    for n, ms, desc in configs:
        print(f"n={n}, ms={ms} ({desc})")
        stats = check_all_adjacent(n, ms, num_trials=2000000)
        total = stats.get('cycles', 0)
        adj = stats.get('all_adj', 0)
        nonadj = stats.get('has_nonadj', 0)
        pct = adj / max(total, 1) * 100
        print(f"  Cycles: {total}, all-adj: {adj} ({pct:.2f}%), non-adj: {nonadj}")
        print()


if __name__ == '__main__':
    main()
