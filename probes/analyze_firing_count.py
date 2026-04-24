#!/usr/bin/env python3
"""How many procs fire in sub-threshold cycles with ≥3 binary?
If few enough fire, pigeonhole gives 3 consecutive non-firing → safe proc."""
import random

def random_transition(m_left, m_self, m_right):
    f = {}
    for L in range(m_left):
        for S in range(m_self):
            for R in range(m_right):
                f[(L, S, R)] = random.randint(0, m_self - 1)
    return f

def privileged(config, sys_f, ms, n, i):
    return sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])] != config[i]

def find_unique_privileged(config, sys_f, ms, n):
    privs = [i for i in range(n) if privileged(config, sys_f, ms, n, i)]
    return privs[0] if len(privs) == 1 else None

def apply_move(config, sys_f, ms, n, i):
    nc = list(config)
    nc[i] = sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])]
    return tuple(nc)

def main():
    random.seed(42)

    for n, ms in [(5, [2,2,2,3,3]), (7, [2,2,2,3,3,3,3]),
                  (9, [2,2,2,3,3,3,3,3,3]),
                  (5, [2,2,2,3,4]),
                  (9, [2,3,2,3,3,3,3,3,3])]:
        firing_counts = []
        max_firing = 0
        total = 0

        for trial in range(500000 if n <= 7 else 100000):
            sys_f = {i: random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n]) for i in range(n)}
            config = tuple(random.randint(0, ms[i]-1) for i in range(n))
            visited = {}
            for step in range(3000):
                if config in visited:
                    start = visited[config]
                    cycle = []
                    c = config
                    ok = True
                    for _ in range(step - start):
                        p = find_unique_privileged(c, sys_f, ms, n)
                        if p is None: ok = False; break
                        cycle.append(p)
                        c = apply_move(c, sys_f, ms, n, p)
                    if ok and cycle:
                        total += 1
                        movers = cycle
                        fc = [0]*n
                        for m in movers:
                            fc[m] += 1
                        k = sum(1 for f in fc if f > 0)
                        firing_counts.append(k)
                        max_firing = max(max_firing, k)
                    break
                visited[config] = step
                p = find_unique_privileged(config, sys_f, ms, n)
                if p is None: break
                config = apply_move(config, sys_f, ms, n, p)

        if firing_counts:
            avg = sum(firing_counts) / len(firing_counts)
            # For pigeonhole: need n-k > 2(n-1)/3 for guaranteed 3 consecutive
            # Equivalently: k < n/3 + 2/3 ≈ n/3
            threshold = n / 3
            below_threshold = sum(1 for k in firing_counts if k < threshold)

            print(f"n={n} ms={ms} ({total} cycles):")
            print(f"  firing procs: min={min(firing_counts)} max={max_firing} avg={avg:.1f}")
            print(f"  threshold for pigeonhole (n/3): {threshold:.1f}")
            print(f"  below threshold: {below_threshold}/{total} ({below_threshold*100//total}%)")
            print(f"  distribution: {dict(sorted(((k, firing_counts.count(k)) for k in set(firing_counts))))}")
            print()

if __name__ == '__main__':
    main()
