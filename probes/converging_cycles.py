#!/usr/bin/env python3
"""What do good cycles of CONVERGING sub-threshold systems look like?

Key question: small_arc_contradicts_convergence proves safe proc → False
for converging systems. So converging systems have NO safe proc.
What's the structure of their good cycles?

We need to find actual converging systems and examine their cycles.
"""
import random
from itertools import product as iterproduct


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


def total_displacement(movers, n):
    td = 0
    L = len(movers)
    for i in range(L):
        curr = movers[i]
        nxt = movers[(i+1) % L]
        diff = (nxt - curr) % n
        if diff == 1: td += 1
        elif diff == n-1: td -= 1
    return td


def has_safe_proc(movers, n):
    fc = [0] * n
    for m in movers:
        fc[m] += 1
    for q in range(n):
        if fc[q] == 0 and fc[(q-1)%n] == 0 and fc[(q+1)%n] == 0:
            return True
    return False


def find_cycle_and_configs(sys_f, ms, n, start_config, max_steps=5000):
    """Returns (movers, cycle_configs) or None."""
    visited = {}
    c = start_config
    for step in range(max_steps):
        if c in visited:
            start = visited[c]
            movers = []
            configs = []
            cc = c
            ok = True
            for _ in range(step - start):
                p = find_unique_privileged(cc, sys_f, ms, n)
                if p is None:
                    ok = False
                    break
                movers.append(p)
                configs.append(cc)
                cc = apply_move(cc, sys_f, ms, n, p)
            if ok and movers:
                return movers, configs
            return None
        visited[c] = step
        p = find_unique_privileged(c, sys_f, ms, n)
        if p is None:
            return None
        c = apply_move(c, sys_f, ms, n, p)
    return None


def check_convergence(sys_f, ms, n, gc_set):
    """Check ALL configs converge to the good cycle."""
    for vals in iterproduct(*[range(m) for m in ms]):
        c = vals
        product_val = 1
        for m in ms:
            product_val *= m
        seen = set()
        reached = False
        for _ in range(product_val + 10):
            if c in gc_set:
                reached = True
                break
            if c in seen:
                break
            seen.add(c)
            p = find_unique_privileged(c, sys_f, ms, n)
            if p is None:
                break
            c = apply_move(c, sys_f, ms, n, p)
        if not reached:
            return False
    return True


def main():
    random.seed(42)

    test_configs = [
        (5, [2, 2, 2, 3, 3]),
        (5, [2, 2, 2, 3, 4]),
        (7, [2, 3, 2, 3, 2, 3, 3]),
        (7, [2, 2, 2, 3, 3, 3, 3]),
    ]

    for n, ms in test_configs:
        product_val = 1
        for m in ms:
            product_val *= m
        threshold = 4 * (3 ** (n - 2))
        if product_val >= threshold:
            continue

        print(f"\nn={n} ms={ms} prod={product_val} threshold={threshold}")

        found = 0
        num_trials = 500000 if n <= 5 else 100000

        for trial in range(num_trials):
            sys_f = {i: random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n])
                     for i in range(n)}
            config = tuple(random.randint(0, ms[i]-1) for i in range(n))

            result = find_cycle_and_configs(sys_f, ms, n, config)
            if result is None:
                continue

            movers, configs = result
            gc_set = set(configs)

            # Check convergence (expensive!)
            conv = check_convergence(sys_f, ms, n, gc_set)
            if not conv:
                continue

            found += 1
            td = total_displacement(movers, n)
            fc = [0] * n
            for m in movers:
                fc[m] += 1
            k = sum(1 for f in fc if f > 0)
            z = n - k
            safe = has_safe_proc(movers, n)

            if found <= 10:
                print(f"  CONVERGING #{found}: L={len(movers)} td={td} k={k} |Z|={z} safe={safe}")
                print(f"    movers={movers[:20]} fc={fc}")

                # What type of mover word?
                binary_pos = [i for i in range(n) if ms[i] == 2]
                binary_fire = {b: fc[b] for b in binary_pos}
                print(f"    binary fire counts: {binary_fire}")

            if found >= 20:
                break

        print(f"  Total converging systems found: {found}")


if __name__ == '__main__':
    main()
