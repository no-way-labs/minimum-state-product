#!/usr/bin/env python3
"""Check: can the no-pivot hypothesis ever be satisfied?
No pivot = no proc with both binary neighbors fires.

If this NEVER happens (the hypothesis is always False), then
no_firing_both_binary_neighbors_false is vacuously true.
"""
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
    random.seed(999)

    configs = [
        (5, [2,2,2,3,3]),
        (5, [2,3,2,3,3]),
        (7, [2,2,2,3,3,3,3]),
        (7, [2,3,2,3,3,3,3]),
        (9, [2,2,2,3,3,3,3,3,3]),
        (9, [2,3,2,3,3,3,3,3,3]),
        (9, [2,3,3,2,3,3,2,3,3]),  # 3 spaced binary (Gap B)
        (9, [2,2,3,3,3,2,3,3,3]),  # mixed
    ]

    for n, ms in configs:
        no_pivot_count = 0
        cycles_found = 0

        for trial in range(100000 if n <= 7 else 50000):
            sys_f = {}
            for i in range(n):
                sys_f[i] = random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n])

            config = tuple(random.randint(0, ms[i]-1) for i in range(n))
            visited = {}
            for step in range(3000):
                if config in visited:
                    start = visited[config]
                    cycle = []
                    c = config
                    valid = True
                    for _ in range(step - start):
                        p = find_unique_privileged(c, sys_f, ms, n)
                        if p is None: valid = False; break
                        cycle.append(p)
                        c = apply_move(c, sys_f, ms, n, p)
                    if not valid or not cycle: break

                    cycles_found += 1
                    L = len(cycle)
                    movers = cycle

                    # Check hno_safe
                    safe = False
                    for q in range(n):
                        visited_q = False
                        for m in movers:
                            if m == q or m == (q-1)%n or m == (q+1)%n:
                                visited_q = True; break
                        if not visited_q:
                            safe = True; break
                    if safe:
                        break  # Has safe proc, skip

                    # Check ≥3 binary
                    num_bin = sum(1 for m in ms if m == 2)
                    if num_bin < 3:
                        break

                    # Find fire counts
                    fc = [0] * n
                    for m in movers:
                        fc[m] += 1

                    # Check no-pivot: no proc with both binary neighbors fires
                    has_pivot = False
                    for t in range(n):
                        if ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2 and fc[t] > 0:
                            has_pivot = True
                            break

                    if not has_pivot:
                        no_pivot_count += 1
                        if no_pivot_count <= 3:
                            # Print details
                            print(f"  NO PIVOT! n={n} ms={ms} L={L}")
                            for t in range(n):
                                if ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2:
                                    print(f"    pivot candidate t={t} m={ms[t]} fc={fc[t]}")

                    break
                visited[config] = step
                p = find_unique_privileged(config, sys_f, ms, n)
                if p is None: break
                config = apply_move(config, sys_f, ms, n, p)

        print(f"n={n} ms={ms}: {cycles_found} cycles, {no_pivot_count} no-pivot (with hno_safe)")

    print("\nIf no-pivot count is 0 everywhere: the hypothesis is contradictory!")
    print("Then no_firing_both_binary_neighbors_false is vacuously true (exfalso).")

if __name__ == '__main__':
    main()
