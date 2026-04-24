#!/usr/bin/env python3
"""Do sub-threshold systems with ≥3 binary ever have non-zero winding?
If not: sweep/odd-winding paths are vacuously empty."""
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

def step_dir(movers, n, k):
    """CW = +1, CCW = -1, stay = 0."""
    L = len(movers)
    cur = movers[k]
    nxt = movers[(k+1) % L]
    if (cur + 1) % n == nxt:
        return 1  # CW
    elif (nxt + 1) % n == cur:
        return -1  # CCW
    else:
        return 0  # stay or jump

def total_displacement(movers, n):
    return sum(step_dir(movers, n, k) for k in range(len(movers)))

def main():
    random.seed(42)

    for n, ms in [(5, [2,2,2,3,3]), (7, [2,2,2,3,3,3,3]),
                  (9, [2,2,2,3,3,3,3,3,3])]:
        zw = 0
        nzw = 0
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
                        td = total_displacement(cycle, n)
                        if td == 0:
                            zw += 1
                        else:
                            nzw += 1
                            if nzw <= 3:
                                print(f"  NZW! n={n} td={td} L={len(cycle)}")
                    break
                visited[config] = step
                p = find_unique_privileged(config, sys_f, ms, n)
                if p is None: break
                config = apply_move(config, sys_f, ms, n, p)

        print(f"n={n} ms={ms}: {total} cycles, {zw} zero-winding, {nzw} non-zero-winding")

if __name__ == '__main__':
    main()
