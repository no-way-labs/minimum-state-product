#!/usr/bin/env python3
"""Think carefully: when does a safe proc exist with binary procs?

A safe proc q means: q, left(q), right(q) all have fc=0.
I.e., 3 consecutive non-firing procs.

Question: with ≥3 binary + sub-threshold + n≥9, do 3 consecutive
non-firing procs always exist?

Key constraint: binary procs fire 0 or ≥2 times (binary parity).
Sub-threshold: product < 4·3^(n-2).

Let me check: in the good cycles we CAN find (without hno_safe),
how many procs fire? Is there always a safe proc?
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

def has_safe_proc(movers, n):
    """Check if a safe proc exists (3 consecutive with fc=0)."""
    fc = [0] * n
    for m in movers:
        fc[m] += 1
    for q in range(n):
        if fc[q] == 0 and fc[(q-1)%n] == 0 and fc[(q+1)%n] == 0:
            return True, q
    return False, -1

def main():
    random.seed(42)

    for n, ms in [(5, [2,2,2,3,3]), (7, [2,2,2,3,3,3,3]),
                  (9, [2,2,2,3,3,3,3,3,3]), (9, [2,3,2,3,3,3,3,3,3]),
                  (5, [3,3,3,3,3]), (9, [3,3,3,3,3,3,3,3,3])]:  # Also 0 binary
        safe_count = 0
        no_safe_count = 0
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
                        safe, q = has_safe_proc(movers, n)
                        if safe:
                            safe_count += 1
                        else:
                            no_safe_count += 1
                            if no_safe_count <= 3:
                                fc = [0]*n
                                for m in movers:
                                    fc[m] += 1
                                print(f"  NO SAFE: n={n} ms={ms} L={len(movers)} fc={fc}")
                                print(f"    firing procs: {[i for i in range(n) if fc[i]>0]}")
                    break
                visited[config] = step
                p = find_unique_privileged(config, sys_f, ms, n)
                if p is None: break
                config = apply_move(config, sys_f, ms, n, p)

        num_bin = sum(1 for m in ms if m == 2)
        print(f"n={n} ms={ms} bin={num_bin}: {total} cycles, "
              f"{safe_count} safe ({safe_count*100//max(total,1)}%), "
              f"{no_safe_count} no-safe ({no_safe_count*100//max(total,1)}%)")

if __name__ == '__main__':
    main()
