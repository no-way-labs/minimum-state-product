#!/usr/bin/env python3
"""Does hno_safe EVER hold for systems with ≥3 binary?
Test with many configurations and MUCH larger search."""
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

def find_all_good_cycles(sys_f, ms, n, max_steps=10000):
    """Find good cycles from multiple starting configs."""
    cycles = []
    for _ in range(20):
        config = tuple(random.randint(0, ms[i]-1) for i in range(n))
        visited = {}
        for step in range(max_steps):
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
                if valid and cycle:
                    movers = tuple(cycle)
                    if movers not in [tuple(c) for c in cycles]:
                        cycles.append(cycle)
                break
            visited[config] = step
            p = find_unique_privileged(config, sys_f, ms, n)
            if p is None: break
            config = apply_move(config, sys_f, ms, n, p)
    return cycles

def check_hno_safe(movers, n):
    for q in range(n):
        visited = any(m == q or m == (q-1)%n or m == (q+1)%n for m in movers)
        if not visited:
            return False
    return True

def main():
    random.seed(12345)

    configs = [
        (5, [2,2,2,3,3]),
        (5, [2,2,2,3,4]),
        (5, [2,3,2,3,3]),
        (7, [2,2,2,3,3,3,3]),
        (9, [2,2,2,3,3,3,3,3,3]),
        # Also try with known valid systems — Sol3 has ms=(3,3,...,3)
        # but that has 0 binary. Try ms=(2,3,...,3) which has 1 binary.
        # With ≥3 binary: need ms with ≥3 twos.
    ]

    for n, ms in configs:
        nosafe_count = 0
        total_cycles = 0

        for trial in range(500000):
            sys_f = {}
            for i in range(n):
                sys_f[i] = random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n])

            cycles = find_all_good_cycles(sys_f, ms, n, max_steps=3000)
            for cycle in cycles:
                total_cycles += 1
                if check_hno_safe(cycle, n):
                    nosafe_count += 1
                    if nosafe_count <= 3:
                        L = len(cycle)
                        fc = [0]*n
                        for m in cycle:
                            fc[m] += 1
                        print(f"  hno_safe! n={n} ms={ms} L={L}")
                        print(f"    fire counts: {fc}")
                        print(f"    distinct movers: {sorted(set(cycle))}")

        print(f"n={n} ms={ms}: {total_cycles} cycles, {nosafe_count} with hno_safe")

    # The key question: does hno_safe REQUIRE that the mover visits
    # every proc's {q, left(q), right(q)} neighborhood?
    # With n procs and 3-neighborhoods: need at least ceil(n/3) distinct movers.
    # For n=9: need ≥ 3 distinct movers.
    # For n=5: need ≥ 2 distinct movers.
    # With ≥3 binary: the binary procs might suffice if spaced right.

    print("\n=== Analysis ===")
    print("If hno_safe NEVER holds with ≥3 binary + sub-threshold:")
    print("Then binary_ring_impossibility is trivially true (no such cycle exists).")
    print("But we need to prove this in Lean, not just observe it computationally.")

if __name__ == '__main__':
    main()
