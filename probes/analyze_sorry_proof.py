#!/usr/bin/env python3
"""Analyze what proof strategy can close binary_ring_impossibility.

The sorry has 6 hypotheses:
1. gc: GoodCycle
2. n >= 9
3. converges
4. hno_safe: no safe processor (every neighborhood visited by mover)
5. subThreshold: product < 4 * 3^(n-2)
6. h3bin: >= 3 binary procs

We need to show these are jointly impossible.

Two callers:
A) both_binary_neighbors_false: t exists with m(lt)=2, m(rt)=2, fc(t)>=2, fc(t)<L,
   and SOME phase has no mechanism (normal form)
B) no_firing_both_binary_neighbors_false: no t with both binary neighbors fires

Strategy: Test which SUBSET of hypotheses is already contradictory.
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

def find_good_cycle(sys_f, ms, n, start_config, max_steps=10000):
    config = start_config
    visited = {}
    for step in range(max_steps):
        if config in visited:
            start = visited[config]
            cycle_configs = []
            movers = []
            c = config
            for _ in range(step - start):
                p = find_unique_privileged(c, sys_f, ms, n)
                if p is None: return None, None
                movers.append(p)
                cycle_configs.append(c)
                c = apply_move(c, sys_f, ms, n, p)
            return cycle_configs, movers
        visited[config] = step
        p = find_unique_privileged(config, sys_f, ms, n)
        if p is None: return None, None
        config = apply_move(config, sys_f, ms, n, p)
    return None, None

def check_hno_safe(movers, n):
    """Check if hno_safe holds (no safe processor)."""
    for q in range(n):
        # q is safe if mover never visits {q, left(q), right(q)}
        visited = any(m == q or m == (q-1)%n or m == (q+1)%n for m in movers)
        if not visited:
            return False  # q is safe, so hno_safe is False
    return True  # no safe processor, hno_safe holds

def check_converges(sys_f, ms, n, good_configs):
    """Quick convergence check: from random non-good configs, do we reach good cycle?"""
    good_set = set(good_configs)
    for _ in range(100):
        config = tuple(random.randint(0, ms[i]-1) for i in range(n))
        if config in good_set:
            continue
        for _ in range(1000):
            p = find_unique_privileged(config, sys_f, ms, n)
            if p is None:
                # Multi-privileged: try all
                privs = [i for i in range(n) if privileged(config, sys_f, ms, n, i)]
                if not privs:
                    break
                p = random.choice(privs)
            config = apply_move(config, sys_f, ms, n, p)
            if config in good_set:
                break
        else:
            return False
    return True

def main():
    random.seed(42)

    # Test various multisets with >= 3 binary
    test_configs = [
        (9, [2,2,2,3,3,3,3,3,3]),  # 3 consec binary, rest ternary
        (9, [2,3,2,3,2,3,3,3,3]),  # 3 non-consec binary
        (9, [2,2,2,2,3,3,3,3,3]),  # 4 binary
        (9, [2,3,3,2,3,3,2,3,3]),  # 3 binary, evenly spaced
    ]

    total_hno_safe = 0
    total_cycles = 0
    total_hno_safe_no_conv = 0  # hno_safe without convergence check

    for n, ms in test_configs:
        prod = 1
        for m in ms:
            prod *= m
        threshold = 4 * 3**(n-2)
        is_sub = prod < threshold
        binary_count = sum(1 for m in ms if m == 2)

        print(f"\nn={n} ms={ms} product={prod} threshold={threshold} sub={is_sub} binary={binary_count}")

        hno_safe_count = 0
        cycle_count = 0
        hno_safe_conv = 0

        for trial in range(100000):
            sys_f = {}
            for i in range(n):
                sys_f[i] = random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n])

            # Try a few starting configs
            for _ in range(3):
                start = tuple(random.randint(0, ms[i]-1) for i in range(n))
                configs, movers = find_good_cycle(sys_f, ms, n, start)
                if configs is None or not movers:
                    continue
                cycle_count += 1
                total_cycles += 1

                if check_hno_safe(movers, n):
                    hno_safe_count += 1
                    total_hno_safe_no_conv += 1

                    # Check convergence too
                    if check_converges(sys_f, ms, n, configs):
                        hno_safe_conv += 1
                        total_hno_safe += 1

                        fc = [0]*n
                        for m in movers:
                            fc[m] += 1
                        L = len(movers)
                        distinct_movers = sorted(set(movers))
                        print(f"  FOUND! L={L} fc={fc} movers={distinct_movers}")

                        # Check for pivot
                        has_pivot = False
                        for t in range(n):
                            if ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2 and fc[t] > 0:
                                has_pivot = True
                                break
                        print(f"    has_pivot={has_pivot}")

        print(f"  cycles={cycle_count} hno_safe={hno_safe_count} hno_safe+conv={hno_safe_conv}")

    print(f"\n=== TOTALS ===")
    print(f"Total cycles: {total_cycles}")
    print(f"hno_safe (no conv): {total_hno_safe_no_conv}")
    print(f"hno_safe + conv: {total_hno_safe}")

if __name__ == '__main__':
    main()
