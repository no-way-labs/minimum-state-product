#!/usr/bin/env python3
"""Test hno_safe with very large trial count to find if it's EVER possible
with >=3 binary at n=9."""
import random

def random_transition(m_left, m_self, m_right):
    f = {}
    for L in range(m_left):
        for S in range(m_self):
            for R in range(m_right):
                f[(L, S, R)] = random.randint(0, m_self - 1)
    return f

def find_good_cycle(sys_f, ms, n, start_config, max_steps=5000):
    config = start_config
    visited = {}
    for step in range(max_steps):
        if config in visited:
            start = visited[config]
            movers = []
            c = config
            for _ in range(step - start):
                privs = [i for i in range(n) if sys_f[i][(c[(i-1)%n], c[i], c[(i+1)%n])] != c[i]]
                if len(privs) != 1: return None
                movers.append(privs[0])
                nc = list(c)
                p = privs[0]
                nc[p] = sys_f[p][(c[(p-1)%n], c[p], c[(p+1)%n])]
                c = tuple(nc)
            return movers
        visited[config] = step
        privs = [i for i in range(n) if sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])] != config[i]]
        if len(privs) != 1: return None
        p = privs[0]
        nc = list(config)
        nc[p] = sys_f[p][(config[(p-1)%n], config[p], config[(p+1)%n])]
        config = tuple(nc)
    return None

def check_hno_safe(movers, n):
    for q in range(n):
        visited = any(m == q or m == (q-1)%n or m == (q+1)%n for m in movers)
        if not visited:
            return False
    return True

def test_small():
    """Test at n=5 with 3 binary where product is sub-threshold."""
    random.seed(42)
    n = 5
    # Product threshold: 4 * 3^3 = 108
    # ms = [2,2,2,3,3], product = 72 < 108 (sub-threshold)
    # ms = [2,2,2,3,4], product = 96 < 108 (sub-threshold, M_5=96)
    # ms = [2,2,2,3,5], product = 120 > 108 (NOT sub-threshold)

    for ms_list in [[2,2,2,3,3], [2,2,2,3,4], [2,2,2,4,4], [2,3,2,3,3]]:
        ms = ms_list
        prod = 1
        for m in ms: prod *= m
        threshold = 4 * 3**(n-2)
        is_sub = prod < threshold
        binary_count = sum(1 for m in ms if m == 2)

        hno_safe_count = 0
        cycle_count = 0
        for trial in range(1000000):
            sys_f = {}
            for i in range(n):
                sys_f[i] = random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n])
            start = tuple(random.randint(0, ms[i]-1) for i in range(n))
            movers = find_good_cycle(sys_f, ms, n, start)
            if movers is None: continue
            cycle_count += 1
            if check_hno_safe(movers, n):
                hno_safe_count += 1
                if hno_safe_count <= 5:
                    fc = [0]*n
                    for m in movers: fc[m] += 1
                    print(f"  hno_safe! ms={ms} L={len(movers)} fc={fc} "
                          f"distinct={sorted(set(movers))}")

        print(f"n={n} ms={ms} prod={prod} sub={is_sub} bin={binary_count}: "
              f"{cycle_count} cycles, {hno_safe_count} hno_safe")

    # Now test WITHOUT sub-threshold: ms=(2,2,2,5,5), product=200 > 108
    ms = [2,2,2,5,5]
    prod = 200
    hno_safe_count = 0
    cycle_count = 0
    for trial in range(1000000):
        sys_f = {}
        for i in range(n):
            sys_f[i] = random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n])
        start = tuple(random.randint(0, ms[i]-1) for i in range(n))
        movers = find_good_cycle(sys_f, ms, n, start)
        if movers is None: continue
        cycle_count += 1
        if check_hno_safe(movers, n):
            hno_safe_count += 1
            if hno_safe_count <= 5:
                fc = [0]*n
                for m in movers: fc[m] += 1
                print(f"  hno_safe! ms={ms} L={len(movers)} fc={fc} "
                      f"distinct={sorted(set(movers))}")
    print(f"n={n} ms={ms} prod={prod} sub=False bin=3: "
          f"{cycle_count} cycles, {hno_safe_count} hno_safe")

test_small()
