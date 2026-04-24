#!/usr/bin/env python3
"""Test: can hno_safe hold at n=9 for ANY good cycle?
Also test: can it hold with NO binary procs? With 1-2 binary?"""
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
                nc[privs[0]] = sys_f[privs[0]][(c[(privs[0]-1)%n], c[privs[0]], c[(privs[0]+1)%n])]
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

def test_config(n, ms, trials=200000, label=""):
    random.seed(12345)
    hno_safe_count = 0
    cycle_count = 0

    for trial in range(trials):
        sys_f = {}
        for i in range(n):
            sys_f[i] = random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n])

        for _ in range(2):
            start = tuple(random.randint(0, ms[i]-1) for i in range(n))
            movers = find_good_cycle(sys_f, ms, n, start)
            if movers is None:
                continue
            cycle_count += 1

            if check_hno_safe(movers, n):
                hno_safe_count += 1
                if hno_safe_count <= 3:
                    fc = [0]*n
                    for m in movers:
                        fc[m] += 1
                    L = len(movers)
                    distinct = sorted(set(movers))
                    print(f"  hno_safe! L={L} distinct={distinct} fc={fc}")

    prod = 1
    for m in ms:
        prod *= m
    binary_count = sum(1 for m in ms if m == 2)
    print(f"{label}n={n} ms={ms} prod={prod} bin={binary_count}: "
          f"{cycle_count} cycles, {hno_safe_count} hno_safe")
    return hno_safe_count

print("=== Testing hno_safe at n=9 ===")
print()

# No binary
test_config(9, [3]*9, label="0 binary: ")
print()

# 1 binary
test_config(9, [2]+[3]*8, label="1 binary: ")
print()

# 2 binary
test_config(9, [2,2]+[3]*7, label="2 binary consec: ")
test_config(9, [2,3,3,3,2]+[3]*4, label="2 binary far: ")
print()

# 3 binary
test_config(9, [2,2,2]+[3]*6, label="3 binary consec: ")
test_config(9, [2,3,3,2,3,3,2,3,3], label="3 binary spaced: ")
test_config(9, [2,3,2,3,2,3,3,3,3], label="3 binary gap1: ")
print()

# Also test n=5 for comparison
print("\n=== Testing hno_safe at n=5 ===")
test_config(5, [3]*5, label="0 binary: ")
test_config(5, [2,3,3,3,3], label="1 binary: ")
test_config(5, [2,2,3,3,3], label="2 binary: ")
test_config(5, [2,2,2,3,3], label="3 binary: ")
