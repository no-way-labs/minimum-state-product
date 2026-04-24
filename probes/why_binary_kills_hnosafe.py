#!/usr/bin/env python3
"""WHY does having binary procs prevent hno_safe?
Test with EXHAUSTIVE cycle enumeration at small n."""
import random
from itertools import product as iterproduct

def all_transitions(m_left, m_self, m_right):
    """Generate ALL possible transition functions for a proc."""
    contexts = [(L, S, R) for L in range(m_left) for S in range(m_self) for R in range(m_right)]
    # Each context maps to one of m_self values
    for values in iterproduct(range(m_self), repeat=len(contexts)):
        yield dict(zip(contexts, values))

def find_all_good_cycles(sys_f, ms, n, max_steps=500):
    """Find all good cycles by exhaustive start config search."""
    cycles = set()
    for start in iterproduct(*[range(ms[i]) for i in range(n)]):
        config = start
        visited = {}
        for step in range(max_steps):
            if config in visited:
                start_idx = visited[config]
                movers = []
                c = config
                valid = True
                for _ in range(step - start_idx):
                    privs = [i for i in range(n) if sys_f[i][(c[(i-1)%n], c[i], c[(i+1)%n])] != c[i]]
                    if len(privs) != 1:
                        valid = False
                        break
                    movers.append(privs[0])
                    nc = list(c)
                    p = privs[0]
                    nc[p] = sys_f[p][(c[(p-1)%n], c[p], c[(p+1)%n])]
                    c = tuple(nc)
                if valid and movers:
                    cycles.add(tuple(movers))
                break
            visited[config] = step
            privs = [i for i in range(n) if sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])] != config[i]]
            if len(privs) != 1:
                break
            p = privs[0]
            nc = list(config)
            nc[p] = sys_f[p][(config[(p-1)%n], config[p], config[(p+1)%n])]
            config = tuple(nc)
    return cycles

def check_hno_safe(movers, n):
    for q in range(n):
        visited = any(m == q or m == (q-1)%n or m == (q+1)%n for m in movers)
        if not visited:
            return False
    return True

# Small test: n=4 (smallest ring with n_ge_4)
n = 4

# Test n=4, ms=[2,3,3,3] (1 binary)
ms = [2,3,3,3]
prod = 1
for m in ms: prod *= m

print(f"n={n} ms={ms} prod={prod}")
print("Exhaustive random transition search...")

random.seed(42)
total_cycles = 0
total_hnosafe = 0

for trial in range(100000):
    sys_f = {}
    for i in range(n):
        sys_f[i] = {}
        for L in range(ms[(i-1)%n]):
            for S in range(ms[i]):
                for R in range(ms[(i+1)%n]):
                    sys_f[i][(L,S,R)] = random.randint(0, ms[i]-1)

    cycles = find_all_good_cycles(sys_f, ms, n)
    for movers in cycles:
        total_cycles += 1
        if check_hno_safe(movers, n):
            total_hnosafe += 1
            if total_hnosafe <= 5:
                fc = [0]*n
                for m in movers: fc[m] += 1
                print(f"  hno_safe! L={len(movers)} fc={fc} movers={list(movers)}")

print(f"Total cycles: {total_cycles}, hno_safe: {total_hnosafe}")

# Compare: n=4, ms=[3,3,3,3] (0 binary)
print()
ms2 = [3,3,3,3]
total_cycles2 = 0
total_hnosafe2 = 0

for trial in range(100000):
    sys_f = {}
    for i in range(n):
        sys_f[i] = {}
        for L in range(ms2[(i-1)%n]):
            for S in range(ms2[i]):
                for R in range(ms2[(i+1)%n]):
                    sys_f[i][(L,S,R)] = random.randint(0, ms2[i]-1)

    cycles = find_all_good_cycles(sys_f, ms2, n)
    for movers in cycles:
        total_cycles2 += 1
        if check_hno_safe(movers, n):
            total_hnosafe2 += 1
            if total_hnosafe2 <= 5:
                fc = [0]*n
                for m in movers: fc[m] += 1
                print(f"  hno_safe! ms=[3,3,3,3] L={len(movers)} fc={fc}")

print(f"ms=[3,3,3,3]: Total cycles: {total_cycles2}, hno_safe: {total_hnosafe2}")
