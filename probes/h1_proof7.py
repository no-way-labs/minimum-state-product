"""
H-1 Uniqueness: the correct theorem.

FINDING: H-1 Uniqueness holds when gcd(m_0, ..., m_{n-1}) = 1.
It can fail when gcd > 1.

For the LB proof: systems with binary (m=2) and ternary (m=3) procs
have gcd(2,3) = 1. So the theorem holds in the relevant setting.

Let me verify the ms=[4,6] counterexample and confirm the gcd condition.
"""
from itertools import product as iprod
import random

def get_good_cycle(ms, tables):
    n = len(ms)
    def fire(config, p):
        L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
        new = list(config); new[p] = tables[p][(L,S,R)]
        return tuple(new)
    good = {}
    for config in iprod(*[range(m) for m in ms]):
        privs = []
        for p in range(n):
            L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
            if tables[p][(L,S,R)] != S:
                privs.append(p)
        if len(privs) == 1:
            good[config] = privs[0]
    if not good: return None, None
    start = next(iter(good))
    cycle = [start]; movers = [good[start]]; cur = start
    for _ in range(100000):
        nxt = fire(cur, good[cur])
        if nxt == start: break
        if nxt not in good: return None, None
        cycle.append(nxt); movers.append(good[nxt]); cur = nxt
    else: return None, None
    return cycle, movers

def check_h1(ms, tables):
    cycle, movers = get_good_cycle(ms, tables)
    if not cycle or len(cycle) <= 2: return None
    CL = len(cycle); n = len(ms)
    for j in range(CL):
        for k in range(j+1, CL):
            diff = sum(1 for i in range(n) if cycle[j][i] != cycle[k][i])
            if diff == 1 and min(k-j, CL-(k-j)) != 1:
                return False
    return True

# Detailed analysis of ms=[4,6] counterexample
print("=== ms=[4,6] counterexample detail ===")
random.seed(42)
ms = [4, 6]
n = 2
for trial in range(50000):
    tables = []
    for p in range(n):
        t = {}
        mL = ms[(p-1)%n]; mS = ms[p]; mR = ms[(p+1)%n]
        for L in range(mL):
            for S in range(mS):
                for R in range(mR):
                    t[(L,S,R)] = random.randrange(mS)
        tables.append(t)
    cycle, movers = get_good_cycle(ms, tables)
    if not cycle or len(cycle) <= 2: continue
    CL = len(cycle)
    fc = [0]*n
    for m in movers: fc[m] += 1
    if not all(fc[p] == ms[p] for p in range(n)): continue

    ok = check_h1(ms, tables)
    if ok == False:
        print(f"CL={CL}, movers={movers}")
        for i in range(CL):
            print(f"  [{i}] {cycle[i]} mover={movers[i]}")

        # Check: mover sequence period
        for d in range(1, CL):
            if CL % d == 0:
                periodic = all(movers[i] == movers[i%d] for i in range(CL))
                if periodic:
                    print(f"  Mover period divides {d}")

        # Check values at each proc
        for p in range(n):
            vals = [cycle[i][p] for i in range(CL)]
            print(f"  Proc {p} values: {vals}")
            for d in range(1, CL):
                if all(vals[i] == vals[(i+d)%CL] for i in range(CL)):
                    print(f"    Period divides {d}")
                    break

        break

# Now: comprehensive gcd test
print("\n=== GCD test: systems with coprime state sizes ===")
from math import gcd
from functools import reduce

test_cases = [
    # (ms, expected: should H-1 hold?)
    ([2,3], True),    # gcd=1
    ([2,5], True),    # gcd=1
    ([3,5], True),    # gcd=1
    ([2,3,5], True),  # gcd=1
    ([4,6], False),   # gcd=2
    ([6,9], False),   # gcd=3
    ([2,4], False),   # gcd=2
    ([3,6], False),   # gcd=3
]

for ms, expected in test_cases:
    g = reduce(gcd, ms)
    n = len(ms)
    random.seed(42)
    found = 0
    violations = 0
    for trial in range(30000):
        tables = []
        for p in range(n):
            t = {}
            mL = ms[(p-1)%n]; mS = ms[p]; mR = ms[(p+1)%n]
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        t[(L,S,R)] = random.randrange(mS)
            tables.append(t)
        cycle, movers = get_good_cycle(ms, tables)
        if not cycle or len(cycle) <= 2: continue
        CL = len(cycle)
        fc = [0]*n
        for m in movers: fc[m] += 1
        if not all(fc[p] == ms[p] for p in range(n)): continue
        found += 1
        ok = check_h1(ms, tables)
        if ok == False:
            violations += 1

    status = "PASS" if violations == 0 else "FAIL"
    match = "OK" if (violations == 0) == expected else "UNEXPECTED"
    print(f"ms={ms}, gcd={g}: {found} systems, {violations} violations [{status}] {match}")

# The key: for the LB proof, ms has binary (2) and ternary (3) procs.
# gcd(2,3) = 1. So H-1 Uniqueness holds.
print("\n=== Specifically: binary+ternary systems (gcd=1) ===")
for ms in [[2,3,3], [2,2,3], [2,3,3,3], [2,2,3,3], [2,2,2,3,3], [2,3,3,3,3]]:
    g = reduce(gcd, ms)
    n = len(ms)
    random.seed(42)
    found = 0
    violations = 0
    for trial in range(20000):
        tables = []
        for p in range(n):
            t = {}
            mL = ms[(p-1)%n]; mS = ms[p]; mR = ms[(p+1)%n]
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        t[(L,S,R)] = random.randrange(mS)
            tables.append(t)
        cycle, movers = get_good_cycle(ms, tables)
        if not cycle or len(cycle) <= 2: continue
        CL = len(cycle)
        fc = [0]*n
        for m in movers: fc[m] += 1
        if not all(fc[p] == ms[p] for p in range(n)): continue
        found += 1
        ok = check_h1(ms, tables)
        if ok == False:
            violations += 1

    print(f"ms={ms}, gcd={g}: {found} minimal systems, {violations} violations")
