"""
Focused: verify gcd=1 => H-1 holds for minimal cycles. Small search.
"""
from itertools import product as iprod
from math import gcd
from functools import reduce
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

random.seed(42)

# Test coprime systems
for ms_test, trials in [
    ([2,3], 5000), ([2,5], 5000), ([3,5], 5000),
    ([2,3,3], 5000), ([2,2,3], 5000),
    ([4,6], 5000), ([2,4], 5000), ([3,6], 5000),
    ([6,10], 5000),
]:
    g = reduce(gcd, ms_test)
    n = len(ms_test)
    found = 0; violations = 0
    for _ in range(trials):
        tables = []
        for p in range(n):
            t = {}
            mL = ms_test[(p-1)%n]; mS = ms_test[p]; mR = ms_test[(p+1)%n]
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        t[(L,S,R)] = random.randrange(mS)
            tables.append(t)
        cycle, movers = get_good_cycle(ms_test, tables)
        if not cycle or len(cycle) <= 2: continue
        CL = len(cycle)
        fc = [0]*n
        for m in movers: fc[m] += 1
        if not all(fc[p] == ms_test[p] for p in range(n)): continue
        found += 1
        for j in range(CL):
            for k in range(j+1, CL):
                diff = sum(1 for i in range(n) if cycle[j][i] != cycle[k][i])
                if diff == 1 and min(k-j, CL-(k-j)) != 1:
                    violations += 1
                    break
            if violations: break
    print(f"ms={str(ms_test):15s} gcd={g}: {found:3d} minimal, {violations} violations")
