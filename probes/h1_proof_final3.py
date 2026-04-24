"""
H-1 Uniqueness: check that it holds when ALL procs fire (fc >= 1 for all p).
Also check: does it hold when gcd(fc) = 1?
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
        for pp in range(n):
            L = config[(pp-1)%n]; S = config[pp]; R = config[(pp+1)%n]
            if tables[pp][(L,S,R)] != S:
                privs.append(pp)
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

from math import gcd
from functools import reduce

random.seed(42)

print("=== n >= 3, fc >= 1 check ===")
for ms_test in [[2,3,3], [2,2,3], [2,3,4], [3,3,3], [2,2,2,3], [2,3,3,3]]:
    n = len(ms_test)
    found_all_fire = 0; viols_all_fire = 0
    found_gcd1 = 0; viols_gcd1 = 0
    for trial in range(50000):
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
        fc = [movers.count(p) for p in range(n)]

        all_fire = all(f >= 1 for f in fc)
        g = reduce(gcd, fc)

        has_viol = False
        for j in range(CL):
            for k in range(j+1, CL):
                diff = sum(1 for i in range(n) if cycle[j][i] != cycle[k][i])
                if diff == 1 and min(k-j, CL-(k-j)) > 1:
                    has_viol = True
                    break
            if has_viol: break

        if all_fire:
            found_all_fire += 1
            if has_viol: viols_all_fire += 1
        if g == 1:
            found_gcd1 += 1
            if has_viol: viols_gcd1 += 1

    print(f"  ms={ms_test}: all_fire: {found_all_fire} systems, {viols_all_fire} violations; "
          f"gcd(fc)=1: {found_gcd1} systems, {viols_gcd1} violations")

# Also: check violations more carefully — what's the gcd of fc?
print("\n=== Violation fc analysis ===")
random.seed(42)
for ms_test in [[2,3,3], [2,2,3], [3,3,3], [2,2,2,3]]:
    n = len(ms_test)
    for trial in range(50000):
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
        fc = [movers.count(p) for p in range(n)]

        has_viol = False
        for j in range(CL):
            for k in range(j+1, CL):
                diff = sum(1 for i in range(n) if cycle[j][i] != cycle[k][i])
                if diff == 1 and min(k-j, CL-(k-j)) > 1:
                    has_viol = True
                    break
            if has_viol: break

        if has_viol:
            g = reduce(gcd, fc)
            zero_count = sum(1 for f in fc if f == 0)
            print(f"  ms={ms_test}, CL={CL}, fc={fc}, gcd={g}, zeros={zero_count}")
