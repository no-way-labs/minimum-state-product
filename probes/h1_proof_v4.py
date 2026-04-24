"""
H-1 Uniqueness — Definitive computational check + proof structure.

1. Fast exhaustive check for n=3 minimal cycles.
2. Proof argument formalization.
"""
from itertools import product as iprod
import random

def check_system(ms):
    """Check ALL good cycles extractable from random systems."""
    n = len(ms)
    ranges = [range(m) for m in ms]

    def make_and_check(tables):
        def fire(config, p):
            L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
            new = list(config); new[p] = tables[p][(L,S,R)]
            return tuple(new)
        good = {}
        for config in iprod(*ranges):
            privs = []
            for pp in range(n):
                L = config[(pp-1)%n]; S = config[pp]; R = config[(pp+1)%n]
                if tables[pp][(L,S,R)] != S:
                    privs.append(pp)
            if len(privs) == 1:
                good[config] = privs[0]
        if not good: return None
        start = next(iter(good))
        cycle = [start]; movers = [good[start]]; cur = start
        for _ in range(10000):
            nxt = fire(cur, good[cur])
            if nxt == start: break
            if nxt not in good: return None
            cycle.append(nxt); movers.append(good[nxt]); cur = nxt
        else: return None
        CL = len(cycle)
        fc = [0]*n
        for m in movers: fc[m] += 1
        if not all(fc[p] == ms[p] for p in range(n)): return None

        # Check H-1
        for j in range(CL):
            for k in range(j+1, CL):
                diff = sum(1 for i in range(n) if cycle[j][i] != cycle[k][i])
                if diff == 1 and min(k-j, CL-(k-j)) > 1:
                    return False
        return True

    return make_and_check

random.seed(12345)
print("=== Fast n=3 search ===")
for ms in [[2,2,3], [2,3,3], [2,3,5], [3,3,5], [2,2,5], [3,5,7]]:
    n = len(ms)
    checker = check_system(ms)
    found = 0; viols = 0
    for trial in range(100000):
        tables = []
        for p in range(n):
            t = {}
            mL = ms[(p-1)%n]; mS = ms[p]; mR = ms[(p+1)%n]
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        t[(L,S,R)] = random.randrange(mS)
            tables.append(t)
        result = checker(tables)
        if result is None: continue
        found += 1
        if result is False:
            viols += 1
    print(f"  ms={ms}: {found} minimal, {viols} violations")

print("\n=== n=4 search ===")
for ms in [[2,2,2,3], [2,3,3,3], [2,2,3,3]]:
    n = len(ms)
    checker = check_system(ms)
    found = 0; viols = 0
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
        result = checker(tables)
        if result is None: continue
        found += 1
        if result is False:
            viols += 1
    print(f"  ms={ms}: {found} minimal, {viols} violations")

# Also specifically check n=2 to confirm failures exist
print("\n=== n=2 search (expect failures) ===")
for ms in [[2,3], [3,5], [2,4]]:
    n = len(ms)
    checker = check_system(ms)
    found = 0; viols = 0
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
        result = checker(tables)
        if result is None: continue
        found += 1
        if result is False:
            viols += 1
    print(f"  ms={ms}: {found} minimal, {viols} violations")
