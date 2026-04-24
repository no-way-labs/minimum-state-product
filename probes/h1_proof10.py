"""
EXHAUSTIVE search for n=3 counterexamples.
At n=3 with small state sizes, we can be exhaustive over ALL transition tables.
"""
from itertools import product as iprod

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

def check_h1_minimal(ms, tables):
    """Check H-1 uniqueness for a system with minimal cycle (fc=m_p)."""
    n = len(ms)
    cycle, movers = get_good_cycle(ms, tables)
    if not cycle or len(cycle) <= 2: return None
    CL = len(cycle)
    fc = [0]*n
    for m in movers: fc[m] += 1
    if not all(fc[p] == ms[p] for p in range(n)): return None  # not minimal
    for j in range(CL):
        for k in range(j+1, CL):
            diff = sum(1 for i in range(n) if cycle[j][i] != cycle[k][i])
            if diff == 1 and min(k-j, CL-(k-j)) != 1:
                return False
    return True

# For n=3, ms=[2,2,3]: each proc has 2*2*3=12 or 2*3*2=12 or 3*2*2=12 context triples.
# Total tables = 2^12 * 2^12 * 3^12 ≈ way too many.
# But: we only care about VALID systems. Let me use random sampling with large count.

import random
random.seed(0)

print("=== Large random search for n=3 minimal cycle violations ===")
for ms_test in [[2,2,3], [2,3,3], [2,3,5], [3,3,3], [2,2,2]]:
    n = len(ms_test)
    found = 0; viols = 0
    for trial in range(200000):
        tables = []
        for p in range(n):
            t = {}
            mL = ms_test[(p-1)%n]; mS = ms_test[p]; mR = ms_test[(p+1)%n]
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        t[(L,S,R)] = random.randrange(mS)
            tables.append(t)
        result = check_h1_minimal(ms_test, tables)
        if result is None: continue
        found += 1
        if result == False:
            viols += 1
            if viols <= 2:
                cycle, movers = get_good_cycle(ms_test, tables)
                print(f"  VIOLATION: ms={ms_test}, CL={len(cycle)}, movers={movers}")
    print(f"ms={ms_test}: {found} minimal systems, {viols} violations (tested 200k)")

# Also test n=4
print("\n=== n=4 ===")
for ms_test in [[2,2,2,3], [2,3,3,3], [2,2,3,3]]:
    n = len(ms_test)
    found = 0; viols = 0
    for trial in range(100000):
        tables = []
        for p in range(n):
            t = {}
            mL = ms_test[(p-1)%n]; mS = ms_test[p]; mR = ms_test[(p+1)%n]
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        t[(L,S,R)] = random.randrange(mS)
            tables.append(t)
        result = check_h1_minimal(ms_test, tables)
        if result is None: continue
        found += 1
        if result == False:
            viols += 1
    print(f"ms={ms_test}: {found} minimal systems, {viols} violations (tested 100k)")
