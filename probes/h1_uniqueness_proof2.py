"""
H-1 Uniqueness: fix distance computation (cyclic distance).
Confirm that ALL H-1 pairs have cyclic distance 1.
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

def check_h1_cyclic(ms, tables, label=""):
    cycle, movers = get_good_cycle(ms, tables)
    if not cycle:
        print(f"{label}: no good cycle")
        return True
    CL = len(cycle); n = len(ms)

    violations = 0
    for j in range(CL):
        for k in range(j+1, CL):
            diff = [i for i in range(n) if cycle[j][i] != cycle[k][i]]
            if len(diff) == 1:
                cyclic_dist = min(k-j, CL-(k-j))
                if cyclic_dist != 1:
                    violations += 1
                    if violations <= 3:
                        p = diff[0]
                        print(f"  VIOLATION: j={j},k={k},p={p},cyclic_dist={cyclic_dist}")
                        print(f"    g_j={cycle[j]} mover={movers[j]}")
                        print(f"    g_k={cycle[k]} mover={movers[k]}")

    if violations == 0:
        print(f"{label}: CL={CL}, H-1 Uniqueness HOLDS")
    else:
        print(f"{label}: CL={CL}, {violations} VIOLATIONS")
    return violations == 0

# Comprehensive test
all_ok = True

# Sol1
for K in range(3, 12):
    for n in [3, 4, 5]:
        if K < n: continue
        ms = [K]*n
        tables = []
        for p in range(n):
            t = {}
            for L in range(K):
                for S in range(K):
                    for R in range(K):
                        if p == 0:
                            t[(L,S,R)] = (S+1)%K if S==L else S
                        else:
                            t[(L,S,R)] = L if S!=L else S
            tables.append(t)
        ok = check_h1_cyclic(ms, tables, f"Sol1 K={K} n={n}")
        all_ok = all_ok and ok

# Sol3v1
for n in range(3, 12):
    ms = [2] + [3]*(n-1)
    tables = []
    for p in range(n):
        t = {}
        for L in range(ms[(p-1)%n]):
            for S in range(ms[p]):
                for R in range(ms[(p+1)%n]):
                    if p == 0:
                        t[(L,S,R)] = (S+1)%ms[p] if S==L else S
                    else:
                        t[(L,S,R)] = L if S!=L else S
        tables.append(t)
    ok = check_h1_cyclic(ms, tables, f"Sol3v1 n={n}")
    all_ok = all_ok and ok

# Random valid systems - exhaustive search for small sizes
print("\n=== Exhaustive small system search ===")
import random
random.seed(42)

def exhaustive_search(ms, max_systems=10000):
    """Try random transition tables."""
    n = len(ms)
    found = 0
    violations = 0
    for _ in range(max_systems):
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
        if cycle and len(cycle) > 2:
            found += 1
            CL = len(cycle)
            for j in range(CL):
                for k in range(j+1, CL):
                    diff = sum(1 for i in range(n) if cycle[j][i] != cycle[k][i])
                    if diff == 1:
                        cdist = min(k-j, CL-(k-j))
                        if cdist != 1:
                            violations += 1
    return found, violations

for ms in [[2,3,3], [3,3,3], [2,2,3], [2,3,4], [2,2,2,3], [3,3,3,3], [2,3,3,3]]:
    found, viols = exhaustive_search(ms, 20000)
    print(f"  ms={ms}: {found} valid systems, {viols} violations")
    if viols > 0:
        all_ok = False

print(f"\nOverall: {'ALL PASS' if all_ok else 'FAILURES FOUND'}")
