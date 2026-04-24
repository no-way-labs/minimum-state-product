"""
H-1 violations at n=2. Investigate ms=[2,3] counterexample.
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

random.seed(42)
ms = [2, 3]
n = 2
found_viols = 0
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

    # Check H-1
    has_viol = False
    for j in range(CL):
        for k in range(j+1, CL):
            diff = [i for i in range(n) if cycle[j][i] != cycle[k][i]]
            if len(diff) == 1:
                cdist = min(k-j, CL-(k-j))
                if cdist != 1:
                    has_viol = True
                    if found_viols < 3:
                        p = diff[0]
                        print(f"VIOLATION #{found_viols+1}: CL={CL}, j={j}, k={k}, p={p}, cdist={cdist}")
                        print(f"  movers={movers}, fc={fc}")
                        for i in range(CL):
                            marker = " <--" if i in [j,k] else ""
                            print(f"  [{i}] {cycle[i]} mover={movers[i]}{marker}")
                        # Print tables
                        for pp in range(n):
                            print(f"  Proc {pp} table (m={ms[pp]}):")
                            for ctx in sorted(tables[pp].keys()):
                                if tables[pp][ctx] != ctx[1]:
                                    print(f"    {ctx} -> {tables[pp][ctx]}")
                    break
        if has_viol: break
    if has_viol:
        found_viols += 1

print(f"\nTotal violations at ms=[2,3]: {found_viols}")

# KEY INSIGHT: at n=2, the ring has only 2 procs. L = R for each proc!
# proc 0 sees (c[1], c[0], c[1]) = context depends on both.
# proc 1 sees (c[0], c[1], c[0]).
# This is a DEGENERATE case (n=2 ring). In a ring with n=2:
# config = (c0, c1). Proc 0's context is (c1, c0, c1), proc 1's is (c0, c1, c0).
#
# The self-stabilization literature typically considers n >= 3.
# Let me check: does the counterexample survive at n >= 3?

print("\n=== n >= 3 with coprime ms, exhaustive ===")
for ms_test in [[2,3,3], [2,2,3], [2,3,5], [3,3,5], [2,2,2,3], [2,3,3,3]]:
    n = len(ms_test)
    random.seed(42)
    found = 0; violations = 0
    for trial in range(10000):
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
                    if violations <= 1:
                        print(f"  ms={ms_test} VIOLATION: CL={CL}, j={j}, k={k}")
                    break
            if violations: break
    print(f"ms={ms_test}: {found} minimal, {violations} violations")
